#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""sipload - SIP / RTP call load and fault tester for SBCs such as the Yeti Switch.

Two roles:
  carrier   answers calls like an upstream carrier (configurable replies, audio, faults)
  customer  places calls like a customer (digest auth, ramp, audio, injected faults)
Each role has a web dashboard, live audio listening, reports and a Prometheus /metrics page.
Python 3.8+, standard library only.  UDP signalling, G.711 (PCMU / PCMA) media.
"""
import argparse
import array
import base64
import zlib
import collections
import csv
import hashlib
import io
import json
import math
import operator
import os
import queue
import random
import re
import secrets
import selectors
import socket
import struct
import sys
import threading
import time
import wave
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

VERSION = "1.22"
UA = "sipload/" + VERSION


def log(*a):
    print(time.strftime("%H:%M:%S"), *a, flush=True)


# ------------------------------------------------------------------ G.711
def _ulaw_dec(u):
    u = ~u & 0xFF
    s = (((u & 0x0F) << 3) + 0x84) << ((u >> 4) & 7)
    s -= 0x84
    return -s if u & 0x80 else s


def _ulaw_enc(pcm):
    sign = 0x80 if pcm < 0 else 0
    if pcm < 0:
        pcm = -pcm
    pcm = min(pcm, 32635) + 0x84
    exp, mask = 7, 0x4000
    while exp > 0 and not (pcm & mask):
        exp -= 1
        mask >>= 1
    return ~(sign | (exp << 4) | ((pcm >> (exp + 3)) & 0x0F)) & 0xFF


def _alaw_dec(a):
    a ^= 0x55
    t = (a & 0x0F) << 4
    seg = (a & 0x70) >> 4
    if seg == 0:
        t += 8
    elif seg == 1:
        t += 0x108
    else:
        t = (t + 0x108) << (seg - 1)
    return t if a & 0x80 else -t


_ALAW_SEG = (0x1F, 0x3F, 0x7F, 0xFF, 0x1FF, 0x3FF, 0x7FF, 0xFFF)


def _alaw_enc(pcm):
    pcm >>= 3
    if pcm >= 0:
        mask = 0xD5
    else:
        mask = 0x55
        pcm = -pcm - 1
    seg = 8
    for i, lim in enumerate(_ALAW_SEG):
        if pcm <= lim:
            seg = i
            break
    if seg >= 8:
        return 0x7F ^ mask
    aval = seg << 4
    aval |= (pcm >> 1) & 0x0F if seg < 2 else (pcm >> seg) & 0x0F
    return aval ^ mask


ULAW_DEC = array.array("h", [_ulaw_dec(i) for i in range(256)])
ALAW_DEC = array.array("h", [_alaw_dec(i) for i in range(256)])
# magnitude proxy (0..127) used to tell silence from audio without decoding every packet
MAG = {0: bytes((~b) & 0x7F for b in range(256)), 8: bytes((b ^ 0x55) & 0x7F for b in range(256))}
DEC = {0: ULAW_DEC, 8: ALAW_DEC}
SILENCE = {0: b"\xff" * 160, 8: b"\xd5" * 160}
# name: (payload type, SDP name, clock rate, payload bytes per 20 ms, RTP timestamp step, fmtp, E-model Ie)
# Only PCMU / PCMA carry real audio.  The others carry correctly sized dummy payload: they test negotiation, packet rate,
# loss, jitter and transcoding capacity, but cannot be listened to or tone-scored.
CODECS = {
    "PCMU": (0, "PCMU", 8000, 160, 160, "", 0), "PCMA": (8, "PCMA", 8000, 160, 160, "", 0),
    "G722": (9, "G722", 8000, 160, 160, "", 0), "GSM": (3, "GSM", 8000, 33, 160, "", 20),
    "G729": (18, "G729", 8000, 20, 160, "annexb=no", 11), "G726-32": (2, "G726-32", 8000, 80, 160, "", 7),
    "ILBC": (97, "iLBC", 8000, 38, 160, "mode=20", 11), "OPUS": (111, "opus", 48000, 60, 960, "minptime=20;useinbandfec=1", 0),
}
CODEC_PT = {k: v[0] for k, v in CODECS.items()}
PT_CODEC = {v[0]: k for k, v in CODECS.items()}
CODEC_BY_PT = {v[0]: v for v in CODECS.values()}


def udp_socket():
    """UDP socket; on Windows stop 'port unreachable' replies from raising errors on later receives."""
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    if hasattr(socket, "SIO_UDP_CONNRESET"):
        try:
            s.ioctl(socket.SIO_UDP_CONNRESET, False)
        except (OSError, ValueError):
            pass
    return s
REAL_PT = (0, 8)
DTMF_EVENTS = "0123456789*#ABCD"
_ENC_TABLES = {}


def enc_table(pt):
    t = _ENC_TABLES.get(pt)
    if t is None:
        f = _ulaw_enc if pt == 0 else _alaw_enc
        t = bytes(f(s) for s in range(-32768, 32768))
        _ENC_TABLES[pt] = t
    return t


# ------------------------------------------------------------------ tone test signal (DTMF + 1004 Hz)
DTMF_LOW = (697, 770, 852, 941)
DTMF_HIGH = (1209, 1336, 1477, 1633)
DTMF_KEYS = "123456789*0#"
DTMF_MAP = {"1": (697, 1209), "2": (697, 1336), "3": (697, 1477), "4": (770, 1209), "5": (770, 1336), "6": (770, 1477),
            "7": (852, 1209), "8": (852, 1336), "9": (852, 1477), "*": (941, 1209), "0": (941, 1336), "#": (941, 1477)}
DTMF_REV = {v: k for k, v in DTMF_MAP.items()}
TT_REF_HZ, TT_REF_AMP, TT_DTMF_AMP = 1004, 8000.0, 5000.0     # amplitudes in 16-bit counts (per tone)
TT_SECONDS = 7.8


def tonetest_pcm():
    """One 7.8 s cycle: 2 s of 1004 Hz, then the DTMF digits 1 2 3 4 5 6 7 8 9 * 0 # (250 ms tone + 150 ms gap), with silences."""
    out = array.array("h")

    def tone(freqs, amp, secs):
        n = int(secs * 8000)
        for i in range(n):
            env = min(1.0, i / 40.0, (n - 1 - i) / 40.0)              # 5 ms ramps, no clicks
            out.append(int(round(sum(math.sin(2 * math.pi * f * i / 8000.0) for f in freqs) * amp * env)))

    tone((TT_REF_HZ,), TT_REF_AMP, 2.0)
    out.extend([0] * 4000)
    for k in DTMF_KEYS:
        tone(DTMF_MAP[k], TT_DTMF_AMP, 0.25)
        out.extend([0] * 1200)
    out.extend([0] * 4000)
    return out


class Audio:
    """A WAV file converted to 20 ms G.711 frames (both codecs), looped when played."""

    def __init__(self, path=None):
        self.path = path
        if path == "__tonetest__":
            self.kind, self.name = "tonetest", "Tone test (DTMF + 1004 Hz)"
            pcm = tonetest_pcm()
        elif path:
            self.kind, self.name = "file", os.path.basename(path)
            pcm = self._load(path)
        else:
            self.kind, self.name = "melody", "built-in tone sequence"
            pcm = self._tones()
        self.seconds = len(pcm) / 8000.0
        pad = (-len(pcm)) % 160
        if pad:
            pcm = pcm + array.array("h", [0] * pad)
        self.frames = {}
        self.frame_sets = {}
        for pt in (0, 8):
            tb = enc_table(pt)
            raw = bytes(tb[s + 32768] for s in pcm)
            fr = [raw[i:i + 160] for i in range(0, len(raw), 160)]
            self.frames[pt] = fr
            self.frame_sets[pt] = set(fr)
        for name, v in CODECS.items():
            if v[0] in REAL_PT:
                continue
            rnd = random.Random(name)
            fr = [bytes(rnd.getrandbits(8) for _ in range(v[3])) for _ in range(50)]
            self.frames[v[0]] = fr
            self.frame_sets[v[0]] = set(fr)
        mags = [sum(f.translate(MAG[0])) / 160.0 for f in self.frames[0]]
        self.active_pct = 100.0 * sum(1 for m in mags if m >= 3) / max(1, len(mags))

    @staticmethod
    def _load(path):
        with wave.open(path, "rb") as w:
            ch, sw, rate, n = w.getnchannels(), w.getsampwidth(), w.getframerate(), w.getnframes()
            data = w.readframes(n)
        if sw != 2:
            raise ValueError("WAV must be 16-bit PCM")
        s = array.array("h")
        s.frombytes(data)
        if sys.byteorder == "big":
            s.byteswap()
        if ch > 1:
            s = array.array("h", [sum(s[i:i + ch]) // ch for i in range(0, len(s) - ch + 1, ch)])
        if rate != 8000:
            ratio = rate / 8000.0
            out = array.array("h")
            n_out = int(len(s) / ratio)
            for i in range(n_out):
                p = i * ratio
                j = int(p)
                f = p - j
                a = s[j]
                b = s[j + 1] if j + 1 < len(s) else a
                out.append(int(a + (b - a) * f))
            s = out
        if len(s) < 1600:
            raise ValueError("WAV is shorter than 0.2 s")
        return s

    @staticmethod
    def _tones():
        # 12 s of tone bursts with pauses, so silence/audio detection and listening both work
        out = array.array("h")
        notes = [440, 523, 659, 784, 659, 523, 440, 392, 494, 587, 698, 587]
        for f in notes:
            for i in range(4000):                     # 0.5 s tone
                env = min(1.0, i / 200.0, (4000 - i) / 200.0)
                out.append(int(9000 * env * math.sin(2 * math.pi * f * i / 8000.0)))
            out.extend([0] * 2000)                    # 0.25 s pause
        return out


def make_wav(path, text=None, tonetest=False):
    """Write a test WAV.  Tries ffmpeg+flite speech, else falls back to the tone sequence."""
    if tonetest:
        a = tonetest_pcm()
        with wave.open(path, "wb") as w:
            w.setnchannels(1)
            w.setsampwidth(2)
            w.setframerate(8000)
            w.writeframes(a.tobytes())
        return "tone test"
    if text:
        import subprocess
        try:
            subprocess.run(["ffmpeg", "-y", "-loglevel", "error", "-f", "lavfi", "-i",
                            "flite=text='%s':voice=slt" % text.replace("'", ""),
                            "-ar", "8000", "-ac", "1", "-sample_fmt", "s16", path], check=True, timeout=60)
            return "speech"
        except Exception:
            pass
    a = Audio._tones()
    with wave.open(path, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(8000)
        w.writeframes(a.tobytes())
    return "tones"


# ------------------------------------------------------------------ quality estimate
def estimate_mos(loss_pct, jitter_ms, delay_ms=40.0, ie0=0.0):
    """Simplified ITU-T G.107 E-model for G.711.  An estimate from loss and jitter only."""
    d = delay_ms + 2.0 * jitter_ms
    idd = 0.024 * d + (0.11 * (d - 177.3) if d > 177.3 else 0.0)
    ie = ie0 + (95.0 - ie0) * loss_pct / (loss_pct + 25.1)
    r = max(0.0, min(100.0, 93.2 - idd - ie))
    if r <= 0:
        return 1.0
    return round(max(1.0, min(4.5, 1 + 0.035 * r + r * (r - 60) * (100 - r) * 7e-6)), 2)


def pctl(vals, p):
    if not vals:
        return None
    v = sorted(vals)
    return v[min(len(v) - 1, int(round((p / 100.0) * (len(v) - 1))))]


def avg(vals):
    return (sum(vals) / len(vals)) if vals else None


def rnd(v, n=1):
    return None if v is None else round(v, n)


# ------------------------------------------------------------------ SIP messages
COMPACT = {"v": "via", "f": "from", "t": "to", "i": "call-id", "m": "contact", "l": "content-length", "c": "content-type"}
REASONS = {100: "Trying", 180: "Ringing", 183: "Session Progress", 200: "OK", 302: "Moved Temporarily",
           400: "Bad Request", 401: "Unauthorized", 403: "Forbidden", 404: "Not Found", 407: "Proxy Authentication Required",
           408: "Request Timeout", 480: "Temporarily Unavailable", 481: "Call/Transaction Does Not Exist",
           486: "Busy Here", 487: "Request Terminated", 488: "Not Acceptable Here", 500: "Server Internal Error",
           503: "Service Unavailable", 504: "Server Time-out", 603: "Decline", 604: "Does Not Exist Anywhere"}


class Msg:
    __slots__ = ("start", "headers", "body", "raw", "addr", "t")

    def __init__(self):
        self.start = ""
        self.headers = []
        self.body = ""
        self.raw = ""
        self.addr = None
        self.t = 0.0

    @property
    def is_request(self):
        return not self.start.startswith("SIP/2.0")

    @property
    def method(self):
        return self.start.split(" ", 1)[0] if self.is_request else self.cseq[1]

    @property
    def uri(self):
        p = self.start.split(" ")
        return p[1] if self.is_request and len(p) > 1 else ""

    @property
    def code(self):
        p = self.start.split(" ", 2)
        return int(p[1]) if not self.is_request and len(p) > 1 and p[1].isdigit() else 0

    def h(self, name, default=""):
        name = name.lower()
        for k, v in self.headers:
            if k == name:
                return v
        return default

    def hs(self, name):
        name = name.lower()
        return [v for k, v in self.headers if k == name]

    @property
    def call_id(self):
        return self.h("call-id")

    @property
    def cseq(self):
        p = self.h("cseq").split()
        return (int(p[0]) if p and p[0].isdigit() else 0, p[1].upper() if len(p) > 1 else "")

    def user(self, header="to"):
        m = re.search(r"sip:([^@>;:]+)@", self.h(header))
        return m.group(1) if m else ""

    def tag(self, header):
        m = re.search(r";\s*tag=([^;>\s]+)", self.h(header))
        return m.group(1) if m else ""


def parse_msg(data, addr=None):
    try:
        text = data.decode("utf-8", "replace")
    except Exception:
        return None
    head, sep, body = text.partition("\r\n\r\n")
    if not sep:
        head, sep, body = text.partition("\n\n")
    lines = head.replace("\r\n", "\n").split("\n")
    if not lines or not lines[0].strip():
        return None
    m = Msg()
    m.start = lines[0].strip()
    if not (m.start.startswith("SIP/2.0") or m.start.endswith("SIP/2.0")):
        return None
    last = None
    for ln in lines[1:]:
        if ln[:1] in (" ", "\t") and last is not None:
            m.headers[last] = (m.headers[last][0], m.headers[last][1] + " " + ln.strip())
            continue
        if ":" not in ln:
            continue
        k, v = ln.split(":", 1)
        k = k.strip().lower()
        k = COMPACT.get(k, k)
        m.headers.append((k, v.strip()))
        last = len(m.headers) - 1
    m.body = body
    m.raw = text
    m.addr = addr
    m.t = time.time()
    return m


def build_msg(start, headers, body=""):
    out = [start]
    for k, v in headers:
        out.append("%s: %s" % (k, v))
    out.append("Content-Length: %d" % len(body.encode()))
    return ("\r\n".join(out) + "\r\n\r\n" + body).encode()


def new_branch():
    return "z9hG4bK" + secrets.token_hex(6)


def new_tag():
    return secrets.token_hex(4)


# ------------------------------------------------------------------ digest authentication
def _md5(s):
    return hashlib.md5(s.encode()).hexdigest()


def parse_challenge(value):
    d = {}
    for m in re.finditer(r'(\w+)\s*=\s*(?:"([^"]*)"|([^,\s]+))', value.partition(" ")[2]):
        d[m.group(1).lower()] = m.group(2) if m.group(2) is not None else m.group(3)
    return d


def digest_header(ch, user, password, method, uri):
    """Authorization header value answering challenge dict `ch`."""
    algo = ch.get("algorithm", "MD5").upper()
    hf = (lambda s: hashlib.sha256(s.encode()).hexdigest()) if "SHA-256" in algo else _md5
    realm, nonce = ch.get("realm", ""), ch.get("nonce", "")
    ha1 = hf("%s:%s:%s" % (user, realm, password))
    ha2 = hf("%s:%s" % (method, uri))
    qop = ch.get("qop", "")
    parts = ['username="%s"' % user, 'realm="%s"' % realm, 'nonce="%s"' % nonce, 'uri="%s"' % uri]
    if "auth" in qop.split(","):
        cn, nc = secrets.token_hex(4), "00000001"
        resp = hf("%s:%s:%s:%s:auth:%s" % (ha1, nonce, nc, cn, ha2))
        parts += ["qop=auth", "nc=" + nc, 'cnonce="%s"' % cn]
    else:
        resp = hf("%s:%s:%s" % (ha1, nonce, ha2))
    parts += ['response="%s"' % resp, "algorithm=" + algo]
    if ch.get("opaque"):
        parts.append('opaque="%s"' % ch["opaque"])
    return "Digest " + ", ".join(parts)


def digest_check(value, method, password, realm, nonces):
    """Server side: True if the Authorization header is valid for a nonce we issued."""
    d = parse_challenge("Digest " + value.partition(" ")[2])
    if d.get("nonce") not in nonces or d.get("realm") != realm:
        return False
    ha1 = _md5("%s:%s:%s" % (d.get("username", ""), realm, password))
    ha2 = _md5("%s:%s" % (method, d.get("uri", "")))
    if d.get("qop") == "auth":
        exp = _md5("%s:%s:%s:%s:auth:%s" % (ha1, d["nonce"], d.get("nc", ""), d.get("cnonce", ""), ha2))
    else:
        exp = _md5("%s:%s:%s" % (ha1, d["nonce"], ha2))
    return exp == d.get("response")


# ------------------------------------------------------------------ SDP
def sdp_codecs(body):
    """{payload type: codec name in capitals} from the rtpmap lines (static types fall back to our table)."""
    names = {}
    in_audio = False
    for ln in body.replace("\r\n", "\n").split("\n"):
        ln = ln.strip()
        if ln.startswith("m="):
            in_audio = ln.startswith("m=audio")
        elif in_audio and ln.startswith("a=rtpmap:"):
            m = re.match(r"a=rtpmap:(\d+)\s+([^/\s]+)", ln)
            if m:
                names[int(m.group(1))] = m.group(2).upper()
    for pt in re.findall(r"\d+", (re.search(r"m=audio \d+ \S+ ([\d ]+)", body) or [None, ""])[1]):
        names.setdefault(int(pt), PT_CODEC.get(int(pt), ""))
    return names


def build_sdp(ip, port, pts, ptime=20, dtmf=True, direction="sendrecv", names=None):
    sid = int(time.time())
    fmts = list(pts) + ([101] if dtmf else [])
    lines = ["v=0", "o=sipload %d %d IN IP4 %s" % (sid, sid, ip), "s=sipload", "c=IN IP4 %s" % ip, "t=0 0",
             "m=audio %d RTP/AVP %s" % (port, " ".join(str(p) for p in fmts))]
    for p in pts:
        cn = (names or {}).get(p) or PT_CODEC.get(p, "PCMU")
        v = CODECS.get(cn) or CODECS["PCMU"]
        lines.append("a=rtpmap:%d %s/%d%s" % (p, v[1], v[2], "/2" if cn == "OPUS" else ""))
        if v[5]:
            lines.append("a=fmtp:%d %s" % (p, v[5]))
    if dtmf:
        lines += ["a=rtpmap:101 telephone-event/8000", "a=fmtp:101 0-16"]
    lines += ["a=ptime:%d" % ptime, "a=" + direction]
    return "\r\n".join(lines) + "\r\n"


def parse_sdp(body):
    """-> (ip, port, [payload types], direction) or None when there is no audio line."""
    ip, port, pts, direction = None, 0, [], "sendrecv"
    media_ip = None
    in_audio = False
    for ln in body.replace("\r\n", "\n").split("\n"):
        ln = ln.strip()
        if ln.startswith("c=IN IP4 "):
            v = ln[9:].split("/")[0].strip()
            if in_audio:
                media_ip = v
            elif ip is None:
                ip = v
        elif ln.startswith("m="):
            p = ln[2:].split()
            if p and p[0] == "audio" and not in_audio and not port:
                in_audio = True
                port = int(p[1]) if p[1].isdigit() else 0
                pts = [int(x) for x in p[3:] if x.isdigit()]
            else:
                in_audio = False
        elif in_audio and ln in ("a=sendonly", "a=recvonly", "a=inactive", "a=sendrecv"):
            direction = ln[2:]
    ip = media_ip or ip
    if not ip or not port:
        return None
    return ip, port, pts, direction


# ------------------------------------------------------------------ RTP
class RtpStream:
    """One call's media socket: sends looped audio, measures what arrives."""

    def __init__(self, sock, port, audio, rec_seconds):
        self.sock, self.port, self.audio = sock, port, audio
        self.remote = None
        self.sending = False
        self.tx_pt = 0
        self.drop_pct = 0.0
        self.seq = random.randrange(65536)
        self.ts = random.randrange(2 ** 32)
        self.ssrc = random.randrange(1, 2 ** 32)
        self.idx = random.randrange(len(audio.frames[0]))
        self.first_tx = True
        self.tx_count = self.tx_bytes = 0
        self.rx_count = self.rx_bytes = 0
        self.rx_first_seq = None
        self.rx_max = 0
        self.rx_cycles = 0
        self.rx_ooo = self.rx_dup = 0
        self.rx_ssrc = None
        self.rx_pt = None
        self.jitter = 0.0
        self.max_jitter = 0.0
        self.last_transit = None
        self.rx_active = 0
        self.rx_exact = 0
        self.rx_first_t = self.rx_last_t = None
        self.rx_dtmf = []
        self.rec = bytearray()
        self.rec_cap = int(rec_seconds * 8000)
        self.rec_tx = bytearray()           # what we sent (G.711 only), for the both-sides recording
        self.tx_t0 = None
        self.rec_pt = None
        self.listeners = []
        self.lock = threading.Lock()
        self.closed = False
        self.echo = False
        self.echo_delay = 0.0
        self.echo_q = collections.deque(maxlen=600)
        self.dtmf_pt = 101                  # telephone-event payload type (from the SDP)
        self.dtmf_digits = []               # digits still to send (RFC 2833)
        self.dtmf_at = 0.0
        self.ev = None
        self.last_ev_ts = None
        self.fkey = None                    # which payload type's audio frames we send (when the wire type differs)
        self.script = collections.deque()    # scripted audio frames (Contact ID); silence is sent when empty
        self.script_mode = False
        self.lenient = False                # caller is a phone, not a tester: any packets count as audio (a quiet caller is not a fault)
        self.rx_tap = None                   # called with every received G.711 packet
        self.sent_t = [0.0] * 4096          # send time by sequence number, for round-trip measurement
        self.rtt_n, self.rtt_sum, self.rtt_min, self.rtt_max = 0, 0.0, None, 0.0

    # --- sending
    def send_one(self):
        if not self.sending or self.remote is None or self.closed:
            return
        pt = self.tx_pt
        if self.dtmf_digits and not self.echo and time.time() >= self.dtmf_at:
            return self._dtmf_tick()
        if self.echo:                                   # echo: reflect each packet unchanged (delayed only if asked to)
            now = time.time()
            while self.echo_q and self.echo_q[0][0] <= now:
                _, raw = self.echo_q.popleft()
                self._raw_send(raw)
            return
        if self.script_mode:
            payload = self.script.popleft() if self.script else SILENCE.get(pt, SILENCE[0])
        else:
            fr = self.audio.frames[self.fkey if self.fkey is not None else pt]
            payload = fr[self.idx % len(fr)]
            self.idx += 1
        self.sent_t[self.seq & 4095] = time.time()
        hdr = struct.pack("!BBHII", 0x80, (0x80 if self.first_tx else 0) | pt, self.seq, self.ts, self.ssrc)
        self.first_tx = False
        self.seq = (self.seq + 1) & 0xFFFF
        self.ts = (self.ts + CODEC_BY_PT.get(self.fkey if self.fkey is not None else pt, CODECS["PCMU"])[4]) & 0xFFFFFFFF
        if self.drop_pct and random.random() * 100.0 < self.drop_pct:
            self._rec_tx(SILENCE.get(pt, SILENCE[0]))
            return
        self._rec_tx(payload)
        try:
            self.sock.sendto(hdr + payload, self.remote)
            self.tx_count += 1
            self.tx_bytes += len(payload)
        except OSError:
            pass

    def _rec_tx(self, payload):
        if (self.fkey if self.fkey is not None else self.tx_pt) not in REAL_PT:
            return
        if self.tx_t0 is None:
            self.tx_t0 = time.time()
        if len(self.rec_tx) < self.rec_cap:
            self.rec_tx += payload

    def _dtmf_tick(self):
        """RFC 2833: one 20 ms tick of a telephone-event (5 tone packets = 100 ms, then 3 end packets), then 100 ms of audio."""
        if self.ev is None:
            d = self.dtmf_digits.pop(0)
            self.ev = {"code": DTMF_EVENTS.find(d) if d in DTMF_EVENTS else 0, "ts": self.ts, "n": 0, "end": 0}
        ev = self.ev
        if ev["n"] < 5:
            ev["n"] += 1
            end, dur = 0, 160 * ev["n"]
        else:
            ev["end"] += 1
            end, dur = 0x80, 160 * 5
        marker = 0x80 if (ev["n"] == 1 and ev["end"] == 0) else 0
        raw = struct.pack("!BBHII", 0x80, marker | self.dtmf_pt, self.seq, ev["ts"], self.ssrc) + struct.pack("!BBH", ev["code"], end | 10, dur)
        self.seq = (self.seq + 1) & 0xFFFF
        self.ts = (self.ts + 160) & 0xFFFFFFFF
        self._rec_tx(SILENCE.get(self.fkey if self.fkey is not None else self.tx_pt, SILENCE[0]))
        if ev["end"] >= 3:
            self.ev = None
            self.dtmf_at = time.time() + 0.1
        try:
            self.sock.sendto(raw, self.remote)
            self.tx_count += 1
        except OSError:
            pass

    def _raw_send(self, raw):
        if self.remote is None or self.closed:
            return
        try:
            self.sock.sendto(raw, self.remote)
            self.tx_count += 1
            self.tx_bytes += len(raw) - 12
        except OSError:
            pass

    # --- receiving
    def on_packet(self, data, arrival):
        if len(data) < 12 or (data[0] >> 6) != 2:
            return
        b0, b1, seq, ts, ssrc = struct.unpack("!BBHII", data[:12])
        off = 12 + 4 * (b0 & 0x0F)
        if b0 & 0x10 and len(data) >= off + 4:
            off += 4 + 4 * struct.unpack("!H", data[off + 2:off + 4])[0]
        end = len(data)
        if b0 & 0x20 and end > off:
            end -= data[-1]
        payload = data[off:end]
        pt = b1 & 0x7F
        if pt == self.dtmf_pt or pt == 101:
            if self.echo:                               # echo test: send the event back too
                if self.echo_delay <= 0:
                    self._raw_send(data)
                else:
                    self.echo_q.append((arrival + self.echo_delay, data))
            if self.rx_first_seq is not None and ssrc == self.rx_ssrc:      # event packets use sequence numbers too: keep loss maths right
                delta = (seq - self.rx_max) & 0xFFFF
                if 0 < delta < 3000:
                    if seq < self.rx_max:
                        self.rx_cycles += 65536
                    self.rx_max = seq
                    self.rx_count += 1
            if len(payload) >= 4 and ts != self.last_ev_ts:   # count each event once (it is repeated in several packets)
                self.last_ev_ts = ts
                self.rx_dtmf.append(DTMF_EVENTS[payload[0]] if payload[0] < 16 else "?")
            return
        if not payload or not (pt in PT_CODEC or pt == self.tx_pt):
            return
        if self.echo:                                   # carrier echo test: reflect the packet as it came
            if self.echo_delay <= 0:
                self._raw_send(data)
            else:
                self.echo_q.append((arrival + self.echo_delay, data))
        if self.rx_ssrc is None:
            self.rx_ssrc = ssrc
        elif ssrc != self.rx_ssrc:
            if ssrc != self.ssrc:
                return                              # ignore a second stream on the same port
            # our own packets are coming back (echo) after the far end played a greeting: measure from here on
            self.rx_count = self.rx_bytes = self.rx_active = self.rx_exact = self.rx_ooo = self.rx_dup = 0
            self.rx_first_seq, self.rx_max, self.rx_cycles = None, 0, 0
            self.jitter = self.max_jitter = 0.0
            self.last_transit = None
            self.rx_ssrc = ssrc
        if self.rx_first_seq is None:
            self.rx_first_seq = self.rx_max = seq
            self.rx_first_t = arrival
            self.rx_pt = pt
            gap = 0
        else:
            delta = (seq - self.rx_max) & 0xFFFF
            if delta == 0:
                self.rx_dup += 1
                return
            if delta < 3000:
                if seq < self.rx_max:
                    self.rx_cycles += 65536
                self.rx_max = seq
                gap = delta - 1
            elif delta > 65536 - 3000:
                self.rx_ooo += 1
                gap = -1
            else:
                self.rx_first_seq, self.rx_max, self.rx_cycles, gap = seq, seq, 0, 0
        self.rx_count += 1
        self.rx_bytes += len(payload)
        self.rx_last_t = arrival
        if gap >= 0:                                   # jitter, RFC 3550 section 6.4.1
            rate = (CODEC_BY_PT.get(pt) or CODECS["PCMU"])[2]
            transit = (int(arrival * rate) - ts) & 0xFFFFFFFF
            if self.last_transit is not None:
                d = (((transit - self.last_transit + 2 ** 31) % 2 ** 32) - 2 ** 31) * (8000.0 / rate)
                self.jitter += (abs(d) - self.jitter) / 16.0
                if self.jitter > self.max_jitter:
                    self.max_jitter = self.jitter
            self.last_transit = transit
        if ssrc == self.ssrc:                           # our own packet came back (echo): round-trip time
            t0 = self.sent_t[seq & 4095]
            if t0:
                rtt = (arrival - t0) * 1000.0
                if 0 < rtt < 5000:
                    self.rtt_n += 1
                    self.rtt_sum += rtt
                    self.rtt_min = rtt if self.rtt_min is None else min(self.rtt_min, rtt)
                    self.rtt_max = max(self.rtt_max, rtt)
        if pt not in REAL_PT:
            self.rx_active += 1
            if payload in self.audio.frame_sets.get(self.fkey if self.fkey is not None else pt, ()):
                self.rx_exact += 1
            return
        if self.rx_tap is not None:
            try:
                self.rx_tap(pt, payload, gap)
            except Exception:
                pass
        if sum(payload.translate(MAG[pt])) >= 3 * len(payload):
            self.rx_active += 1
        if payload in self.audio.frame_sets[pt]:
            self.rx_exact += 1
        if len(self.rec) < self.rec_cap:
            if 0 < gap < 60:
                self.rec += SILENCE[pt] * gap
            self.rec += payload
            self.rec_pt = pt
        if self.listeners:
            pcm = array.array("h", map(DEC[pt].__getitem__, payload)).tobytes()
            for q in list(self.listeners):
                try:
                    q.put_nowait(pcm)
                except queue.Full:
                    pass

    def stats(self):
        exp = (self.rx_cycles + self.rx_max - self.rx_first_seq + 1) if self.rx_first_seq is not None else 0
        lost = max(0, exp - self.rx_count)
        loss_pct = (100.0 * lost / exp) if exp else 0.0
        jit_ms = self.jitter / 8.0
        n = max(1, self.rx_count)
        active_pct = 100.0 * self.rx_active / n
        src = self.audio.active_pct
        got = self.rx_count > 0
        return {
            "tx_packets": self.tx_count, "rx_packets": self.rx_count, "rx_expected": exp, "rx_lost": lost,
            "loss_pct": round(loss_pct, 2), "jitter_ms": round(jit_ms, 2), "max_jitter_ms": round(self.max_jitter / 8.0, 2),
            "ooo": self.rx_ooo, "dup": self.rx_dup, "rx_codec": PT_CODEC.get(self.rx_pt, "") if got else "",
            "active_pct": round(active_pct, 1), "exact_pct": round(100.0 * self.rx_exact / n, 1) if got else 0.0,
            "audio_ok": bool(got and self.rx_active > 0 and active_pct >= 0.5 * src) or (self.script_mode and got) or (self.lenient and got),   # Contact ID: mostly silence by design
            "mos": estimate_mos(loss_pct, jit_ms, 40.0, (CODECS.get(PT_CODEC.get(self.rx_pt, "PCMU")) or CODECS["PCMU"])[6]) if got else None,
            "rtt_ms": round(self.rtt_sum / self.rtt_n, 1) if self.rtt_n else None, "rtt_min": round(self.rtt_min, 1) if self.rtt_n else None,
            "rtt_max": round(self.rtt_max, 1) if self.rtt_n else None,
            "dtmf": "".join(self.rx_dtmf),
        }


class RtpEngine:
    """Paces every call's outgoing packets (20 ms) and reads every call's incoming packets."""

    def __init__(self, bind_ip, pmin, pmax):
        self.bind_ip, self.pmin, self.pmax = bind_ip, pmin, pmax
        self.streams = []
        self.by_sock = {}
        self.lock = threading.Lock()
        self.sel = selectors.DefaultSelector()
        self.running = True
        self.late_ticks = 0
        self.ticks = 0
        self.max_lag_ms = 0.0
        self.total_tx = self.total_rx = 0
        threading.Thread(target=self._tx_loop, daemon=True, name="rtp-tx").start()
        threading.Thread(target=self._rx_loop, daemon=True, name="rtp-rx").start()

    def open(self, audio, rec_seconds):
        for _ in range(500):
            port = random.randrange(self.pmin, self.pmax, 2)
            s = udp_socket()
            try:
                s.bind((self.bind_ip, port))
            except OSError:
                s.close()
                continue
            s.setblocking(False)
            try:
                s.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 1 << 20)
            except OSError:
                pass
            st = RtpStream(s, port, audio, rec_seconds)
            with self.lock:
                self.streams.append(st)
                self.by_sock[s] = st
                self.sel.register(s, selectors.EVENT_READ)
            return st
        raise RuntimeError("no free RTP port in %d-%d" % (self.pmin, self.pmax))

    def close(self, st):
        with self.lock:
            st.closed = True
            st.sending = False
            if st in self.streams:
                self.streams.remove(st)
            if st.sock in self.by_sock:
                del self.by_sock[st.sock]
                try:
                    self.sel.unregister(st.sock)
                except Exception:
                    pass
        for q in list(st.listeners):
            try:
                q.put_nowait(None)
            except queue.Full:
                pass
        try:
            st.sock.close()
        except OSError:
            pass

    def _tx_loop(self):
        nxt = time.perf_counter()
        while self.running:
            now = time.perf_counter()
            if now < nxt:
                time.sleep(max(0.0, nxt - now - 0.0004))
                continue
            lag = (now - nxt) * 1000.0
            if lag > self.max_lag_ms:
                self.max_lag_ms = lag
            if lag > 40:
                self.late_ticks += 1
                nxt = now
            nxt += 0.02
            with self.lock:
                lst = list(self.streams)
            if lst:
                self.ticks += 1
            n = 0
            for st in lst:
                if st.sending:
                    st.send_one()
                    n += 1
            self.total_tx += n

    def _rx_loop(self):
        while self.running:
            try:
                events = self.sel.select(0.02)
            except Exception:
                time.sleep(0.01)
                continue
            t = time.time()
            for key, _ in events:
                st = self.by_sock.get(key.fileobj)
                if st is None:
                    continue
                for _ in range(64):
                    try:
                        data, addr = st.sock.recvfrom(2048)
                    except (BlockingIOError, InterruptedError):
                        break
                    except OSError:
                        break
                    self.total_rx += 1
                    st.on_packet(data, t)

    def stop(self):
        self.running = False


# ------------------------------------------------------------------ audio fidelity analysis of the tone test
import operator as _op

_PROJ = {}


def _proj_tables(f, m):
    t = _PROJ.get((f, m))
    if t is None:
        w = 2 * math.pi * f / 8000.0
        t = ([math.cos(w * k) for k in range(m)], [math.sin(w * k) for k in range(m)])
        _PROJ[(f, m)] = t
    return t


def _tone_stats(block, freqs, exp_amp):
    """Fit sinusoids at the known frequencies; -> (snr_db, level_db, [phases])."""
    m = len(block)
    sig, lv, ph = 0.0, [], []
    for f in freqs:
        ct, st = _proj_tables(f, m)
        c = sum(map(_op.mul, block, ct))
        s = sum(map(_op.mul, block, st))
        a = 2.0 * math.hypot(c, s) / m
        sig += a * a / 2.0
        lv.append(20 * math.log10(max(a, 1e-6) / exp_amp))
        ph.append(math.atan2(-s, c))
    tot = sum(v * v for v in block) / m
    res = max(tot - sig, tot * 1e-6, 1e-9)
    return min(60.0, 10 * math.log10(max(sig, 1e-9) / res)), sum(lv) / len(lv), ph


def _wrap(a):
    return (a + math.pi) % (2 * math.pi) - math.pi


def _interp(x, pts):
    if x <= pts[0][0]:
        return pts[0][1]
    for (x0, y0), (x1, y1) in zip(pts, pts[1:]):
        if x <= x1:
            return y0 + (y1 - y0) * (x - x0) / (x1 - x0)
    return pts[-1][1]


def analyze_tones(pcm):
    """Measure how cleanly the tone test arrived.  pcm = int16 samples at 8 kHz (>= 3 s).
    Returns snr_db, level_db, freq_hz, digits_*, dropout_ms, noise_floor_dbfs and a 1-5 score."""
    x = list(pcm[4000:84000]) if len(pcm) > 4000 + 24000 else list(pcm)
    N = 160
    nfr = len(x) // N
    if nfr < 25:
        return {"error": "recording too short (%.1f s)" % (len(x) / 8000.0), "score": None}
    allf = list(DTMF_LOW) + list(DTMF_HIGH) + [TT_REF_HZ]
    coef = {f: 2 * math.cos(2 * math.pi * f / 8000.0) for f in allf}
    labels = []
    for fr in range(nfr):
        seg = x[fr * N:(fr + 1) * N]
        e = sum(v * v for v in seg) / N
        if e < 400:
            labels.append("S")
            continue
        tp = {}
        for f in allf:
            c, s1, s2 = coef[f], 0.0, 0.0
            for v in seg:
                s1, s2 = v + c * s1 - s2, s1
            tp[f] = 2.0 * (s1 * s1 + s2 * s2 - c * s1 * s2) / (N * N)
        lo = max(DTMF_LOW, key=tp.get)
        hi = max(DTMF_HIGH, key=tp.get)
        if tp[TT_REF_HZ] >= 0.6 * e:
            labels.append("R")
        elif tp[lo] + tp[hi] >= 0.6 * e and tp[lo] >= 0.1 * e and tp[hi] >= 0.1 * e:
            labels.append(DTMF_REV[(lo, hi)])
        else:
            labels.append("?")
    # runs -> events; a short hole inside one tone is a dropout, not a second tone
    runs = []
    for i, l in enumerate(labels):
        if runs and runs[-1][0] == l:
            runs[-1][2] = i + 1
        else:
            runs.append([l, i, i + 1])
    ev = []
    for r in runs:
        if r[0] in ("S", "?"):
            continue
        if ev and ev[-1][0] == r[0] and r[1] - ev[-1][2] <= 25:
            ev[-1][2] = r[2]
        elif r[2] - r[1] >= 3:
            ev.append(list(r))
    ev = [e for e in ev if e[2] - e[1] >= 3]
    if len(ev) < 2:
        return {"error": "no test tones heard - the OTHER end is not sending the Tone test (set Tone test on both testers), or no audio came through", "score": None, "tones_found": len(ev)}
    snrs, levels, dev, drop_ms, freqerr = [], [], [], 0, []
    for lab, a, b in ev:
        lo_s, hi_s = (a + 1) * N, (b - 1) * N
        if lab == "R":
            freqs, amp = (TT_REF_HZ,), TT_REF_AMP
        else:
            freqs, amp = DTMF_MAP[lab], TT_DTMF_AMP
        span = hi_s - lo_s
        M = 800 if span >= 800 else (400 if span >= 480 else 0)
        phases = []
        if M:
            for j in range(span // M):
                blk = x[lo_s + j * M: lo_s + (j + 1) * M]
                sn, lv, ph = _tone_stats(blk, freqs, amp)
                snrs.append(sn)
                levels.append(lv)
                phases.append(ph[0])
            if lab == "R" and M == 800 and len(phases) >= 3:
                exp = 2 * math.pi * ((TT_REF_HZ * M / 8000.0) % 1.0)
                d = [_wrap(_wrap(phases[i + 1] - phases[i]) - exp) for i in range(len(phases) - 1)]
                freqerr.append(sum(d) / len(d) / (2 * math.pi) * 8000.0 / M)
        pw = [sum(v * v for v in x[k:k + 80]) / 80.0 for k in range(lo_s, hi_s - 79, 80)]
        if pw:
            med = sorted(pw)[len(pw) // 2]
            drop_ms += 10 * sum(1 for p in pw if p < 0.03 * med)
        if lab != "R":
            dev.append(lab)
    ok = miss = wrong = 0
    prev = None
    for d in dev:
        i = DTMF_KEYS.index(d)
        if prev is None:
            ok += 1
        else:
            k = (i - prev - 1) % 12
            if k == 0:
                ok += 1
            elif k <= 3:
                ok += 1
                miss += k
            else:
                wrong += 1
        prev = i
    sil = [labels_i for labels_i, l in enumerate(labels) if l == "S"]
    ms = [sum(v * v for v in x[i * N:(i + 1) * N]) / N for i in sil]
    nf = 10 * math.log10(max(sum(ms) / len(ms), 1e-3) / (32768.0 ** 2)) if ms else None
    snr = sum(snrs) / len(snrs) if snrs else None
    lvl = sum(levels) / len(levels) if levels else None
    fe = sum(freqerr) / len(freqerr) if freqerr else None
    tot = ok + miss + wrong
    pct = 100.0 * ok / tot if tot else 0.0
    score = _interp(snr if snr is not None else 0.0, [(5, 1.5), (15, 3.0), (25, 4.0), (33, 4.4), (60, 4.5)])
    score -= (1 - pct / 100.0) * 1.5
    score -= min(1.0, drop_ms / 300.0)
    if lvl is not None and abs(lvl) > 6:
        score -= 0.6
    elif lvl is not None and abs(lvl) > 3:
        score -= 0.3
    if fe is not None and abs(fe) > 2.0:
        score -= 0.3
    if nf is not None and nf > -50:
        score -= 0.3
    return {"snr_db": rnd(snr, 1), "level_db": rnd(lvl, 2), "freq_hz": rnd(fe, 2), "digits_ok": ok, "digits_missing": miss,
            "digits_wrong": wrong, "digits_pct": round(pct, 1), "dropout_ms": drop_ms, "noise_floor_dbfs": rnd(nf, 1),
            "tones_found": len(ev), "score": round(max(1.0, min(4.5, score)), 2)}


def decode_pcm(rec, pt):
    return array.array("h", map(DEC[pt].__getitem__, rec))


# ------------------------------------------------------------------ Contact ID (alarm panel -> central station, DTMF in the audio)
# Receiver sends a 1400 Hz handshake (100 ms), the panel sends 16 DTMF digits (50 ms tone / 50 ms gap):
#   AAAA 18 QEEE GG CCC S   account, message type, event qualifier+code, group, zone, check digit
# The sum of the 16 digits (0 counts as 10, B..F as 11..15) must be a multiple of 15.  The receiver then answers with
# a 1400 Hz kiss-off (about 800 ms).  No kiss-off = the panel sends again (up to 4 tries) and finally reports a failure.
CID_GRID = ("123A", "456B", "789C", "*0#D")
CID_WIRE = {c: c for c in "0123456789"}
CID_WIRE.update({"B": "*", "C": "#", "D": "A", "E": "B", "F": "C"})        # digit 11..15 are sent as these DTMF keys
CID_FROM_WIRE = {v: k for k, v in CID_WIRE.items()}
CID_FREQ = {}
for _r, _row in enumerate(CID_GRID):
    for _c, _k in enumerate(_row):
        CID_FREQ[_k] = (DTMF_LOW[_r], DTMF_HIGH[_c])
CID_EVENTS = {"110": "Fire", "120": "Panic", "121": "Duress", "130": "Burglary", "131": "Perimeter", "132": "Interior", "134": "Entry/exit",
              "140": "General alarm", "301": "AC power loss", "302": "Low battery", "305": "System reset", "401": "Open/close by user",
              "402": "Group open/close", "441": "Armed stay", "570": "Zone bypass", "602": "Periodic test report", "603": "Periodic RF transmission"}
CID_HS_HZ, CID_HS_AMP, CID_DTMF_AMP = 1400, 6000.0, 3500.0
CID_TRIES = 4


def cid_val(ch):
    return 10 if ch == "0" else (int(ch) if ch.isdigit() else "0123456789ABCDEF".index(ch))


def cid_check_digit(first15):
    s = sum(cid_val(c) for c in first15) % 15
    c = (15 - s) % 15
    return "F" if c == 0 else ("0" if c == 10 else "0123456789ABCDEF"[c])


def cid_build(acct="1234", event="1602", group="00", zone="000", fault=""):
    """The 16-digit message.  fault 'badsum' breaks the check digit, 'short' drops the last digit."""
    body = acct + "18" + event + group + zone
    chk = cid_check_digit(body)
    if fault == "badsum":
        chk = "1" if chk != "1" else "2"
    msg = body + chk
    if fault == "short":
        msg = msg[:15]
    return msg


def cid_valid(msg):
    return len(msg) == 16 and all(c in "0123456789BCDEF" for c in msg) and sum(cid_val(c) for c in msg) % 15 == 0


def cid_describe(msg):
    if len(msg) != 16:
        return {}
    ev = msg[7:10]
    q = {"1": "new event / alarm", "3": "restore", "6": "status"}.get(msg[6], "q%s" % msg[6])
    return {"account": msg[0:4], "type": msg[4:6], "qualifier": q, "event": msg[6:10], "event_name": CID_EVENTS.get(ev, "code " + ev),
            "group": msg[10:12], "zone": msg[12:15], "check": msg[15]}


def cid_parse_param(s):
    """'1234 1130 01 001' (account event group zone; later parts optional) -> dict."""
    parts = [x for x in re.split(r"[\s,;/-]+", str(s or "").strip()) if x]
    d = {"acct": "1234", "event": "1602", "group": "00", "zone": "000"}
    for key, ln, alpha in (("acct", 4, "0123456789ABCDEF"), ("event", 4, "0123456789"), ("group", 2, "0123456789"), ("zone", 3, "0123456789")):
        if not parts:
            break
        v = parts.pop(0).upper()
        if len(v) != ln or any(ch not in alpha for ch in v):
            raise ValueError("Contact ID: '%s' should be %d characters (format: account event group zone, e.g. 1234 1130 01 001)" % (v, ln))
        d[key] = v
    if parts:
        raise ValueError("Contact ID: too many parts (account event group zone)")
    if d["event"][0] not in "136":
        raise ValueError("Contact ID: the event starts with 1 (new), 3 (restore) or 6 (status), e.g. 1130")
    return d


def cid_frames(pt, parts):
    """parts: ('t', freqs, amp, ms) tones or ('s', ms) silence -> list of 160-byte G.711 frames."""
    pcm = array.array("h")
    for p in parts:
        if p[0] == "s":
            pcm.extend([0] * int(8 * p[1]))
            continue
        _, freqs, amp, ms = p
        n = int(8 * ms)
        for i in range(n):
            env = min(1.0, i / 16.0, (n - 1 - i) / 16.0)
            pcm.append(int(round(sum(math.sin(2 * math.pi * f * i / 8000.0) for f in freqs) * amp * env)))
    pad = (-len(pcm)) % 160
    if pad:
        pcm.extend([0] * pad)
    tb = enc_table(pt)
    raw = bytes(tb[s + 32768] for s in pcm)
    return [raw[i:i + 160] for i in range(0, len(raw), 160)]


def cid_handshake_parts(ms=100):
    return [("t", (CID_HS_HZ,), CID_HS_AMP, ms)]


def cid_message_parts(msg):
    out = []
    for c in msg:
        out.append(("t", CID_FREQ[CID_WIRE[c]], CID_DTMF_AMP, 50))
        out.append(("s", 50))
    return out


_CID_FREQS = (697, 770, 852, 941, 1209, 1336, 1477, 1633, 1400)
_CID_COS = [[math.cos(2 * math.pi * f * n / 8000.0) for n in range(80)] for f in _CID_FREQS]
_CID_SIN = [[math.sin(2 * math.pi * f * n / 8000.0) for n in range(80)] for f in _CID_FREQS]
_CID_ROT = [[complex(math.cos(2 * math.pi * f * 80 * k / 8000.0), -math.sin(2 * math.pi * f * 80 * k / 8000.0)) for k in range(4)] for f in _CID_FREQS]


class CidDetector:
    """Finds 1400 Hz tones and DTMF digits in an audio stream (40 ms windows every 10 ms).
    events: (time, 'T', length ms) for a 1400 Hz tone, (time, 'D', cid character) for a digit."""

    def __init__(self):
        self.buf = []
        self.blocks = collections.deque(maxlen=4)
        self.cur = None
        self.hops = 0
        self.events = collections.deque()

    def feed(self, samples):
        self.buf.extend(samples)
        mul = operator.mul
        while len(self.buf) >= 80:
            blk = self.buf[:80]
            del self.buf[:80]
            xs = []
            for i in range(9):
                re_ = sum(map(mul, blk, _CID_COS[i]))
                im_ = sum(map(mul, blk, _CID_SIN[i]))
                xs.append(complex(re_, -im_))
            self.blocks.append((xs, sum(map(mul, blk, blk))))
            if len(self.blocks) == 4:
                self._hop(self._classify())

    def _classify(self):
        E = sum(b[1] for b in self.blocks)
        if E / 320.0 < 150.0 * 150.0:
            return None
        r = []
        for i in range(9):
            x = sum(self.blocks[k][0][i] * _CID_ROT[i][k] for k in range(4))
            r.append(2.0 * (x.real * x.real + x.imag * x.imag) / (320.0 * E))
        if r[8] > 0.65:
            return "T"
        lo = sorted(range(4), key=lambda i: -r[i])
        hi = sorted(range(4, 8), key=lambda i: -r[i])
        rl, rh = r[lo[0]], r[hi[0]]
        if rl > 0.15 and rh > 0.15 and rl + rh > 0.6 and r[lo[1]] < rl * 0.25 and r[hi[1]] < rh * 0.25 and 0.2 < rh / rl < 5.0:
            return CID_GRID[lo[0]][hi[0] - 4]
        return None

    def _hop(self, label):
        if label == self.cur:
            self.hops += 1
            return
        if self.cur is not None:
            ln = self.hops * 10 + 20
            if self.cur == "T":
                self.events.append((time.time(), "T", ln))
            else:
                self.events.append((time.time(), "D", CID_FROM_WIRE.get(self.cur, "?")))
        self.cur, self.hops = label, 1


def cid_attach(st):
    """Send scripted audio on this stream and decode what comes back."""
    det = CidDetector()
    st.script_mode = True

    def tap(pt, payload, gap):
        if gap < 0:
            return
        if 0 < gap < 50:
            det.feed([0] * (160 * gap))
        det.feed(list(map(DEC[pt].__getitem__, payload)))

    st.rx_tap = tap
    return det


def cid_play(st, pt, parts):
    """Queue audio; returns the time (seconds) it takes to play."""
    fr = cid_frames(pt, parts)
    st.script.extend(fr)
    return len(fr) * 0.02


def cid_wait(node, call, secs):
    """Sleep secs; False when the call or tester is stopping."""
    end = time.time() + secs
    while time.time() < end:
        if node.stopping or getattr(call, "abort", False) or call.done:
            return False
        time.sleep(0.01)
    return True


def cid_next_tone(det, since, timeout, node, call):
    """Wait for the next 1400 Hz tone after time since.  Returns (time, length ms) or None."""
    end = time.time() + timeout
    while time.time() < end:
        if node.stopping or getattr(call, "abort", False) or call.done:
            return None
        while det.events:
            ev = det.events.popleft()
            if ev[1] == "T" and ev[0] >= since and ev[2] >= 50:
                return ev[0], ev[2]
        time.sleep(0.01)
    return None


def cid_panel(node, call, st, mp, fault, count=1, hs_timeout=15.0):
    """The customer side (alarm panel): waits for the handshake, sends the message, waits for the kiss-off.
    With count > 1 it sends the same message again after each kiss-off (the receiver offers a new handshake)."""
    info = {"role": "panel", "ok": False, "tries": 0, "sent": "", "kiss_ms": None, "hs_ms": None, "total_ms": None, "why": "", "count": count, "msgs": 0}
    call.cid = info
    t_up = time.time()
    try:
        pt = st.tx_pt if st.tx_pt in REAL_PT else 0
        det = cid_attach(st)
        msg = cid_build(mp["acct"], mp["event"], mp["group"], mp["zone"], fault)
        info["sent"] = msg
        hs = cid_next_tone(det, t_up, hs_timeout, node, call)
        if hs is None:
            info["why"] = "no handshake tone from the receiver within %d s" % hs_timeout
            return
        info["hs_ms"] = round((hs[0] - t_up) * 1000)
        info["hs_len"] = hs[1]
        for k in range(count):
            got = None
            for attempt in range(1, CID_TRIES + 1):
                info["tries"] += 1
                if not cid_wait(node, call, 0.15):
                    return
                t_send = time.time()
                dur = cid_play(st, pt, cid_message_parts(msg))
                if not cid_wait(node, call, dur + 0.05):
                    return
                ans = cid_next_tone(det, t_send, 4.0, node, call)
                if ans is None:
                    info["why"] = "no kiss-off after the message (try %d)" % attempt
                    continue
                if ans[1] >= 500:
                    got = ans
                    break
                info["why"] = "receiver sent a short tone (%d ms) instead of a kiss-off: it asked for the message again" % ans[1]
            if got is None:
                info["why"] = ("message %d: " % (k + 1) if count > 1 else "") + "no kiss-off after %d tries" % CID_TRIES + ("; last: " + info["why"] if info["why"] else "")
                return
            info["msgs"] += 1
            info["kiss_ms"] = got[1]
            info["total_ms"] = round((got[0] - t_up) * 1000)
            info["why"] = ""
            if k + 1 < count and cid_next_tone(det, got[0], 4.0, node, call) is None:
                info["why"] = "the receiver did not offer another handshake for message %d" % (k + 2)
                return
        info["ok"] = True
    finally:
        call.cid_end = time.time()
        call.cid_evt.set()


def cid_receiver(node, call, st, plan):
    """The carrier side (central station receiver): handshake, collect 16 digits, check them, kiss-off (or ask again).
    After a kiss-off it offers another handshake so the panel can send more messages."""
    mode = plan.get("cid_mode", "ok")                   # ok | nohand (never sends a handshake) | nokiss (never sends the kiss-off)
    info = {"role": "receiver", "ok": False, "tries": 0, "digits": "", "valid": False, "why": "", "mode": mode, "messages": []}
    call.cid = info
    try:
        pt = st.tx_pt if st.tx_pt in REAL_PT else 0
        det = cid_attach(st)
        if mode == "nohand":
            info["why"] = "test mode: handshake never sent"
            cid_wait(node, call, 25)
            return
        if not cid_wait(node, call, float(plan.get("cid_delay_ms", 400)) / 1000.0):
            return

        def collect(first_wait):
            digits = []
            t0 = time.time()
            last = t0
            while True:
                if node.stopping or getattr(call, "abort", False) or call.done:
                    return None
                while det.events:
                    ev = det.events.popleft()
                    if ev[1] == "D" and ev[0] >= t0:
                        digits.append(ev[2])
                        last = time.time()
                if len(digits) >= 16:
                    cid_wait(node, call, 0.15)
                    break
                if digits and time.time() - last > 1.0:
                    break
                if not digits and time.time() > t0 + first_wait:
                    break
                time.sleep(0.01)
            return "".join(digits)

        left, first = CID_TRIES, True
        while left > 0:
            det.events.clear()
            dur = cid_play(st, pt, cid_handshake_parts(100))
            if not cid_wait(node, call, dur):
                return
            msg = collect(6.0 if first else 3.5)
            if msg is None:
                return
            if not msg:
                if not first and info["ok"]:
                    return                                   # no further message: normal end
                info["tries"] += 1
                info["why"] = "no digits received after the handshake"
                left -= 1
                continue
            info["tries"] += 1
            info["digits"] = msg
            if cid_valid(msg) and msg[4:6] in ("18", "98"):
                info["valid"] = True
                info.update(cid_describe(msg))
                if mode == "nokiss":
                    info["why"] = "test mode: kiss-off withheld"
                    left -= 1
                    continue
                cid_wait(node, call, 0.15)
                dur = cid_play(st, pt, cid_handshake_parts(800))
                cid_wait(node, call, dur)
                info["ok"] = True
                info["why"] = ""
                info["messages"].append(msg)
                first, left = False, CID_TRIES
                cid_wait(node, call, 0.4)                    # a gap, so the next handshake is not heard as part of the kiss-off
                continue
            info["valid"] = False
            info["why"] = ("checksum wrong" if len(msg) == 16 else "%d digits received, 16 expected" % len(msg)) + " (%s)" % msg
            left -= 1
            first = False if info["ok"] else first
    finally:
        call.cid_end = time.time()
        call.cid_evt.set()


# ------------------------------------------------------------------ caller ID / STIR-SHAKEN readback (9989xxx)
def _b64json(s):
    try:
        s += "=" * (-len(s) % 4)
        return json.loads(base64.urlsafe_b64decode(s.encode()).decode("utf-8", "replace"))
    except Exception:
        return None


def _digits(s):
    return "".join(ch for ch in str(s or "") if ch.isdigit())


def _hdr_ident(v):
    """'"Name" <sip:123@host;user=phone>;verstat=...' -> (display name, user, whole header text)."""
    v = v or ""
    m = re.match(r'\s*(?:"([^"]*)"|([^<"]*?))\s*<', v)
    name = ((m.group(1) if m and m.group(1) is not None else (m.group(2) if m else "")) or "").strip()
    u = re.search(r"(?:sips?|tel):\+?([^@;>\s,]+)", v)
    return name, (u.group(1) if u else ""), v


def parse_caller_info(inv):
    """What the INVITE says about the caller: From, P-Asserted-Identity, STIR/SHAKEN Identity header and verstat."""
    info = {"from": "", "from_name": "", "from_user": "", "pai": [], "ppi": "", "rpid": "", "verstat": "", "attest_ind": "",
            "identity": [], "attest": "", "stir": "no Identity header (no STIR/SHAKEN signature received)"}
    info["from"] = inv.h("from")
    info["from_name"], info["from_user"], _ = _hdr_ident(info["from"])
    for v in inv.hs("p-asserted-identity"):
        for part in re.split(r",(?=\s*(?:\"|<|sips?:|tel:))", v):
            info["pai"].append(_hdr_ident(part)[1] or part.strip())
    info["ppi"] = _hdr_ident(inv.h("p-preferred-identity"))[1]
    info["rpid"] = _hdr_ident(inv.h("remote-party-id"))[1]
    whole = " ".join([inv.h("from"), inv.h("p-asserted-identity"), inv.h("remote-party-id"), inv.h("p-preferred-identity"), inv.h("contact")])
    m = re.search(r"verstat=([\w-]+)", whole, re.I)
    info["verstat"] = m.group(1) if m else ""
    info["attest_ind"] = inv.h("p-attestation-indicator")
    for v in inv.hs("identity") + inv.hs("y"):
        tok = v.split(";")[0].strip().strip('"<> ')
        params = dict((k.strip().lower(), x.strip().strip('"<>')) for k, _, x in (p.partition("=") for p in v.split(";")[1:]))
        parts = tok.split(".")
        d = {"info": params.get("info", ""), "alg": params.get("alg", ""), "ppt": params.get("ppt", ""), "ok_format": False}
        if len(parts) == 3:
            hd, pl = _b64json(parts[0]), _b64json(parts[1])
            if isinstance(pl, dict):
                d["ok_format"] = True
                d["header"] = hd if isinstance(hd, dict) else {}
                d["attest"] = str(pl.get("attest", ""))
                d["orig"] = (pl.get("orig") or {}).get("tn", "") if isinstance(pl.get("orig"), dict) else ""
                dest = pl.get("dest") or {}
                d["dest"] = dest.get("tn", []) if isinstance(dest, dict) else []
                d["iat"] = pl.get("iat")
                d["origid"] = pl.get("origid", "")
                if isinstance(d["iat"], (int, float)):
                    d["age_s"] = round(time.time() - d["iat"])
        info["identity"].append(d)
    ids = [d for d in info["identity"] if d.get("ok_format")]
    if ids:
        d = ids[0]
        info["attest"] = d.get("attest", "").upper()
        fr = _digits(info["from_user"]) or _digits(info["pai"][0] if info["pai"] else "")
        info["orig_matches_from"] = bool(_digits(d.get("orig")) and fr and _digits(d.get("orig"))[-10:] == fr[-10:])
        info["stir"] = "signed, attestation %s%s" % (info["attest"] or "?", "" if info["orig_matches_from"] else " (signed number does NOT match the From number)")
    elif info["identity"]:
        info["stir"] = "Identity header present but could not be decoded"
    elif info["attest_ind"]:
        info["attest"] = info["attest_ind"].strip()[:1].upper()
        info["stir"] = "P-Attestation-Indicator: " + info["attest_ind"]
    if info["verstat"]:
        info["stir"] += "; verstat " + info["verstat"]
    info["note"] = "The signature itself is not verified here: this shows what reached the tester."
    return info


_RB_CACHE = {}
_RB_EMB = {}


def _rb_embedded(name):
    """The clips built into this file (used when audio/readback/<name>.wav is not there)."""
    if not _RB_EMB:
        raw = zlib.decompress(base64.b64decode(RB_DATA))
        head, _, blob = raw.partition(b"\n")
        for k, (o, n) in json.loads(head.decode()).items():
            _RB_EMB[k] = array.array("h", map(DEC[0].__getitem__, blob[o:o + n]))
    return _RB_EMB.get(name) or array.array("h")


def _rb_clip(audio_dir, name):
    """audio/readback/<name>.wav when present (so you can swap the voice), else the built-in clip."""
    f = os.path.join(audio_dir, "readback", name + ".wav")
    c = _RB_CACHE.get(f)
    if c is None:
        try:
            w = wave.open(f)
            c = array.array("h", w.readframes(w.getnframes()))
            if w.getframerate() != 8000:
                c = array.array("h")
        except Exception:
            c = array.array("h")
        if not c:
            c = _rb_embedded(name)
        _RB_CACHE[f] = c
    return c


_RB_WORDS = {}


def _rb_word(audio_dir, w):
    """A spoken name/word from audio/readback/words.pack (None when the pack or the word is not there)."""
    f = os.path.join(audio_dir, "readback", "words.pack")
    try:
        mt = os.path.getmtime(f)
    except OSError:
        return None
    c = _RB_WORDS.get(f)
    if c is None or c[0] != mt:
        try:
            raw = zlib.decompress(open(f, "rb").read())
            head, _, blob = raw.partition(b"\n")
            c = (mt, json.loads(head.decode()), blob)
        except Exception as e:
            log("words.pack could not be read:", repr(e))
            c = (mt, {}, b"")
        _RB_WORDS.clear()
        _RB_WORDS[f] = c
    ent = c[1].get(w)
    if not ent:
        return None
    return array.array("h", map(DEC[0].__getitem__, c[2][ent[0]:ent[0] + ent[1]]))


def readback_pcm(audio_dir, info, restricted=False):
    out = array.array("h")

    def gap(ms):
        out.extend([0] * int(8 * ms))

    def clip(name):
        out.extend(_rb_clip(audio_dir, name))

    def spell(text, group=False):
        n = 0
        for ch in str(text).lower()[:24]:
            if ch.isdigit():
                clip("d_" + ch)
                n += 1
                gap(320 if (group and n in (3, 6)) else 130)
            elif ch.isalpha():
                clip("l_" + ch)
                gap(180)
            else:
                gap(200)

    def say_name(text):
        """Known names and words are spoken as words (Alice), anything else is spelled letter by letter."""
        toks = re.findall(r"[A-Z]?[a-z]+|[A-Z]+(?![a-z])|\d+", str(text))[:6]
        for t in toks:
            if t.isdigit():
                spell(t)
            else:
                w = _rb_word(audio_dir, t.lower())
                if w is not None:
                    out.extend(w)
                else:
                    spell(t)
            gap(350)

    if restricted:
        clip("p_restricted")
        return out

    def sentence():
        clip("p_from")
        gap(150)
        spell(info.get("from_user") or "", True)
        gap(500)
        if info.get("pai"):
            clip("p_pai")
            gap(150)
            spell(info["pai"][0], True)
        else:
            clip("p_nopai")
        gap(350)
        nm = info.get("from_name") or ""
        if nm and nm != info.get("from_user"):
            clip("p_name")
            gap(150)
            say_name(nm)
        else:
            clip("p_noname")
        gap(500)
        if info.get("attest"):
            clip("p_attest")
            gap(150)
            if info["attest"].lower() in ("a", "b", "c"):
                clip("l_" + info["attest"].lower())
            gap(300)
            if "orig_matches_from" in info:
                clip("p_matchok" if info["orig_matches_from"] else "p_matchbad")
        else:
            clip("p_nostir")
        gap(400)
        v = info.get("verstat", "").lower()
        if v:
            clip("p_verpass" if "passed" in v else "p_verfail")
            gap(400)

    gap(600)
    sentence()
    gap(1200)
    clip("p_from")                                   # the key facts once more
    gap(150)
    spell(info.get("from_user") or "", True)
    gap(500)
    if info.get("attest") and info["attest"].lower() in ("a", "b", "c"):
        clip("p_attest")
        gap(150)
        clip("l_" + info["attest"].lower())
    else:
        clip("p_nostir")
    gap(300)
    clip("p_goodbye")
    gap(500)
    return out


def pcm_frames(pt, pcm):
    pcm = array.array("h", pcm)
    pad = (-len(pcm)) % 160
    if pad:
        pcm.extend([0] * pad)
    tb = enc_table(pt)
    raw = bytes(tb[s + 32768] for s in pcm)
    return [raw[i:i + 160] for i in range(0, len(raw), 160)]


def readback_run(node, call, st, pt):
    """Optional password gate (restricted-number message, password typed on the keypad), then speak the caller's
    number, name and STIR/SHAKEN level, then end the call."""
    try:
        info = call.callerinfo if call.callerinfo is not None else {}
        call.callerinfo = info
        pw = "".join(ch for ch in str(getattr(node.args, "readback_password", "") or "").upper() if ch in "0123456789*#ABCD")
        gate = info["gate"] = {"required": bool(pw), "result": "no password needed", "digits": 0}
        if pw:
            det = cid_attach(st)                             # in-band keypad tones; RFC 2833 events arrive in st.rx_dtmf
            n0 = len(st.rx_dtmf)
            fr = pcm_frames(pt, readback_pcm(node.audio_dir, info, restricted=True))
            st.script.extend(fr)
            t_end = time.time() + len(fr) * 0.02 + 6.0
            ev = inband = ""
            ok = False
            while time.time() < t_end and not call.done and not node.stopping:
                ev = "".join(c for c in st.rx_dtmf[n0:] if c in "0123456789*#ABCD")
                while det.events:
                    e = det.events.popleft()
                    if e[1] == "D":
                        inband += CID_WIRE.get(e[2], "")          # detector reports Contact ID characters; map back to keypad keys
                if pw in ev or pw in inband:
                    ok = True
                    break
                time.sleep(0.05)
            gate["digits"] = max(len(ev), len(inband))
            if not ok:
                gate["result"] = "denied: no password entered" if not gate["digits"] else "denied: wrong password (%d keys entered)" % gate["digits"]
                call.end_after = time.time() + 0.3
                return
            gate["result"] = "accepted"
            st.script.clear()
            time.sleep(0.3)
        pcm = readback_pcm(node.audio_dir, info)
        if not pcm:
            return
        fr = pcm_frames(pt, pcm)
        st.script.extend(fr)
        call.end_after = time.time() + len(fr) * 0.02 + 1.5
    except Exception as e:
        log("readback failed:", repr(e))


RB_DATA = "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hSUAyjj8GnFle5+0fvDu4th/fLMOkebaKkTpp3u7x7uXr5dNvR1NTTI5X1LNr62RCKtltdWyjqbGvif53eX+ycDh8c71yVbHzv7+6XGk9eXivnfg4nrgraet9fWtvar75bVZ3t8uqet+lF+9tPa/nbR33571dR5Er8/O7/svutu+D/S2vrXXdQy8NTbL6yAq6noaeIl2/3o38HJ3+3x+9nD++HTb2fXa33t59fz/M1ZB4pS+p+7b3uhx03HrSf9VX8dAU0tVT8tzm1zSWH8y6DttXD9ce3os4QvaBc21Nw9b25Hz45fL+/OXPplMeCw5vdxtam3skL50VQ7IXp+vv3dF22S1DbVN7ad9F3cHFzt7B8ev18/S2+72x+7ngb7bztfLgc6XZml7p7Sp623w9Ob+fOD+/uahq7Wn+/vj6+1D30l/90HX94em29bXh/bH9rYB+fngzX3Hw8PNr12X39uvXjsf374/t9w3N/fKTlrO7huPm16PJGcdzzed923Pj3fRrqOm/ba2k5r+G8lJ+Z68c6sreiF7qr9qaXvreLm6u/3e13f1cn412NvfJIne97003TYMntftfG87EO909+/LDrtkB5XnDy1XHfetLWddp31XLYNdt69Ng9GG29771+7D29OLu9eWu1ZJn7xLet/7stMerhm45D013PU27p13bz4eyh6aok0tZ5L2l/uzxst2wWH9dvPJNm+3vTrEC0kaLsWXsp3NG1/leVP9nvistnSv/vDsbb3q6kDSXLvNu3gU/Xq2KdqN1O20HNa8bVaeNFfuC0KdB7sN503dzY09A9Kut/vXo5uulsP2yu7XTsHm6QvMQdFm423j6anodF8UPn69iDbxrutFskjhTv3z3YmnNDxYdsYb+H70sLcl3D9uDEkOpZey8qjg8bi2/631RLDTuntUH73q6ry+36+L1pxdde+2SHol4equTXFddK+vYeNaHH6RVG/LBG93gu7Ai2xd1lD+LKjYeKzYuuYeB6uDOxeVoeqOYHtH+Fx85+fXL9aKtpt5R7vCnb7mix6ZLNjdGD7vrz0eEEcfeP2C2nL5Wdvpef3dzvPN/v1x/d55zd35U/nha7T3hCvrE702XlbfHzydB85eDxpqS2tOiw52al+7z/kvEeHB4Nlbr/85sLsWPfI/3l23CuprSjgiHqOOxajlFzf5+/Zht5qfW52d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"


# ------------------------------------------------------------------ calls and the node
def detect_ip(hint="192.0.2.1"):
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect((hint, 9))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except OSError:
        return "127.0.0.1"


# Dial plan: the number dialed picks what the carrier does, so a tester (or any phone) can steer it through Yeti.
# prefix = first digits of the dialed number; action = answer|busy|notfound|unavail|servererr|forbidden|decline|temp|noanswer|timeout|badmedia
# audio = tone (DTMF test) | speech | echo (send back what we hear) | default (the audio chosen on this tester)
DEFAULT_DIALPLAN = [
    {"prefix": "9989", "name": "caller ID + STIR/SHAKEN readback", "action": "answer", "audio": "readback", "expect": "answered, reads back the calling number, caller name and attestation level"},
    {"prefix": "9980", "name": "Contact ID receiver", "action": "answer", "audio": "cid", "cid_mode": "ok", "expect": "answered, handshake sent, message checked, kiss-off sent"},
    {"prefix": "9981", "name": "Contact ID: no handshake", "action": "answer", "audio": "cid", "cid_mode": "nohand", "fail": True, "expect": "answered but the receiver never sends the handshake tone"},
    {"prefix": "9982", "name": "Contact ID: no kiss-off", "action": "answer", "audio": "cid", "cid_mode": "nokiss", "fail": True, "expect": "message received but the receiver never sends the kiss-off"},
    {"prefix": "9990", "name": "answer + tone test", "action": "answer", "audio": "tone", "expect": "answered, tone test played"},
    {"prefix": "9991", "name": "answer + speech", "action": "answer", "audio": "speech", "expect": "answered, speech played"},
    {"prefix": "9992", "name": "echo (hear yourself)", "action": "answer", "audio": "echo", "echo_ms": 0, "hangup_after": 60, "expect": "answered, your audio comes straight back (round-trip time is measured)"},
    {"prefix": "9993", "name": "answer after 5 s", "action": "answer", "audio": "default", "delay_ms": 5000, "expect": "answered after 5 s of ringing"},
    {"prefix": "9994", "name": "ring, never answer", "action": "noanswer", "expect": "rings, then 480 / caller gives up"},
    {"prefix": "9995", "name": "answer, no audio", "action": "answer", "rtp_mode": "none", "expect": "answered but silent (no RTP)"},
    {"prefix": "9996", "name": "answer, 5% audio loss", "action": "answer", "audio": "tone", "loss_pct": 5, "expect": "answered, about 5% loss heard"},
    {"prefix": "9997", "name": "486 busy", "action": "busy", "expect": "486 Busy Here"},
    {"prefix": "9998", "name": "404 not found", "action": "notfound", "expect": "404 Not Found"},
    {"prefix": "9999", "name": "503 unavailable", "action": "unavail", "expect": "503 Service Unavailable"},
]
CARRIER_DEFAULTS = {
    "dialplan_on": True, "dialplan": DEFAULT_DIALPLAN,
    "mix": {"answer": 100, "busy": 0, "notfound": 0, "unavail": 0, "servererr": 0, "forbidden": 0,
            "decline": 0, "temp": 0, "redirect": 0, "badmedia": 0, "noanswer": 0, "timeout": 0},
    "ring_ms": 500, "delay_min_ms": 0, "delay_max_ms": 0, "early_media": False,
    "rtp_mode": "normal",            # normal | none (never send audio) | blackhole (advertise a dead port) | private_ip (advertise 192.0.2.1)
    "loss_pct": 0.0, "hangup_after": 0, "auth_user": "", "auth_pass": "", "codecs": list(CODECS),
}
REPLY = {"busy": 486, "notfound": 404, "unavail": 503, "servererr": 500, "forbidden": 403, "decline": 603,
         "temp": 480, "redirect": 302, "badmedia": 488}
REALM = "sipload"
MAX_TRACE = 60


def call_rec_offset(rtp):
    """Samples by which the received recording starts after the sent recording (negative: before)."""
    if rtp.tx_t0 is None or rtp.rx_first_t is None:
        return 0
    return int(round((rtp.rx_first_t - rtp.tx_t0) * 8000))


class Call:
    def __init__(self, node, direction, call_id, method="INVITE"):
        self.node, self.dir, self.call_id, self.method = node, direction, call_id, method
        self.id = next(node.ids)
        self.q = queue.Queue()
        self.t0 = time.time()
        self.t_invite = self.t_18x = self.t_answer = self.t_end = None
        self.state = "init"
        self.number = self.peer = self.fault = self.expect = self.action = ""
        self.code = 0
        self.reason = ""
        self.result = ""
        self.hungup_by = ""
        self.answered = False
        self.retx = 0
        self.auth_fail = 0
        self.local_tag = new_tag()
        self.remote_addr = None
        self.rtp = None
        self.stats = None
        self.trace = []
        self.done = False
        self.talk_t0 = None
        self.rec = b""
        self.rec_pt = None
        self.rec_tx = b""
        self.rec_off = 0
        self.tx_pt = 0
        self.caller = ""
        self.auth_user = self.auth_pass = ""
        self.dtmf_expect = ""
        self.akind = ""
        self.tone = None
        self.peer_sipload = True             # False when the caller is not another sipload (a phone, a PBX): no tone scoring
        self.callerinfo = None               # From / P-Asserted-Identity / STIR-SHAKEN as received
        self.end_after = 0.0
        self.cid = None                      # Contact ID result
        self.cid_evt = threading.Event()
        self.cid_end = None

    def wait(self, timeout):
        try:
            return self.q.get(timeout=max(0.0, timeout))
        except queue.Empty:
            return None

    def note(self, direction, text):
        if len(self.trace) < MAX_TRACE:
            self.trace.append((round(time.time() - self.t0, 3), direction, text[:2500]))

    def dur(self):
        if self.talk_t0 is None:
            return 0.0
        return round((self.t_end or time.time()) - self.talk_t0, 1)

    def snapshot_stats(self):
        if self.rtp is not None:
            self.stats = self.rtp.stats()

    def to_dict(self, detail=False):
        s = self.stats or (self.rtp.stats() if self.rtp is not None else {})
        d = {
            "id": self.id, "dir": self.dir, "method": self.method, "number": self.number, "caller": self.caller, "peer": self.peer,
            "dtmf_expect": self.dtmf_expect, "tone": (self.tone or {}).get("score"), "rtt": s.get("rtt_ms"), "codec": s.get("rx_codec", ""), "tone_err": bool(self.tone and self.tone.get("error")),
            "state": self.state, "result": self.result, "code": self.code, "reason": self.reason, "fault": self.fault,
            "expect": self.expect, "action": self.action, "started": round(self.t0, 3), "dur": self.dur(),
            "setup_ms": round((self.t_answer - self.t_invite) * 1000) if self.t_answer and self.t_invite else None,
            "pdd_ms": round(((self.t_18x or self.t_answer) - self.t_invite) * 1000) if (self.t_18x or self.t_answer) and self.t_invite else None,
            "hungup_by": self.hungup_by, "answered": self.answered, "retx": self.retx, "auth_fail": self.auth_fail,
            "tx": s.get("tx_packets", 0), "rx": s.get("rx_packets", 0), "loss": s.get("loss_pct"), "jitter": s.get("jitter_ms"),
            "mos": s.get("mos"), "audio_ok": s.get("audio_ok"), "exact": s.get("exact_pct"), "rx_codec": s.get("rx_codec", ""),
            "live": self.rtp is not None and not self.done, "dtmf": s.get("dtmf", ""), "cid": self.cid, "attest": (self.callerinfo or {}).get("attest", ""),
        }
        if detail:
            d["trace"] = self.trace
            d["stats"] = s
            d["tone_detail"] = self.tone
            d["callerinfo"] = self.callerinfo
        return d


class Node:
    def __init__(self, role, args):
        self.role = role
        self.args = args
        self.ids = iter(range(1, 10 ** 9))
        self.lock = threading.RLock()
        self.calls = {}
        self.history = collections.deque(maxlen=5000)
        self.codes = collections.Counter()
        self.results = collections.Counter()
        self.series = collections.deque(maxlen=3600)
        self.started = time.time()
        self.stopping = False
        self.sip_rx = self.sip_tx = self.sip_retx = 0
        self.peak = 0
        self.nonces = set()
        self.audio = Audio(args.audio) if args.audio else Audio()
        self.audio_dir = args.audio_dir
        self.cfg = json.loads(json.dumps(CARRIER_DEFAULTS))
        self.thresholds = {"min_asr": 95.0, "max_pdd_ms": 2000, "min_mos": 3.8, "max_loss_pct": 1.0, "max_jitter_ms": 30.0, "min_tone": 4.0}
        self.tone_limit = getattr(args, "tone_limit", 5000)
        self.tone_budget = self.tone_limit
        self.aq = queue.Queue()
        threading.Thread(target=self._tone_worker, daemon=True, name="tone-analysis").start()
        self.run = None
        self.rec_seconds = args.record_seconds
        bind = args.bind
        self.adv_ip = args.advertise_ip or (bind if bind not in ("0.0.0.0", "") else detect_ip(getattr(args, "target_host", None) or "192.0.2.1"))
        self.sock = udp_socket()
        self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        try:
            self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 1 << 21)
        except OSError:
            pass
        self.sock.bind((bind, args.sip_port))
        self.sip_port = self.sock.getsockname()[1]
        self.rtp = RtpEngine(bind, args.rtp_min, args.rtp_max)
        threading.Thread(target=self._rx_loop, daemon=True, name="sip-rx").start()
        threading.Thread(target=self._sampler, daemon=True, name="sampler").start()

    # ---- transport
    def sip_send(self, data, addr, call=None, retx=False):
        try:
            self.sock.sendto(data, addr)
        except OSError as e:
            log("SIP send failed:", e)
            return
        self.sip_tx += 1
        if retx:
            self.sip_retx += 1
            if call:
                call.retx += 1
        if call:
            call.note("tx", data.decode("utf-8", "replace"))

    def _rx_loop(self):
        while not self.stopping:
            try:
                data, addr = self.sock.recvfrom(65535)
            except OSError:
                if self.stopping:
                    return
                continue
            if len(data) < 12:
                continue                                    # keep-alive blanks
            msg = parse_msg(data, addr)
            if msg is None:
                continue
            self.sip_rx += 1
            try:
                self.dispatch(msg, addr)
            except Exception as e:                           # never let one packet kill the loop
                log("dispatch error:", repr(e))

    def dispatch(self, msg, addr):
        cid = msg.call_id
        with self.lock:
            call = self.calls.get(cid)
        if call is not None:
            call.note("rx", msg.raw)
            call.q.put(msg)
            return
        if msg.is_request:
            m = msg.method
            if m == "INVITE" and self.role == "carrier":
                c = Call(self, "in", cid)
                c.note("rx", msg.raw)
                with self.lock:
                    self.calls[cid] = c
                threading.Thread(target=self._guard, args=(self.uas_run, c, msg), daemon=True).start()
            elif m == "REGISTER" and self.role == "carrier":
                self.on_register(msg, addr)
            elif m == "OPTIONS":
                self.sip_send(self.simple_resp(msg, 200), addr)
            elif m in ("BYE", "CANCEL"):
                self.sip_send(self.simple_resp(msg, 200 if m == "BYE" else 481), addr)
            elif m == "ACK":
                pass
            else:
                self.sip_send(self.simple_resp(msg, 403 if m == "INVITE" else 405), addr)

    def on_register(self, msg, addr):
        """Registrar for testing: accepts anyone, or requires digest auth when a username is configured."""
        cfg = self.cfg
        a = msg.h("authorization")
        if not cfg["auth_user"]:
            self.sip_send(self.simple_resp(msg, 200), addr)
            return
        good = bool(a) and digest_check(a, "REGISTER", cfg["auth_pass"], REALM, self.nonces) \
            and parse_challenge(a).get("username") == cfg["auth_user"]
        if good or a:
            c = Call(self, "in", msg.call_id, "REGISTER")
            c.peer, c.t0 = "%s:%d" % addr, time.time()
            c.number = parse_challenge(a).get("username", "") if a else ""
            c.t_invite = c.t_answer = c.t0
            c.note("rx", msg.raw)
            if good:
                self.sip_send(self.simple_resp(msg, 200), addr, c)
                self.finish(c, "registered", 200, "registered")
            else:
                c.auth_fail = 1
                self.sip_send(self.simple_resp(msg, 403), addr, c)
                self.finish(c, "rejected", 403, "bad credentials")
            return
        nonce = secrets.token_hex(8)
        self.nonces.add(nonce)
        h = []
        for i, v in enumerate(msg.hs("via")):
            h.append(("Via", self._via_fix(v, addr) if i == 0 else v))
        to = msg.h("to") + (";tag=" + new_tag() if ";tag=" not in msg.h("to") else "")
        h += [("From", msg.h("from")), ("To", to), ("Call-ID", msg.call_id), ("CSeq", msg.h("cseq")), ("User-Agent", UA),
              ("WWW-Authenticate", 'Digest realm="%s", nonce="%s", algorithm=MD5, qop="auth"' % (REALM, nonce))]
        self.sip_send(build_msg("SIP/2.0 401 Unauthorized", h), addr)

    def _guard(self, fn, call, *a):
        try:
            fn(call, *a)
        except Exception as e:
            import traceback
            log("call %d crashed: %r\n%s" % (call.id, e, traceback.format_exc()))
            self.finish(call, "error", 0, "internal error %r" % e)

    # ---- message builders
    def _via_fix(self, v, addr):
        if addr and ";rport" in v and ";rport=" not in v:
            v = v.replace(";rport", ";rport=%d;received=%s" % (addr[1], addr[0]), 1)
        return v

    def simple_resp(self, req, code, reason=None):
        h = []
        for i, v in enumerate(req.hs("via")):
            h.append(("Via", self._via_fix(v, req.addr) if i == 0 else v))
        h += [("From", req.h("from")), ("To", req.h("to")), ("Call-ID", req.call_id), ("CSeq", req.h("cseq")),
              ("User-Agent", UA)]
        return build_msg("SIP/2.0 %d %s" % (code, reason or REASONS.get(code, "Status")), h)

    def build_resp(self, call, req, code, reason=None, body="", extra=None, tagged=True, contact=True):
        h = []
        for i, v in enumerate(req.hs("via")):
            h.append(("Via", self._via_fix(v, req.addr) if i == 0 else v))
        to = req.h("to")
        if tagged and ";tag=" not in to:
            to += ";tag=" + call.local_tag
        h += [("From", req.h("from")), ("To", to), ("Call-ID", req.call_id), ("CSeq", req.h("cseq"))]
        if contact and 100 < code < 400:
            h.append(("Contact", "<sip:sipload@%s:%d>" % (self.adv_ip, self.sip_port)))
        h += [("Allow", "INVITE, ACK, CANCEL, BYE, OPTIONS"), ("User-Agent", UA)]
        for k, v in (extra or []):
            h.append((k, v))
        if body:
            h.append(("Content-Type", "application/sdp"))
        return build_msg("SIP/2.0 %d %s" % (code, reason or REASONS.get(code, "Status")), h, body)

    # ---- bookkeeping
    def finish(self, call, result, code=None, reason=None):
        if call.done:
            return
        call.done = True
        call.t_end = time.time()
        call.result = result
        if code is not None:
            call.code = code
        if reason is not None:
            call.reason = reason
        call.state = "ended"
        if call.rtp is not None:
            call.snapshot_stats()
            call.rec = bytes(call.rtp.rec)
            call.rec_pt = call.rtp.rec_pt
            call.rec_tx = bytes(call.rtp.rec_tx)
            call.tx_pt = call.rtp.fkey if call.rtp.fkey is not None else call.rtp.tx_pt
            call.rec_off = call_rec_offset(call.rtp)
            self.rtp.close(call.rtp)
        with self.lock:
            self.calls.pop(call.call_id, None)
            self.history.append(call)
            if (call.rec and call.answered and call.cid is None and call.peer_sipload and (self.audio.kind == "tonetest" or call.akind in ("tone", "echo")) and self.tone_budget > 0):
                self.tone_budget -= 1
                self.aq.put(call)
            self.results[result] += 1
            if call.code:
                self.codes[call.code] += 1
            if len(self.history) > 300:               # keep recordings only for the newest 300 calls
                self.history[-301].rec = b""
                self.history[-301].rec_tx = b""

    def _tone_worker(self):
        while True:
            call = self.aq.get()
            try:
                self.analyze_call(call)
            except Exception as e:
                call.tone = {"error": "analysis failed: %r" % e, "score": None}

    def analyze_call(self, call):
        rec = bytes(call.rtp.rec) if (call.rtp is not None and not call.done) else call.rec
        pt = (call.rtp.rec_pt if (call.rtp is not None and not call.done) else call.rec_pt) or 0
        if not rec:
            call.tone = {"error": "no audio was received on this call", "score": None}
        else:
            call.tone = analyze_tones(decode_pcm(rec, pt))
        return call.tone

    def _sampler(self):
        while not self.stopping:
            time.sleep(1.0)
            with self.lock:
                act = len(self.calls)
                up = sum(1 for c in self.calls.values() if c.talk_t0 and not c.done)
                self.peak = max(self.peak, act)
                done = len(self.history)
                fail = sum(v for k, v in self.results.items() if k not in ("completed",))
            self.series.append((round(time.time(), 1), act, up, done, fail))

    # ---- dial plan
    def match_plan(self, number):
        if not self.cfg.get("dialplan_on", True):
            return None
        best = None
        for r in self.cfg.get("dialplan") or []:
            pf = str(r.get("prefix", ""))
            if pf and str(number).startswith(pf) and (best is None or len(pf) > len(best["prefix"])):
                best = r
        return best

    def echo_greeting(self, pt):
        """20 ms frames of audio/echo-test.wav (played before the echo starts), or None when the file is not there."""
        f = os.path.join(self.audio_dir, "echo-test.wav")
        try:
            mt = os.path.getmtime(f)
        except OSError:
            return None
        c = getattr(self, "_greet", None)
        if c is None or c[0] != (f, mt):
            try:
                self._greet = c = ((f, mt), Audio(f))
            except Exception as e:
                log("echo-test.wav could not be read:", repr(e))
                self._greet = c = ((f, mt), None)
        return list(c[1].frames[pt]) if c[1] is not None else None

    def _greeting_then_echo(self, call, st):
        while st.script and not call.done and not self.stopping:
            time.sleep(0.02)
        time.sleep(0.1)
        st.script_mode = False
        st.echo = True

    def audio_for(self, kind):
        if kind == "tone":
            if not hasattr(self, "_a_tone"):
                self._a_tone = Audio("__tonetest__")
            return self._a_tone
        if kind == "speech":
            if not hasattr(self, "_a_speech"):
                f = os.path.join(self.audio_dir, "test-speech.wav")
                self._a_speech = Audio(f) if os.path.exists(f) else Audio()
            return self._a_speech
        return self.audio

    # ---- UAS (carrier role)
    def pick_action(self):
        mix = self.cfg["mix"]
        tot = sum(max(0, v) for v in mix.values())
        if tot <= 0:
            return "answer"
        r = random.uniform(0, tot)
        for k, v in mix.items():
            r -= max(0, v)
            if r <= 0:
                return k
        return "answer"

    def uas_run(self, call, inv):
        cfg = self.cfg
        addr = inv.addr
        call.peer = "%s:%d" % addr
        call.remote_addr = addr
        m = re.search(r"sip:([^@;>]+)@", inv.uri)
        call.number = m.group(1) if m else inv.user("to")
        call.caller = inv.user("from")
        call.peer_sipload = "sipload" in inv.h("user-agent").lower()
        try:
            call.callerinfo = parse_caller_info(inv)
        except Exception as e:
            log("caller info:", repr(e))
        call.t_invite = call.t0
        call.state = "incoming"
        cur = {"inv": inv, "last": None}

        def reply(code, body="", extra=None, tagged=True, reason=None, req=None, contact=True):
            data = self.build_resp(call, req or cur["inv"], code, reason, body, extra, tagged, contact)
            if req is None:
                cur["last"] = data
            self.sip_send(data, addr, call)
            return data

        def pump(secs):
            """Wait up to secs.  Returns 'cancel', 'bye' or None; absorbs retransmits and OPTIONS."""
            end = time.time() + secs
            while True:
                rem = end - time.time()
                if rem <= 0:
                    return None
                msg = call.wait(min(rem, 0.2))
                if msg is None or not msg.is_request:
                    continue
                mt = msg.method
                if mt == "CANCEL":
                    reply(200, req=msg, tagged=False, contact=False)
                    reply(487)
                    return "cancel"
                if mt == "BYE":
                    reply(200, req=msg, contact=False)
                    return "bye"
                if mt == "INVITE" and msg.cseq == cur["inv"].cseq and cur["last"]:
                    self.sip_send(cur["last"], addr, call, retx=True)
                elif mt == "OPTIONS":
                    reply(200, req=msg, contact=False)
                elif mt == "ACK":
                    return "ack"

        # --- decide what to do
        action = self.pick_action()
        plan = self.match_plan(call.number)
        if plan:
            action = plan.get("action", "answer")
        call.action = plan["name"] if plan else action
        P = lambda k: plan[k] if (plan and k in plan) else cfg[k]
        if action == "timeout":
            call.state = "ignoring"
            pump(40)
            return self.finish(call, "ignored", 0, "no reply sent (simulated dead server)")

        # --- authentication (to test the gateway auth settings configured in Yeti)
        if cfg["auth_user"]:
            ok = False
            for attempt in range(3):
                a = cur["inv"].h("authorization")
                good = bool(a) and digest_check(a, "INVITE", cfg["auth_pass"], REALM, self.nonces) \
                    and parse_challenge(a).get("username") == cfg["auth_user"]
                if good:
                    ok = True
                    break
                if a:
                    call.auth_fail += 1
                if attempt == 2 or (a and call.auth_fail >= 2):
                    reply(403, contact=False)
                    break
                nonce = secrets.token_hex(8)
                self.nonces.add(nonce)
                reply(401, extra=[("WWW-Authenticate", 'Digest realm="%s", nonce="%s", algorithm=MD5, qop="auth"' % (REALM, nonce))], contact=False)
                nxt = None
                end = time.time() + 6
                while time.time() < end and nxt is None:
                    mm = call.wait(0.3)
                    if mm is not None and mm.is_request and mm.method == "INVITE" and mm.cseq[0] > cur["inv"].cseq[0]:
                        nxt = mm
                if nxt is None:
                    return self.finish(call, "failed", 401, "caller gave up after auth challenge")
                cur["inv"] = nxt
            if not ok:
                pump(2)
                return self.finish(call, "rejected", 403, "authentication failed")
        inv = cur["inv"]

        reply(100, tagged=False, contact=False)

        # --- plain rejections
        if action in REPLY:
            code = REPLY[action]
            extra = [("Contact", "<sip:redirected@192.0.2.10>")] if action == "redirect" else None
            call.state = "rejecting"
            reply(code, extra=extra, contact=(action != "redirect"))
            end = time.time() + 6
            iv, nextsend = 0.5, time.time() + 0.5
            while time.time() < end:
                r = pump(0.2)
                if r == "ack":
                    break
                if time.time() >= nextsend:
                    self.sip_send(cur["last"], addr, call, retx=True)
                    iv = min(iv * 2, 4)
                    nextsend = time.time() + iv
            return self.finish(call, "rejected", code, REASONS.get(code, ""))

        # --- media negotiation
        offer = parse_sdp(inv.body)
        pt, cname, onames = None, None, {}
        if offer:
            onames = sdp_codecs(inv.body)
            for p in offer[2]:
                nm = onames.get(p) or PT_CODEC.get(p)
                if nm in CODEC_PT and nm in [c.upper() for c in P("codecs")]:
                    pt, cname = p, nm
                    break
        if offer is None or pt is None:
            reply(488, contact=False)
            pump(3)
            return self.finish(call, "rejected", 488, "no common codec" if offer else "no SDP offer")

        akind = plan.get("audio", "default") if plan else "default"
        call.akind = akind
        st_dt = onames and [k for k, v in onames.items() if v == "TELEPHONE-EVENT"]
        st = self.rtp.open(self.audio_for(akind), self.rec_seconds)
        call.rtp = st
        st.lenient = not call.peer_sipload
        st.tx_pt = pt
        st.fkey = CODEC_PT[cname]
        if st_dt:
            st.dtmf_pt = st_dt[0]
        st.remote = (offer[0], offer[1])
        st.drop_pct = float(P("loss_pct"))
        greet = None
        if akind == "echo":
            st.echo_delay = float(plan.get("echo_ms", 0)) / 1000.0
            st.echo = True
            if cname in ("PCMU", "PCMA"):
                greet = self.echo_greeting(pt)
            if greet:                                     # play echo-test.wav first, echo afterwards
                st.echo = False
                st.script_mode = True
        if akind == "readback" and cname in ("PCMU", "PCMA"):
            st.script_mode = True
        mode = P("rtp_mode")
        adv_ip, adv_port = self.adv_ip, st.port
        if mode == "private_ip":
            adv_ip = "192.0.2.1"
        elif mode == "blackhole":
            adv_port = st.port + 1000 if st.port + 1000 < 65000 else st.port - 1000
        sdp = build_sdp(adv_ip, adv_port, [pt], names={pt: cname})

        call.state = "ringing"
        delay = random.uniform(cfg["delay_min_ms"], max(cfg["delay_min_ms"], cfg["delay_max_ms"])) / 1000.0 + cfg["ring_ms"] / 1000.0
        if plan and "delay_ms" in plan:
            delay = float(plan["delay_ms"]) / 1000.0
        if cfg["early_media"] and action == "answer":
            reply(183, body=sdp)
            st.sending = mode != "none"
        elif cfg["ring_ms"] > 0 or delay > 0:
            reply(180)
        if action == "noanswer":
            r = pump(60)
            if r != "cancel":
                reply(480, contact=False)
                pump(3)
                self.finish(call, "failed", 480, "rang out, never answered")
            else:
                self.finish(call, "cancelled", 487, "caller cancelled")
            return
        r = pump(delay)
        if r == "cancel":
            return self.finish(call, "cancelled", 487, "caller cancelled")

        # --- answer, then keep resending the 200 until the ACK arrives
        call.t_answer = time.time()
        ok200 = reply(200, body=sdp)
        got_ack, iv, t_end = False, 0.5, time.time() + 32
        nxt = time.time() + iv
        while time.time() < t_end and not got_ack:
            r = pump(max(0.05, nxt - time.time()))
            if r == "ack":
                got_ack = True
            elif r == "bye":
                return self.finish(call, "dropped", 200, "caller hung up before ACK")
            elif r == "cancel":
                pass
            elif time.time() >= nxt:
                self.sip_send(ok200, addr, call, retx=True)
                iv = min(iv * 2, 4)
                nxt = time.time() + iv
        if not got_ack:
            call.hungup_by = "us (no ACK)"
            self.uas_bye(call, cur, addr, inv)
            return self.finish(call, "no_ack", 200, "no ACK for our 200 OK within 32 s")

        call.answered = True
        call.state = "up"
        call.talk_t0 = time.time()
        call.code = 200
        st.sending = mode != "none"
        hang = float(P("hangup_after"))
        if greet:
            st.script.extend(greet)
            threading.Thread(target=self._greeting_then_echo, args=(call, st), daemon=True, name="echo-greeting").start()
        if akind == "readback" and st.script_mode:
            threading.Thread(target=readback_run, args=(self, call, st, pt), daemon=True, name="readback").start()
        if akind == "cid":
            threading.Thread(target=cid_receiver, args=(self, call, st, plan), daemon=True, name="cid-rx").start()
        while not self.stopping:
            if call.end_after and time.time() >= call.end_after and not hang:
                hang = 0.001
            if call.cid_end and time.time() - call.cid_end > 8.0 and not hang:
                hang = 0.001                                  # message done: hang up shortly after (the panel normally does it first)
            r = pump(0.25)
            if r == "bye":
                call.hungup_by = "caller"
                return self.finish(call, "completed", 200, "caller hung up")
            if hang and time.time() - call.talk_t0 >= hang:
                call.hungup_by = "us"
                self.uas_bye(call, cur, addr, inv)
                return self.finish(call, "completed", 200, ("readback finished" if call.end_after else "we hung up after %ds" % hang))
            if time.time() - call.talk_t0 > 3600:
                break
        call.hungup_by = "us (shutdown)"
        self.uas_bye(call, cur, addr, inv)
        self.finish(call, "aborted", 200, "tester stopped")

    def uas_bye(self, call, cur, addr, inv):
        to_hdr = inv.h("from")
        contact = re.search(r"<([^>]+)>", inv.h("contact"))
        ruri = contact.group(1) if contact else "sip:%s@%s:%d" % (call.number, addr[0], addr[1])
        branch = new_branch()
        h = [("Via", "SIP/2.0/UDP %s:%d;branch=%s;rport" % (self.adv_ip, self.sip_port, branch)), ("Max-Forwards", "70"),
             ("From", inv.h("to") + (";tag=" + call.local_tag if ";tag=" not in inv.h("to") else "")), ("To", to_hdr),
             ("Call-ID", call.call_id), ("CSeq", "%d BYE" % (random.randint(100, 900))), ("User-Agent", UA)]
        data = build_msg("BYE %s SIP/2.0" % ruri, h)
        iv = 0.5
        for _ in range(6):
            self.sip_send(data, addr, call)
            end = time.time() + iv
            while time.time() < end:
                mm = call.wait(0.1)
                if mm is not None and not mm.is_request and mm.cseq[1] == "BYE":
                    return
            iv = min(iv * 2, 4)


# ------------------------------------------------------------------ customer role: calls, faults, runs
FAULTS = {
    "bad_password":   ("Wrong password", "401/403 after the digest retry; shows up in the SBC auth log and any auto-ban tool"),
    "bad_user":       ("Unknown username", "401/403 rejection; this is what a scanner looks like"),
    "no_auth":        ("Ignore the auth challenge", "call fails at the first 401/407"),
    "codec_mismatch": ("Offer a codec nobody supports (X-SIPLOAD)", "488 Not Acceptable (or Yeti transcoding if allowed)"),
    "private_sdp":    ("Private IP in SDP (NAT mistake)", "call connects but you hear nothing, or Yeti latches on"),
    "wrong_rtp_port": ("Advertise the wrong RTP port", "call connects, caller receives no audio"),
    "no_media":       ("Send no audio", "call connects, the far end receives no audio"),
    "no_ack":         ("Never send ACK", "far end resends its 200 OK; if you hold the call longer than 32 s it gives up with a BYE"),
    "no_bye":         ("Never hang up", "call stays up until the far end or the session timer ends it"),
    "early_cancel":   ("CANCEL while ringing", "487 Request Terminated"),
    "bad_callee":     ("Dial a number that has no route", "404 / 503 from Yeti routing"),
    "short_call":     ("Hang up after 1-2 seconds", "completed, but counted by Yeti short-call limits"),
    "loss_5":         ("Drop 5% of our audio packets", "far end reports about 5% loss, MOS drops"),
    "loss_20":        ("Drop 20% of our audio packets", "far end reports about 20% loss, MOS poor"),
}
RUN_DEFAULTS = {
    "kind": "batch",                 # batch | steps | auth
    "target": "", "from_user": "sipload", "from_domain": "", "display": "sipload test",
    "auth_user": "", "auth_pass": "", "callee_start": "9990001", "callee_end": "9990100", "callee_count": 100, "profiles": "", "list_csv": "", "dtmf": "", "dtmf_after": 2.0, "cid": "", "cid_fault": "", "cid_count": 1,
    "calls": 10, "cps": 2.0, "hold_min": 20, "hold_max": 20,
    "steps": [[10, 60], [25, 60], [50, 60], [100, 60]],      # [concurrent calls, seconds]
    "codecs": ["PCMU"], "faults": [], "fault_pct": 0, "ring_timeout": 60,
    "auth_method": "REGISTER", "auth_count": 20, "auth_per_min": 30, "auth_users": "random",
}


class RunState:
    def __init__(self, params):
        self.id = secrets.token_hex(3)
        self.params = params
        self.state = "running"
        self.started = time.time()
        self.ended = None
        self.launched = 0
        self.stop = threading.Event()
        self.first_call_id = None
        self.note = ""

    def to_dict(self):
        return {"id": self.id, "state": self.state, "kind": self.params.get("kind"), "started": self.started,
                "ended": self.ended, "launched": self.launched, "params": self.params, "note": self.note}


def parse_hostport(s, default_port=5060):
    s = s.strip()
    host, _, port = s.partition(":")
    return host, int(port) if port.isdigit() else default_port


def _method_uac(node):
    # bound onto Node below
    pass


def uac_invite_msg(node, call, p, number, cseq, branch, sdp, auth_hdr=None):
    host, port = p["_target"]
    ruri = "sip:%s@%s:%d" % (number, host, port)
    dom = p["from_domain"] or host
    h = [("Via", "SIP/2.0/UDP %s:%d;branch=%s;rport" % (node.adv_ip, node.sip_port, branch)), ("Max-Forwards", "70"),
         ("From", '"%s" <sip:%s@%s>;tag=%s' % (p["display"], call.caller or p["from_user"], dom, call.local_tag)),
         ("To", "<sip:%s@%s>" % (number, host)), ("Call-ID", call.call_id), ("CSeq", "%d INVITE" % cseq),
         ("Contact", "<sip:%s@%s:%d>" % (call.caller or p["from_user"], node.adv_ip, node.sip_port)),
         ("Allow", "INVITE, ACK, CANCEL, BYE, OPTIONS"), ("User-Agent", UA), ("Content-Type", "application/sdp")]
    if auth_hdr:
        h.append(auth_hdr)
    return build_msg("INVITE %s SIP/2.0" % ruri, h, sdp), ruri


def uac_run(node, call, p):
    """One outgoing call from INVITE to BYE."""
    fault = call.fault
    host, port = p["_target"]
    target = (host, port)
    number = call.number
    call.peer = "%s:%d" % target
    call.remote_addr = target
    st = node.rtp.open(node.audio, node.rec_seconds)
    call.rtp = st
    cnames = [c.upper() for c in p["codecs"] if c.upper() in CODEC_PT] or ["PCMU"]
    pts = [CODEC_PT[c] for c in cnames]
    st.tx_pt = pts[0]
    st.fkey = pts[0]
    adv_ip, adv_port = node.adv_ip, st.port
    if fault == "private_sdp":
        adv_ip = "192.0.2.1"
    elif fault == "wrong_rtp_port":
        adv_port = st.port + 1000 if st.port + 1000 < 65000 else st.port - 1000
    if fault == "codec_mismatch":
        sdp = build_sdp(adv_ip, adv_port, [], dtmf=True).replace("RTP/AVP 101", "RTP/AVP 120 101").replace(
            "a=rtpmap:101", "a=rtpmap:120 X-SIPLOAD/8000\r\na=rtpmap:101", 1)
    else:
        sdp = build_sdp(adv_ip, adv_port, pts)
    if fault == "loss_5":
        st.drop_pct = 5.0
    elif fault == "loss_20":
        st.drop_pct = 20.0
    user, pw = (call.auth_user, call.auth_pass) if call.auth_user else (p["auth_user"], p["auth_pass"])
    if fault == "bad_password":
        pw = (pw or "x") + "-wrong"
    elif fault == "bad_user":
        user = "zz" + secrets.token_hex(3)

    cseq, branch = 1, new_branch()
    data, ruri = uac_invite_msg(node, call, p, number, cseq, branch, sdp)
    call.t_invite = time.time()
    call.state = "calling"
    node.sip_send(data, target, call)
    iv, nxt, t_start = 0.5, time.time() + 0.5, time.time()
    got_resp = got_18x = False
    cancel_at = None
    sent_auth = 0
    to_hdr = ""
    remote_contact = None
    ring_timeout = float(p["ring_timeout"])

    def send_ack_non2xx(resp):
        h = [("Via", "SIP/2.0/UDP %s:%d;branch=%s;rport" % (node.adv_ip, node.sip_port, branch)), ("Max-Forwards", "70"),
             ("From", resp.h("from")), ("To", resp.h("to")), ("Call-ID", call.call_id),
             ("CSeq", "%d ACK" % resp.cseq[0]), ("User-Agent", UA)]
        node.sip_send(build_msg("ACK %s SIP/2.0" % ruri, h), target, call)

    final = None
    while final is None:
        if node.stopping or (call.dir == "out" and getattr(call, "abort", False) and not got_18x and not got_resp):
            return node.finish(call, "aborted", 0, "tester stopped")
        now = time.time()
        if fault == "early_cancel" and cancel_at is None and (got_18x or now - t_start > 1.0):
            cancel_at = now + 0.1
        if cancel_at and now >= cancel_at:
            h = [("Via", "SIP/2.0/UDP %s:%d;branch=%s;rport" % (node.adv_ip, node.sip_port, branch)), ("Max-Forwards", "70"),
                 ("From", '"%s" <sip:%s@%s>;tag=%s' % (p["display"], call.caller or p["from_user"], p["from_domain"] or host, call.local_tag)),
                 ("To", "<sip:%s@%s>" % (number, host)), ("Call-ID", call.call_id), ("CSeq", "%d CANCEL" % cseq),
                 ("User-Agent", UA)]
            node.sip_send(build_msg("CANCEL %s SIP/2.0" % ruri, h), target, call)
            cancel_at = None
            call.state = "cancelling"
            end = time.time() + 5
            while time.time() < end:
                m = call.wait(0.2)
                if m is not None and not m.is_request and m.cseq[1] == "INVITE" and m.code >= 200:
                    send_ack_non2xx(m)
                    return node.finish(call, "cancelled", m.code, m.start.split(" ", 2)[2] if m.code else "")
            return node.finish(call, "failed", 0, "no 487 after CANCEL")
        if not got_resp and now >= nxt:
            if now - t_start >= 32:
                return node.finish(call, "timeout", 408, "no response within 32 s")
            node.sip_send(data, target, call, retx=True)
            iv = min(iv * 2, 4)
            nxt = now + iv
        if got_18x and now - t_start > ring_timeout:
            h = [("Via", "SIP/2.0/UDP %s:%d;branch=%s;rport" % (node.adv_ip, node.sip_port, branch)), ("Max-Forwards", "70"),
                 ("From", '"%s" <sip:%s@%s>;tag=%s' % (p["display"], call.caller or p["from_user"], p["from_domain"] or host, call.local_tag)),
                 ("To", "<sip:%s@%s>" % (number, host)), ("Call-ID", call.call_id), ("CSeq", "%d CANCEL" % cseq)]
            node.sip_send(build_msg("CANCEL %s SIP/2.0" % ruri, h), target, call)
            ring_timeout = 10 ** 9
            continue
        m = call.wait(0.1)
        if m is None or m.is_request:
            if m is not None and m.method == "OPTIONS":
                node.sip_send(node.simple_resp(m, 200), target, call)
            continue
        if m.cseq[1] != "INVITE":
            continue
        code = m.code
        call.code, call.reason = code, (m.start.split(" ", 2) + ["", "", ""])[2]
        if code == 100:
            got_resp = True
        elif 100 < code < 200:
            got_resp = True
            if not got_18x:
                got_18x = True
                call.t_18x = time.time()
                call.state = "ringing"
            if m.body:
                a = parse_sdp(m.body)
                if a:
                    st.remote = (a[0], a[1])
        elif code in (401, 407) and sent_auth < 2:
            send_ack_non2xx(m)
            hdr_name = "WWW-Authenticate" if code == 401 else "Proxy-Authenticate"
            ch = m.h(hdr_name)
            if fault == "no_auth" or not ch or not user:
                call.auth_fail += 1
                return node.finish(call, "rejected", code, "challenge not answered" if ch else "no credentials")
            sent_auth += 1
            cseq += 1
            branch = new_branch()
            val = digest_header(parse_challenge(ch), user, pw, "INVITE", ruri)
            data, ruri = uac_invite_msg(node, call, p, number, cseq, branch, sdp,
                                        ("Authorization" if code == 401 else "Proxy-Authorization", val))
            call.state = "authenticating"
            node.sip_send(data, target, call)
            got_resp, iv, nxt, t_start = False, 0.5, time.time() + 0.5, time.time()
        elif code >= 200:
            final = m

    code = final.code
    if code != 200:
        send_ack_non2xx(final)
        if code in (401, 407):
            call.auth_fail += 1
        return node.finish(call, "rejected" if code != 487 else "cancelled", code, call.reason)

    # --- 200 OK: ACK, media, hold
    call.t_answer = time.time()
    call.answered = True
    call.state = "up"
    call.talk_t0 = time.time()
    to_hdr = final.h("to")
    mc = re.search(r"<([^>]+)>", final.h("contact"))
    remote_contact = mc.group(1) if mc else ruri
    ans = parse_sdp(final.body)
    if ans:
        st.remote = (ans[0], ans[1])
        an = sdp_codecs(final.body)
        for k, v in an.items():
            if v == "TELEPHONE-EVENT":
                st.dtmf_pt = k
        for ap in ans[2]:                                  # the codec the far end chose from our list
            nm = an.get(ap) or PT_CODEC.get(ap)
            if nm in cnames:
                st.tx_pt, st.fkey = ap, CODEC_PT[nm]
                break
    ack_branch = new_branch()

    def send_ack():
        h = [("Via", "SIP/2.0/UDP %s:%d;branch=%s;rport" % (node.adv_ip, node.sip_port, ack_branch)), ("Max-Forwards", "70"),
             ("From", final.h("from")), ("To", to_hdr), ("Call-ID", call.call_id), ("CSeq", "%d ACK" % final.cseq[0]),
             ("User-Agent", UA)]
        node.sip_send(build_msg("ACK %s SIP/2.0" % remote_contact, h), target, call)

    if fault != "no_ack":
        send_ack()
    st.sending = fault != "no_media" and ans is not None
    if p.get("dtmf") and ans is not None and fault != "no_media":
        if ans:
            for k, v in sdp_codecs(final.body).items():
                if v == "TELEPHONE-EVENT":
                    st.dtmf_pt = k
        st.dtmf_digits = [d for d in str(p["dtmf"]).upper() if d in DTMF_EVENTS]
        st.dtmf_at = time.time() + max(0.0, float(p.get("dtmf_after", 2.0)))
    hold = random.uniform(float(p["hold_min"]), max(float(p["hold_min"]), float(p["hold_max"])))
    if fault == "short_call":
        hold = random.uniform(1.0, 2.0)
    if p.get("_cid") and ans is not None and fault != "no_media":
        hold = 90.0                                       # the panel session ends the call itself
        threading.Thread(target=cid_panel, args=(node, call, st, p["_cid"], p.get("cid_fault", ""), int(p.get("cid_count", 1))), daemon=True, name="cid-panel").start()
    end_at = time.time() + hold
    while True:
        if node.stopping or getattr(call, "abort", False):
            call.hungup_by = "us (stopped)"
            break
        if time.time() >= end_at or (call.cid_evt.is_set() and time.time() - (call.cid_end or 0) > 0.4):
            call.hungup_by = "us"
            break
        m = call.wait(0.2)
        if m is None:
            continue
        if m.is_request:
            if m.method == "BYE":
                node.sip_send(node.simple_resp(m, 200), target, call)
                call.hungup_by = "far end"
                early = end_at - time.time()
                return node.finish(call, "dropped" if early > 1.5 else "completed", 200,
                                   "far end hung up %.0f s early" % early if early > 1.5 else "far end hung up")
            if m.method == "OPTIONS":
                node.sip_send(node.simple_resp(m, 200), target, call)
            elif m.method == "INVITE":
                node.sip_send(node.build_resp(call, m, 200, body=sdp), m.addr, call)
        elif m.cseq[1] == "INVITE" and m.code == 200:
            if fault != "no_ack":
                send_ack()                              # the far end resent its 200: our ACK was lost

    if fault == "no_bye" and not node.stopping and not getattr(call, "abort", False):
        call.hungup_by = "nobody (leaked)"
        call.state = "leaked"
        while not node.stopping and not getattr(call, "abort", False):
            m = call.wait(0.5)
            if m is not None and m.is_request and m.method == "BYE":
                node.sip_send(node.simple_resp(m, 200), target, call)
                call.hungup_by = "far end"
                return node.finish(call, "completed", 200, "far end ended the call (session timer?)")
        call.hungup_by = "us (tester stopped)"

    # --- hang up
    call.state = "hanging up"
    branch_b = new_branch()
    h = [("Via", "SIP/2.0/UDP %s:%d;branch=%s;rport" % (node.adv_ip, node.sip_port, branch_b)), ("Max-Forwards", "70"),
         ("From", final.h("from")), ("To", to_hdr), ("Call-ID", call.call_id), ("CSeq", "%d BYE" % (cseq + 1)),
         ("User-Agent", UA)]
    bye = build_msg("BYE %s SIP/2.0" % remote_contact, h)
    iv = 0.5
    ok = False
    for _ in range(6):
        node.sip_send(bye, target, call, retx=_ > 0)
        end = time.time() + iv
        while time.time() < end:
            m = call.wait(0.1)
            if m is not None and not m.is_request and m.cseq[1] == "BYE":
                ok = True
                break
            if m is not None and m.is_request and m.method == "BYE":
                node.sip_send(node.simple_resp(m, 200), target, call)
                ok = True
                break
        if ok:
            break
        iv = min(iv * 2, 4)
    time.sleep(0.15)
    if call.stats is None and call.rtp is not None:
        call.snapshot_stats()
    node.finish(call, "completed" if ok else "completed_no_bye_reply", 200, "hung up" if ok else "BYE not answered")


def uac_register(node, call, p):
    """One REGISTER attempt (used by the authentication-failure test)."""
    host, port = p["_target"]
    target = (host, port)
    call.peer = "%s:%d" % target
    user = call.number
    pw = p["auth_pass"] or "wrong"
    if call.auth_user:                                  # account taken from the number list: real credentials
        user, pw = call.auth_user, call.auth_pass
    elif p["auth_users"] == "random":
        user = "zz" + secrets.token_hex(3)
    else:
        user = p["auth_user"] or user
        pw = pw + "-wrong"
    dom = p["from_domain"] or host
    ruri = "sip:%s" % host
    cseq = 1
    call.number = user
    for attempt in range(2):
        h = [("Via", "SIP/2.0/UDP %s:%d;branch=%s;rport" % (node.adv_ip, node.sip_port, new_branch())), ("Max-Forwards", "70"),
             ("From", "<sip:%s@%s>;tag=%s" % (user, dom, call.local_tag)), ("To", "<sip:%s@%s>" % (user, dom)),
             ("Call-ID", call.call_id), ("CSeq", "%d REGISTER" % cseq), ("Contact", "<sip:%s@%s:%d>" % (user, node.adv_ip, node.sip_port)),
             ("Expires", "60"), ("User-Agent", UA)]
        if attempt:
            h.append(("Authorization", digest_header(ch, user, pw, "REGISTER", ruri)))
        data = build_msg("REGISTER %s SIP/2.0" % ruri, h)
        call.t_invite = time.time()
        node.sip_send(data, target, call)
        resp = None
        end = time.time() + 6
        nxt, iv = time.time() + 0.5, 0.5
        while time.time() < end and resp is None:
            m = call.wait(0.1)
            if m is not None and not m.is_request and m.cseq[1] == "REGISTER" and m.code >= 200:
                resp = m
            elif time.time() >= nxt:
                node.sip_send(data, target, call, retx=True)
                iv = min(iv * 2, 4)
                nxt = time.time() + iv
        if resp is None:
            return node.finish(call, "timeout", 408, "no reply")
        call.t_answer = time.time()
        call.code, call.reason = resp.code, (resp.start.split(" ", 2) + ["", "", ""])[2]
        if resp.code in (401, 407) and attempt == 0:
            ch = parse_challenge(resp.h("www-authenticate" if resp.code == 401 else "proxy-authenticate"))
            if not ch:
                return node.finish(call, "rejected", resp.code, "challenge without parameters")
            cseq += 1
            continue
        if resp.code == 200:
            return node.finish(call, "accepted", 200, "registration ACCEPTED (unexpected for a bad login)")
        call.auth_fail += 1
        return node.finish(call, "rejected", resp.code, call.reason)
    node.finish(call, "rejected", call.code, call.reason)


def node_new_uac_call(self, run, idx, p, method="INVITE"):
    cid = "%s@%s" % (secrets.token_hex(8), self.adv_ip)
    c = Call(self, "out", cid, method)
    base = p["callee_start"]
    n = int(base) + (idx % max(1, int(p["callee_count"])))
    c.number = str(n).zfill(len(base))
    prof = p.get("_profiles")
    if prof:
        pf = random.choices([x[0] for x in prof], [x[1] for x in prof])[0]
        c.number = pf + str(1 + idx % 100).zfill(max(1, len(base) - len(pf)))
    c.caller = p["from_user"]
    lst = p.get("_list")
    if lst:
        row = lst[idx % len(lst)]
        c.number, c.caller, c.auth_user, c.auth_pass = row[0], (row[1] or p["from_user"]), row[2], row[3]
    plan = self.match_plan(c.number)
    if p.get("dtmf") and plan and plan.get("audio") == "echo":
        c.dtmf_expect = str(p["dtmf"])
    if plan and (plan.get("action", "answer") != "answer" or plan.get("rtp_mode") == "none" or plan.get("loss_pct")):
        c.action = plan["name"]
        c.fault = "plan: " + plan["name"]
        c.expect = plan.get("expect", "")
    if p.get("_cid"):
        c.akind = "cid"
        if p.get("cid_fault") and not c.fault:
            c.fault = "cid: " + ("wrong check digit" if p["cid_fault"] == "badsum" else "message one digit short")
            c.expect = "receiver rejects the message: no kiss-off, panel gives up after 4 tries"
    if plan and plan.get("fail") and not c.fault:
        c.fault = "plan: " + plan["name"]
        c.expect = plan.get("expect", "")
    faults = p.get("faults") or []
    if faults and not p.get("_cid") and random.random() * 100.0 < float(p.get("fault_pct", 0)):
        c.fault = random.choice(faults)
        c.expect = FAULTS.get(c.fault, ("", ""))[1]
    with self.lock:
        self.calls[cid] = c
    fn = uac_run if method == "INVITE" else uac_register
    threading.Thread(target=self._guard, args=(lambda call: fn(self, call, p), c), daemon=True).start()
    return c


def node_start_run(self, params):
    if self.run is not None and self.run.state == "running":
        raise ValueError("a test is already running; stop it first")
    p = json.loads(json.dumps(RUN_DEFAULTS))
    p.update({k: v for k, v in params.items() if k in RUN_DEFAULTS})
    p["_target"] = parse_hostport(p["target"], 5060)
    if not p["_target"][0]:
        raise ValueError("target is empty")
    p["callee_start"] = str(p["callee_start"]).strip()
    if not p["callee_start"].isdigit():
        raise ValueError("dial numbers 'from' must be digits, for example 9990001")
    end = str(p.get("callee_end") or "").strip()
    if end:
        if not end.isdigit() or int(end) < int(p["callee_start"]):
            raise ValueError("dial numbers 'to' must be digits and not lower than 'from'")
        p["callee_count"] = min(int(end) - int(p["callee_start"]) + 1, 100000)
    p["_list"] = None
    if str(p.get("list_csv") or "").strip():
        rows = []
        for ln in str(p["list_csv"]).splitlines():
            ln = ln.strip()
            if not ln or ln.startswith("#"):
                continue
            cells = [c.strip() for c in re.split(r"[,;\t]", ln)]
            if not rows and cells[0].lower() in ("number", "dial", "dialed", "to", "destination", "dialed number"):
                continue
            rows.append((cells[0], cells[1] if len(cells) > 1 else "", cells[2] if len(cells) > 2 else "", cells[3] if len(cells) > 3 else ""))
            if len(rows) >= 200000:
                break
        if not rows or not all(r[0] for r in rows):
            raise ValueError("number list: each line needs a number to dial (number[,calling number[,auth user,auth password]])")
        p["_list"] = rows
        p["list_csv"] = "(list of %d rows)" % len(rows)
    p["_cid"] = None
    if str(p.get("cid") or "").strip():
        p["_cid"] = cid_parse_param(p["cid"])
        p["cid"] = "%(acct)s %(event)s %(group)s %(zone)s" % p["_cid"]
        p["codecs"] = [c for c in p["codecs"] if c.upper() in ("PCMU", "PCMA")] or ["PCMU"]     # Contact ID needs G.711
        p["cid_count"] = max(1, min(int(p.get("cid_count") or 1), 5))
        if p.get("cid_fault") not in ("", "badsum", "short"):
            raise ValueError("Contact ID fault must be empty, badsum or short")
    plan0 = self.match_plan(p["callee_start"])
    if p["_cid"] is None and plan0 and plan0.get("audio") == "cid":      # dialing a Contact ID receiver without a message: send a periodic test
        p["_cid"] = cid_parse_param("")
        p["cid"] = "%(acct)s %(event)s %(group)s %(zone)s" % p["_cid"]
        p["codecs"] = [c for c in p["codecs"] if c.upper() in ("PCMU", "PCMA")] or ["PCMU"]
    p["dtmf"] = "".join(d for d in str(p.get("dtmf") or "").upper() if d in DTMF_EVENTS)
    p["_profiles"] = None
    if str(p.get("profiles") or "").strip():
        pr = []
        for part in str(p["profiles"]).split(","):
            k, _, v = part.strip().partition("=")
            if not k.strip().isdigit():
                raise ValueError("mix must look like 9990=80,9997=20")
            pr.append((k.strip(), max(0.0, float(v or 1))))
        if not pr or sum(x[1] for x in pr) <= 0:
            raise ValueError("mix needs at least one weight above 0")
        p["_profiles"] = pr
    p["calls"] = max(1, min(int(p["calls"]), 5000))
    p["cps"] = max(0.1, min(float(p["cps"]), 100.0))
    p["hold_min"] = max(0.0, float(p["hold_min"]))
    p["hold_max"] = max(p["hold_min"], float(p["hold_max"]))
    p["fault_pct"] = max(0.0, min(float(p["fault_pct"]), 100.0))
    p["faults"] = [f for f in p["faults"] if f in FAULTS]
    p["steps"] = [[max(1, min(int(a), 1000)), max(1, int(b))] for a, b in p["steps"]]
    if not str(p["callee_start"]).isdigit():
        raise ValueError("callee_start must be digits, for example 9990001")
    p["callee_start"] = str(p["callee_start"])
    self.adv_ip = self.args.advertise_ip or detect_ip(p["_target"][0])
    self.reset_history(keep_active=True)
    run = RunState({k: v for k, v in p.items() if not k.startswith("_")})
    self.run = run
    threading.Thread(target=self._run_thread, args=(run, p), daemon=True, name="run").start()
    return run


def node_run_thread(self, run, p):
    try:
        kind = p["kind"]
        if kind == "batch":
            interval = 1.0 / p["cps"]
            nxt = time.time()
            for i in range(p["calls"]):
                if run.stop.is_set() or self.stopping:
                    break
                while time.time() < nxt and not run.stop.is_set():
                    time.sleep(0.005)
                nxt += interval
                node_new_uac_call(self, run, i, p)
                run.launched += 1
        elif kind == "steps":
            i = 0
            for conc, secs in p["steps"]:
                run.note = "step: %d concurrent calls for %d s" % (conc, secs)
                end = time.time() + secs
                last_launch = 0.0
                while time.time() < end and not run.stop.is_set() and not self.stopping:
                    with self.lock:
                        active = sum(1 for c in self.calls.values() if c.method == "INVITE")
                    room = conc - active
                    budget = int(p["cps"] * 0.1 + 0.999)
                    for _ in range(max(0, min(room, budget))):
                        node_new_uac_call(self, run, i, p)
                        i += 1
                        run.launched += 1
                    time.sleep(0.1)
                if run.stop.is_set():
                    break
            run.note = "ending: waiting for calls to finish"
        elif kind == "auth":
            gap = 60.0 / max(0.1, float(p["auth_per_min"]))
            nxt = time.time()
            for i in range(int(p["auth_count"])):
                if run.stop.is_set() or self.stopping:
                    break
                while time.time() < nxt and not run.stop.is_set():
                    time.sleep(0.02)
                nxt += gap
                p2 = dict(p)
                p2["faults"] = []
                c = node_new_uac_call(self, run, i, p2, method="REGISTER")
                run.launched += 1
        # wait for the calls to finish (stop = hang everything up)
        while True:
            with self.lock:
                left = [c for c in self.calls.values() if c.dir == "out"]
            if not left:
                break
            if run.stop.is_set():
                for c in left:
                    c.abort = True
            time.sleep(0.2)
        run.state = "stopped" if run.stop.is_set() else "done"
    except Exception as e:
        import traceback
        log("run crashed:", repr(e), traceback.format_exc())
        run.state = "error"
        run.note = repr(e)
    run.ended = time.time()
    run.note = run.note if run.state == "error" else ""
    self.last_report_files = None
    try:
        if self.args.out:
            self.save_report(run)
    except Exception as e:
        log("could not save report:", repr(e))


def node_reset_history(self, keep_active=False):
    with self.lock:
        self.history.clear()
        self.codes.clear()
        self.results.clear()
        self.peak = len(self.calls) if keep_active else 0
        self.series.clear()
        self.rtp.max_lag_ms = 0.0
        self.rtp.late_ticks = 0
        self.rtp.ticks = 0
        self.sip_retx = 0
        self.tone_budget = self.tone_limit


Node.new_uac_call = node_new_uac_call
Node.start_run = node_start_run
Node._run_thread = node_run_thread
Node.reset_history = node_reset_history


# ------------------------------------------------------------------ summary and reports
def _fmt(v, unit="", nd=1):
    return "-" if v is None else ("%s%s" % (round(v, nd), unit))


def summarize(node):
    with node.lock:
        calls = list(node.history)
        active = list(node.calls.values())
        peak = node.peak
    inv = [c for c in calls if c.method == "INVITE"]
    reg = [c for c in calls if c.method == "REGISTER"]
    normal = [c for c in inv if not c.fault]
    faulty = [c for c in inv if c.fault]
    answered = [c for c in normal if c.answered]
    S = {"role": node.role, "generated": time.time(), "peak_concurrent": peak, "active_now": len(active),
         "calls_total": len(inv), "normal_calls": len(normal), "fault_calls": len(faulty),
         "answered": len(answered), "completed": sum(1 for c in normal if c.result == "completed"),
         "dropped": sum(1 for c in normal if c.result == "dropped"),
         "no_ack": sum(1 for c in normal if c.result == "no_ack"),
         "failed": sum(1 for c in normal if not c.answered)}
    S["asr_pct"] = round(100.0 * len(answered) / len(normal), 1) if normal else None
    pdd = [c.to_dict()["pdd_ms"] for c in answered]
    pdd = [x for x in pdd if x is not None]
    setup = [c.to_dict()["setup_ms"] for c in answered]
    setup = [x for x in setup if x is not None]
    S["pdd_avg"], S["pdd_p95"], S["pdd_max"] = rnd(avg(pdd), 0), pctl(pdd, 95), max(pdd) if pdd else None
    S["setup_avg"], S["setup_p95"] = rnd(avg(setup), 0), pctl(setup, 95)
    media = [c for c in answered if c.stats]
    loss = [c.stats["loss_pct"] for c in media if c.stats["rx_packets"] > 0]
    jit = [c.stats["jitter_ms"] for c in media if c.stats["rx_packets"] > 0]
    mos = [c.stats["mos"] for c in media if c.stats.get("mos")]
    S["no_audio"] = sum(1 for c in media if not c.stats["audio_ok"])
    tn = [c.tone for c in calls if c.tone and c.tone.get("score") is not None and "error" not in c.tone and not c.fault]
    rt = [c.stats["rtt_ms"] for c in calls if c.stats and c.stats.get("rtt_ms") is not None]
    S["rtt_calls"] = len(rt)
    if rt:
        S["rtt_avg"], S["rtt_max"] = rnd(avg(rt), 1), max(c.stats["rtt_max"] for c in calls if c.stats and c.stats.get("rtt_max") is not None)
        S["rtt_min"] = min(c.stats["rtt_min"] for c in calls if c.stats and c.stats.get("rtt_min") is not None)
    dt = [c for c in calls if c.dtmf_expect and c.stats]
    S["dtmf_calls"] = len(dt)
    S["dtmf_bad"] = sum(1 for c in dt if c.stats.get("dtmf", "") != c.dtmf_expect)
    cc = [c for c in inv if c.cid]
    S["cid_calls"] = len(cc)
    S["cid_ok"] = sum(1 for c in cc if c.cid.get("ok"))
    S["cid_bad"] = sum(1 for c in cc if bool(c.cid.get("ok")) == bool(c.fault)) if node.role == "customer" else 0     # a fault-injected call is meant to fail
    pan = [c.cid for c in cc if c.cid.get("role") == "panel" and c.cid.get("ok")]
    S["cid_tries_avg"] = rnd(avg([x["tries"] for x in pan]), 2) if pan else None
    S["cid_hs_avg"] = rnd(avg([x["hs_ms"] for x in pan if x.get("hs_ms") is not None]), 0) if pan else None
    S["cid_total_avg"] = rnd(avg([x["total_ms"] for x in pan if x.get("total_ms") is not None]), 0) if pan else None
    S["tone_calls"] = len(tn)
    S["tone_unmeasured"] = sum(1 for c in calls if c.tone and c.tone.get("error") and not c.fault)
    if tn:
        def _a(k):
            v = [t[k] for t in tn if t.get(k) is not None]
            return rnd(avg(v), 2) if v else None
        S["tone_avg"], S["tone_min"] = _a("score"), min(t["score"] for t in tn)
        S["tone_snr_avg"], S["tone_digits_pct"] = _a("snr_db"), _a("digits_pct")
        S["tone_dropout_ms"] = sum(t.get("dropout_ms", 0) for t in tn)
        S["tone_level_avg"], S["tone_freq_avg"] = _a("level_db"), _a("freq_hz")
    S["loss_avg"], S["loss_max"] = rnd(avg(loss), 2), max(loss) if loss else None
    S["jitter_avg"], S["jitter_p95"], S["jitter_max"] = rnd(avg(jit), 2), pctl(jit, 95), max(jit) if jit else None
    S["mos_avg"], S["mos_min"] = rnd(avg(mos), 2), min(mos) if mos else None
    S["tx_packets"] = sum(c.stats["tx_packets"] for c in calls if c.stats)
    S["rx_packets"] = sum(c.stats["rx_packets"] for c in calls if c.stats)
    S["exact_avg"] = rnd(avg([c.stats["exact_pct"] for c in media if c.stats["rx_packets"] > 0]), 1)
    S["codes"] = dict(sorted(collections.Counter(c.code for c in inv if c.code).items()))
    S["results"] = dict(collections.Counter(c.result for c in inv))
    faults = {}
    for c in faulty:
        f = faults.setdefault(c.fault, {"label": FAULTS.get(c.fault, (c.fault, ""))[0], "expect": c.expect, "n": 0, "outcomes": collections.Counter(), "no_audio": 0})
        f["n"] += 1
        f["outcomes"]["%s %s" % (c.code or "-", c.result)] += 1
        if c.answered and c.stats and not c.stats["audio_ok"]:
            f["no_audio"] += 1
    for f in faults.values():
        f["outcomes"] = dict(f["outcomes"])
    S["faults"] = faults
    if reg:
        S["auth"] = {"attempts": len(reg), "rejected": sum(1 for c in reg if c.result == "rejected"),
                     "accepted": sum(1 for c in reg if c.result == "accepted"),
                     "timeout": sum(1 for c in reg if c.result == "timeout"),
                     "codes": dict(collections.Counter(c.code for c in reg))}
    S["tester"] = {"rtp_max_lag_ms": round(node.rtp.max_lag_ms, 1), "late_ticks": node.rtp.late_ticks, "ticks": node.rtp.ticks,
                 "late_pct": round(100.0 * node.rtp.late_ticks / max(1, node.rtp.ticks), 2),
                   "sip_retransmits": node.sip_retx}
    # --- verdict
    th = node.thresholds
    V = []

    def add(name, val, rule, ok):
        V.append({"name": name, "value": val, "rule": rule, "status": "PASS" if ok else "FAIL"})

    if node.role == "customer" and normal:
        add("Answer rate (ASR)", _fmt(S["asr_pct"], "%"), ">= %s%%" % th["min_asr"], (S["asr_pct"] or 0) >= th["min_asr"])
        add("Post-dial delay p95", _fmt(S["pdd_p95"], " ms", 0), "<= %s ms" % th["max_pdd_ms"], S["pdd_p95"] is None or S["pdd_p95"] <= th["max_pdd_ms"])
        add("Calls dropped mid-call", str(S["dropped"] + S["no_ack"]), "0", S["dropped"] + S["no_ack"] == 0)
    if media:
        add("Calls with no audio", str(S["no_audio"]), "0", S["no_audio"] == 0)
        add("Packet loss (average)", _fmt(S["loss_avg"], "%", 2), "<= %s%%" % th["max_loss_pct"], (S["loss_avg"] or 0) <= th["max_loss_pct"])
        add("Jitter p95", _fmt(S["jitter_p95"], " ms", 1), "<= %s ms" % th["max_jitter_ms"], (S["jitter_p95"] or 0) <= th["max_jitter_ms"])
        add("MOS, worst call (estimated)", _fmt(S["mos_min"], "", 2), ">= %s" % th["min_mos"], (S["mos_min"] or 0) >= th["min_mos"])
    if S.get("dtmf_calls"):
        add("RFC 2833 DTMF digits echoed back correctly", "%d of %d calls" % (S["dtmf_calls"] - S["dtmf_bad"], S["dtmf_calls"]), "all", S["dtmf_bad"] == 0)
    if S.get("cid_calls"):
        add("Contact ID messages acknowledged with a kiss-off" if node.role == "customer" else "Contact ID messages accepted by this receiver",
            "%d of %d calls" % (S["cid_ok"], S["cid_calls"]), "all" if node.role == "customer" else "informational", S["cid_bad"] == 0)
    if S.get("tone_unmeasured") and node.role == "customer":
        add("Calls where the tone test could not be measured", str(S["tone_unmeasured"]), "0", False)
    if S.get("tone_calls"):
        add("Tone fidelity score, worst call (1-4.5)", _fmt(S["tone_min"], "", 2), ">= %s" % th["min_tone"], S["tone_min"] >= th["min_tone"])
        add("DTMF digits decoded correctly", _fmt(S["tone_digits_pct"], "%", 1), "100%", (S["tone_digits_pct"] or 0) >= 99.9)
    if inv or media or reg:
        t_ = S["tester"]
        add("Tester health (RTP timer lag)", "%s ms worst, %d late ticks (%s%%)" % (_fmt(t_["rtp_max_lag_ms"], "", 0), t_["late_ticks"], t_["late_pct"]),
            "late ticks <= 1% and worst <= 250 ms", t_["late_pct"] <= 1.0 and t_["rtp_max_lag_ms"] <= 250)
    S["verdict"] = V
    S["overall"] = "FAIL" if any(v["status"] == "FAIL" for v in V) else ("PASS" if V else "NO DATA")
    return S


def render_text(node, S, run=None):
    L = []
    L.append("=" * 72)
    L.append("sipload report - %s - %s" % (node.role, time.strftime("%Y-%m-%d %H:%M:%S")))
    L.append("this tester: %s  %s:%s  (host %s)" % (node.role, node.adv_ip, node.sip_port, socket.gethostname()))
    if run:
        pr = run.params
        L.append("test: %s   target %s   calls %s   hold %s-%s s   faults %s @ %s%%" % (
            pr.get("kind"), pr.get("target"), pr.get("calls") if pr.get("kind") == "batch" else pr.get("steps"),
            pr.get("hold_min"), pr.get("hold_max"), ",".join(pr.get("faults") or []) or "none", pr.get("fault_pct")))
        L.append("run %s: %s, %d launched, %.0f s" % (run.id, run.state, run.launched, (run.ended or time.time()) - run.started))
    L.append("=" * 72)
    L.append("OVERALL: %s" % S["overall"])
    for v in S["verdict"]:
        L.append("  [%s] %-34s %-12s (rule %s)" % (v["status"], v["name"], v["value"], v["rule"]))
    L.append("-" * 72)
    L.append("calls %d (normal %d, fault-injected %d)   answered %d   completed %d   dropped %d   failed %d   peak concurrent %d" % (
        S["calls_total"], S["normal_calls"], S["fault_calls"], S["answered"], S["completed"], S["dropped"], S["failed"], S["peak_concurrent"]))
    L.append("setup avg %s ms, p95 %s ms | PDD avg %s ms, p95 %s ms, max %s ms" % (
        _fmt(S["setup_avg"], "", 0), _fmt(S["setup_p95"], "", 0), _fmt(S["pdd_avg"], "", 0), _fmt(S["pdd_p95"], "", 0), _fmt(S["pdd_max"], "", 0)))
    L.append("media: loss avg %s%% max %s%% | jitter avg %s ms p95 %s ms max %s ms | MOS avg %s min %s | packets tx %d rx %d" % (
        _fmt(S["loss_avg"], "", 2), _fmt(S["loss_max"], "", 2), _fmt(S["jitter_avg"], "", 2), _fmt(S["jitter_p95"], "", 1),
        _fmt(S["jitter_max"], "", 1), _fmt(S["mos_avg"], "", 2), _fmt(S["mos_min"], "", 2), S["tx_packets"], S["rx_packets"]))
    if S.get("tone_calls"):
        L.append("tone test (%d calls analysed): score avg %s min %s | SNR avg %s dB | level error avg %s dB | frequency error avg %s Hz | digits ok %s%% | dropouts %d ms" % (
            S["tone_calls"], _fmt(S["tone_avg"], "", 2), _fmt(S["tone_min"], "", 2), _fmt(S["tone_snr_avg"], "", 1), _fmt(S["tone_level_avg"], "", 2),
            _fmt(S["tone_freq_avg"], "", 2), _fmt(S["tone_digits_pct"], "", 1), S["tone_dropout_ms"]))
    if S.get("dtmf_calls"):
        L.append("RFC 2833 DTMF (echo): %d of %d calls returned the digits correctly" % (S["dtmf_calls"] - S["dtmf_bad"], S["dtmf_calls"]))
    if S.get("cid_calls"):
        L.append("Contact ID: %d of %d calls completed (message accepted, kiss-off heard)%s" % (
            S["cid_ok"], S["cid_calls"], "   handshake after %s ms, %s tries, done in %s ms (averages)" % (S["cid_hs_avg"], S["cid_tries_avg"], S["cid_total_avg"]) if S.get("cid_hs_avg") is not None else ""))
    wc = worst_calls(node, 5)
    if wc:
        L.append("lowest quality calls:")
        for d in wc:
            L.append("  #%-4s dialed %-12s from %-10s %-6s MOS %s  loss %s%%  jitter %s ms  rtt %s  tone %s  %s" % (
                d["id"], d["number"], d["caller"] or "-", d["codec"] or "-", _fmt(d["mos"], "", 2), _fmt(d["loss"], "", 2), _fmt(d["jitter"], "", 1),
                _fmt(d["rtt"], "", 1), _fmt(d["tone"], "", 2), d["result"]))
    if S.get("rtt_calls"):
        L.append("echo round-trip time (%d calls): avg %s ms, min %s ms, max %s ms" % (S["rtt_calls"], _fmt(S["rtt_avg"], "", 1), _fmt(S["rtt_min"], "", 1), _fmt(S["rtt_max"], "", 1)))
    if S.get("tone_unmeasured"):
        L.append("tone test: %d calls could not be measured (other end not sending the Tone test, or no audio)" % S["tone_unmeasured"])
    L.append("SIP final codes: " + (", ".join("%s x%d" % kv for kv in S["codes"].items()) or "none"))
    L.append("results: " + (", ".join("%s x%d" % kv for kv in S["results"].items()) or "none"))
    if S["faults"]:
        L.append("-" * 72)
        L.append("fault injection:")
        for k, f in S["faults"].items():
            L.append("  %-16s %3d calls  outcomes: %s%s" % (k, f["n"], ", ".join("%s x%d" % kv for kv in f["outcomes"].items()),
                                                           ("  (answered but silent: %d)" % f["no_audio"]) if f["no_audio"] else ""))
            L.append("      expected: %s" % f["expect"])
    if "auth" in S:
        a = S["auth"]
        L.append("-" * 72)
        L.append("authentication test: %d attempts, %d rejected, %d ACCEPTED, %d no reply; codes %s" % (
            a["attempts"], a["rejected"], a["accepted"], a["timeout"], a["codes"]))
    L.append("tester: RTP timer max lag %s ms, late ticks %d of %d (%s%%), SIP retransmits %d" % (
        S["tester"]["rtp_max_lag_ms"], S["tester"]["late_ticks"], S["tester"]["ticks"], S["tester"]["late_pct"], S["tester"]["sip_retransmits"]))
    L.append("=" * 72)
    return "\n".join(L)


CSV_COLS = ["id", "dir", "method", "number", "caller", "peer", "result", "code", "reason", "fault", "action", "started", "dur", "setup_ms", "pdd_ms",
            "hungup_by", "retx", "auth_fail", "tx", "rx", "loss", "jitter", "mos", "audio_ok", "exact", "rx_codec", "tone", "rtt"]


def render_csv(node):
    out = io.StringIO()
    w = csv.writer(out)
    w.writerow(CSV_COLS)
    for c in list(node.history):
        d = c.to_dict()
        d["started"] = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(d["started"]))
        w.writerow([d.get(k, "") for k in CSV_COLS])
    return out.getvalue()


def worst_calls(node, n=10):
    """Answered normal calls with a MOS, worst first (lowest MOS, then lowest tone score, then highest loss)."""
    ds = [c.to_dict() for c in list(node.history) if c.answered and not c.fault and c.stats and c.stats.get("mos") is not None]
    ds.sort(key=lambda d: (d["mos"], d["tone"] if d["tone"] is not None else 9.9, -(d["loss"] or 0), d["id"]))
    return ds[:n]


def worst_html(node, esc):
    wc = worst_calls(node, 10)
    if not wc:
        return ""
    rows = "".join("<tr><td>%d</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td></tr>" % (
        d["id"], esc(d["number"]), esc(d["caller"]), esc(d["codec"]), d["mos"], d["loss"] if d["loss"] is not None else "", d["jitter"] if d["jitter"] is not None else "",
        d["rtt"] if d["rtt"] is not None else "", d["tone"] if d["tone"] is not None else "", esc(d["result"])) for d in wc)
    return ("<h2>Lowest quality calls (worst 10)</h2><div class='tag'>Sorted by MOS, then tone score and loss. Use the call number to find it in the dashboard or CSV.</div>"
            "<table><tr><th>#</th><th>Dialed</th><th>From</th><th>Codec</th><th>MOS</th><th>Loss %%</th><th>Jitter ms</th><th>RTT ms</th><th>Tone</th><th>Result</th></tr>%s</table>" % rows).replace("%%", "%")


def _bucket(pts, n, mode):
    if len(pts) <= n:
        return pts
    k = len(pts) / float(n)
    out = []
    for i in range(n):
        ch = pts[int(i * k):int((i + 1) * k)]
        if not ch:
            continue
        ys = [p[1] for p in ch]
        y = min(ys) if mode == "min" else (max(ys) if mode == "max" else sum(ys) / len(ys))
        out.append((sum(p[0] for p in ch) / len(ch), y))
    return out


def _svg_chart(title, note, lines, ymin, ymax, xlabel, hline=None, w=1000, h=230):
    L, R, T, B = 52, 14, 14, 34
    xs = [p[0] for _, _, pts in lines for p in pts]
    if not xs:
        return ""
    x0, x1 = min(xs), max(xs)
    if x1 == x0:
        x1 = x0 + 1
    fx = lambda x: L + (x - x0) / (x1 - x0) * (w - L - R)
    fy = lambda y: T + (1 - (min(max(y, ymin), ymax) - ymin) / float(ymax - ymin)) * (h - T - B)
    g = []
    for i in range(5):
        v = ymin + (ymax - ymin) * i / 4.0
        g.append('<line x1="%d" x2="%d" y1="%.1f" y2="%.1f" stroke="#e3e6ec"/><text x="%d" y="%.1f" font-size="11" text-anchor="end" fill="#555">%s</text>' % (
            L, w - R, fy(v), fy(v), L - 6, fy(v) + 4, ("%.1f" % v).rstrip("0").rstrip(".")))
    for i in range(6):
        v = x0 + (x1 - x0) * i / 5.0
        g.append('<text x="%.1f" y="%d" font-size="11" text-anchor="middle" fill="#555">%d</text>' % (fx(v), h - 16, round(v)))
    g.append('<text x="%d" y="%d" font-size="11" text-anchor="middle" fill="#555">%s</text>' % ((L + w - R) // 2, h - 3, xlabel))
    if hline:
        g.append('<line x1="%d" x2="%d" y1="%.1f" y2="%.1f" stroke="#c0262d" stroke-dasharray="6 4"/><text x="%d" y="%.1f" font-size="11" fill="#c0262d" text-anchor="end">%s</text>' % (
            L, w - R, fy(hline[0]), fy(hline[0]), w - R - 2, fy(hline[0]) - 4, hline[1]))
    leg = []
    for j, (lab, col, pts) in enumerate(lines):
        if not pts:
            continue
        d = " ".join("%.1f,%.1f" % (fx(x), fy(y)) for x, y in pts)
        if len(pts) > 1:
            g.append('<polyline fill="none" stroke="%s" stroke-width="1.6" points="%s"/>' % (col, d))
        if len(pts) <= 150:
            g.extend('<circle cx="%.1f" cy="%.1f" r="2.6" fill="%s"/>' % (fx(x), fy(y), col) for x, y in pts)
        leg.append('<tspan fill="%s">&#9632; %s</tspan>&nbsp;&nbsp;' % (col, lab))
    g.append('<text x="%d" y="11" font-size="12">%s</text>' % (L, "".join(leg)))
    return '<h3>%s</h3><div class="tag">%s</div><svg viewBox="0 0 %d %d" width="100%%" style="max-width:%dpx;background:#fff;border:1px solid #d5d9e0">%s</svg>' % (title, note, w, h, w, "".join(g))


def charts_html(node):
    ds = [c.to_dict() for c in list(node.history)[-5000:]]
    ds = [d for d in ds if not d["fault"]] or ds
    out = []
    n = lambda k: [(i + 1, d[k]) for i, d in enumerate(ds) if d.get(k) is not None]
    mos = n("mos")
    if mos:
        out.append(_svg_chart("MOS per call", "Estimated voice quality of each call, in the order the calls finished (long runs show the worst call in each group). 4.4 is perfect G.711; the red line is the pass limit.",
                              [("MOS", "#2563eb", _bucket(mos, 300, "min"))], 1, 4.5, "call number", (node.thresholds["min_mos"], "limit %.1f" % node.thresholds["min_mos"])))
    tone = n("tone")
    if tone:
        out.append(_svg_chart("Tone test score per call", "How closely the received tones match the original (1-4.5). Dips mean noise, dropouts, wrong level or missing digits.",
                              [("tone score", "#7c3aed", _bucket(tone, 300, "min"))], 1, 4.5, "call number", (node.thresholds["min_tone"], "limit %.1f" % node.thresholds["min_tone"])))
    rtt = n("rtt")
    if rtt:
        out.append(_svg_chart("Echo round-trip time per call", "Time for our audio packets to reach the echo number and come back (ms, worst in each group). This is the latency of the whole path.",
                              [("round trip ms", "#0f766e", _bucket(rtt, 300, "max"))], 0, max(p[1] for p in rtt) * 1.2 + 1, "call number"))
    loss, jit = n("loss"), n("jitter")
    if loss or jit:
        top = max([p[1] for p in loss + jit] + [5.0])
        out.append(_svg_chart("Packet loss and jitter per call", "Loss in % and jitter in ms (worst in each group). Loss should stay near 0.",
                              [("loss %", "#d97706", _bucket(loss, 300, "max")), ("jitter ms", "#0f766e", _bucket(jit, 300, "max"))], 0, top * 1.1, "call number"))
    ser = list(node.series)
    if len(ser) >= 2:
        t0 = ser[0][0]
        pts = [(s[0] - t0, s[1]) for s in ser]
        top = max(p[1] for p in pts) or 1
        out.append(_svg_chart("Calls in progress over time", "How many calls were up at once during the test (the load the SBC carried).",
                              [("calls in progress", "#2563eb", _bucket(pts, 300, "max"))], 0, top * 1.1 + 1, "seconds since start"))
    return "".join(out)


def list_reports(node):
    d = node.args.out
    res = []
    if d and os.path.isdir(d):
        for f in sorted(os.listdir(d), reverse=True):
            if f.startswith("sipload-") and f.endswith(".html"):
                st = os.stat(os.path.join(d, f))
                m = re.search(r"-(PASS|FAIL|NODATA)\.html$", f)
                res.append({"name": f, "time": time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(st.st_mtime)), "size": st.st_size,
                            "verdict": m.group(1) if m else ""})
    return {"dir": os.path.abspath(d) if d else "", "reports": res[:200]}


def render_html(node, S, run=None):
    esc = lambda s: (str(s).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;"))
    rows = "".join("<tr class='%s'><td>%s</td><td>%s</td><td>%s</td><td>%s</td></tr>" % (
        v["status"].lower(), esc(v["status"]), esc(v["name"]), esc(v["value"]), esc(v["rule"])) for v in S["verdict"])
    crows = ""
    for c in list(node.history)[-500:]:
        d = c.to_dict()
        crows += "<tr>" + "<td>%s</td>" * 13 + "</tr>" 
        crows = crows[:crows.rfind("<tr>")] + ("<tr>" + "<td>%s</td>" * 13 + "</tr>") % (
            d["id"], esc(d["number"]), esc(d["caller"]), d["tone"] if d["tone"] is not None else "", esc(d["result"]), d["code"] or "", esc(d["fault"]), d["dur"], d["pdd_ms"] if d["pdd_ms"] is not None else "",
            d["loss"] if d["loss"] is not None else "", d["jitter"] if d["jitter"] is not None else "", d["mos"] if d["mos"] is not None else "",
            "yes" if d["audio_ok"] else ("no" if d["audio_ok"] is False else ""))
    fr = "".join("<tr><td>%s</td><td>%d</td><td>%s</td><td>%s</td></tr>" % (esc(k), f["n"], esc(", ".join("%s x%d" % kv for kv in f["outcomes"].items())), esc(f["expect"]))
                 for k, f in S["faults"].items())
    runinfo = ""
    if run:
        pr = run.params
        runinfo = "<p>Test <b>%s</b> to %s - %d calls launched - %s - %.0f s</p>" % (esc(pr.get("kind")), esc(pr.get("target")), run.launched, esc(run.state), (run.ended or time.time()) - run.started)
    runinfo = ("<p>This tester (%s): <b>%s</b> SIP port %s &middot; host %s%s</p>" % (
        esc(node.role), esc(node.adv_ip), node.sip_port, esc(socket.gethostname()),
        (" &middot; sending to <b>%s</b>" % esc(run.params.get("target"))) if run else "")) + runinfo
    txt = esc(render_text(node, S, run))
    return """<!doctype html><html><head><meta charset="utf-8"><title>sipload report</title>
<style>body{font:14px system-ui,sans-serif;margin:24px;max-width:1100px;color:#1d2330}h1{font-size:20px}table{border-collapse:collapse;width:100%%;margin:10px 0}
td,th{border:1px solid #d5d9e0;padding:4px 8px;text-align:left;font-size:13px}th{background:#f1f3f7}tr.pass td:first-child{color:#0a7d33;font-weight:700}tr.fail td:first-child{color:#c0262d;font-weight:700}
.big{font-size:26px;font-weight:700;color:%s}pre{background:#f6f7f9;padding:10px;overflow:auto;font-size:12px}</style></head><body>
<h1>sipload report - %s - %s</h1>%s<div class="big">OVERALL: %s</div>
<table><tr><th>Status</th><th>Check</th><th>Result</th><th>Rule</th></tr>%s</table>
%s<h2>Calls (latest 500)</h2><table><tr><th>#</th><th>Dialed number</th><th>From</th><th>Tone score</th><th>Result</th><th>Code</th><th>Fault</th><th>Secs</th><th>PDD ms</th><th>Loss %%</th><th>Jitter ms</th><th>MOS</th><th>Audio</th></tr>%s</table>
<h2>Details</h2><pre>%s</pre></body></html>""" % (
        "#0a7d33" if S["overall"] == "PASS" else "#c0262d", esc(node.role), time.strftime("%Y-%m-%d %H:%M:%S"), runinfo, S["overall"], rows,
        worst_html(node, esc) + charts_html(node) + (("<h2>Fault injection</h2><table><tr><th>Fault</th><th>Calls</th><th>Outcomes</th><th>Expected</th></tr>%s</table>" % fr) if fr else ""),
        crows, txt)


def node_save_report(self, run=None):
    d = self.args.out
    if not d:
        raise ValueError("saving reports is turned off (started with --out ''); restart without it")
    os.makedirs(d, exist_ok=True)
    S = summarize(self)
    base = os.path.join(d, "sipload-%s-%s-%s" % (self.role, time.strftime("%Y%m%d-%H%M%S"), S["overall"].replace(" ", "")))
    open(base + ".html", "w").write(render_html(self, S, run))
    open(base + ".csv", "w").write(render_csv(self))
    open(base + ".json", "w").write(json.dumps({"summary": S, "run": run.to_dict() if run else None,
                                                 "calls": [c.to_dict() for c in self.history]}, indent=1, default=str))
    print(render_text(self, S, run), flush=True)
    self.last_report = os.path.abspath(base)
    log("report saved in", os.path.dirname(self.last_report), "->", os.path.basename(base) + ".html / .csv / .json")
    return self.last_report


def node_state(self):
    now = time.time()
    with self.lock:
        act = [c.to_dict() for c in sorted(self.calls.values(), key=lambda c: c.id)]
        fin = [c.to_dict() for c in list(self.history)[-300:]]
    cache = getattr(self, "_sum_cache", None)
    if cache is None or now - cache[0] > 1.0:
        self._sum_cache = cache = (now, summarize(self))
    S = cache[1]
    try:
        audios = sorted(f for f in os.listdir(self.audio_dir) if f.lower().endswith(".wav"))
    except OSError:
        audios = []
    return {"role": self.role, "version": VERSION, "now": now, "uptime": round(now - self.started), "ip": self.adv_ip,
            "sip_port": self.sip_port, "run": self.run.to_dict() if self.run else None, "summary": S,
            "active": act, "finished": fin, "series": list(self.series)[-900:], "cfg": self.cfg, "thresholds": self.thresholds,
            "codec_list": list(CODECS), "audio": {"name": self.audio.name, "kind": self.audio.kind, "seconds": round(self.audio.seconds, 1), "files": audios},
            "faults": {k: v[0] for k, v in FAULTS.items()}, "fault_help": {k: v[1] for k, v in FAULTS.items()},
            "run_defaults": RUN_DEFAULTS, "sip": {"rx": self.sip_rx, "tx": self.sip_tx, "retx": self.sip_retx},
            "rtp": {"tx": self.rtp.total_tx, "rx": self.rtp.total_rx, "lag_ms": round(self.rtp.max_lag_ms, 1)}}


def node_metrics(self):
    S = summarize(self)
    r = self.role
    L = []

    def m(name, val, help_, labels="", kind="gauge"):
        if not any(x.startswith("# HELP " + name + " ") for x in L):
            L.append("# HELP %s %s" % (name, help_))
            L.append("# TYPE %s %s" % (name, kind))
        L.append("%s%s %s" % (name, labels, val))

    m("sipload_calls_active", len(self.calls), "Calls in progress.", '{role="%s"}' % r)
    m("sipload_calls_peak", S["peak_concurrent"], "Peak concurrent calls.", '{role="%s"}' % r)
    for k, v in S["results"].items():
        m("sipload_calls_total", v, "Finished calls by result.", '{role="%s",result="%s"}' % (r, k), "counter")
    for k, v in S["codes"].items():
        m("sipload_sip_final_code_total", v, "Calls by final SIP code.", '{role="%s",code="%s"}' % (r, k), "counter")
    for k in ("loss_avg", "loss_max", "jitter_avg", "jitter_p95", "mos_avg", "mos_min", "pdd_avg", "pdd_p95", "asr_pct",
              "tone_avg", "tone_min", "tone_snr_avg", "tone_digits_pct", "tone_dropout_ms", "rtt_avg", "rtt_max", "answered"):
        if S.get(k) is not None:
            m("sipload_" + k, S[k], "Summary " + k + " over finished normal calls since the last reset.", '{role="%s"}' % r)
    m("sipload_run_active", 1 if (self.run is not None and self.run.state == "running") else 0, "1 while a test is running.", '{role="%s"}' % r)
    if S["verdict"]:
        m("sipload_verdict_pass", 1 if S["overall"] == "PASS" else 0, "1 = overall PASS, 0 = FAIL (last results since reset).", '{role="%s"}' % r)
    m("sipload_uptime_seconds", int(time.time() - self.started), "Tester uptime.", '{role="%s"}' % r)
    m("sipload_info", 1, "Tester version.", '{role="%s",version="%s"}' % (r, VERSION))
    m("sipload_rtp_packets_total", self.rtp.total_tx, "RTP packets sent.", '{role="%s",dir="tx"}' % r, "counter")
    m("sipload_rtp_packets_total", self.rtp.total_rx, "RTP packets received.", '{role="%s",dir="rx"}' % r, "counter")
    m("sipload_rtp_timer_lag_ms", round(self.rtp.max_lag_ms, 1), "Worst delay of the 20 ms RTP timer (tester health).", '{role="%s"}' % r)
    return "\n".join(L) + "\n"


Node.save_report = node_save_report
Node.state = node_state
Node.metrics = node_metrics


# ------------------------------------------------------------------ web dashboard
def wav_both(rx, rxpt, tx, txpt, off, mode="mix"):
    """Both sides of a call. mode: mix (mono, both heard together), stereo (left = heard, right = sent), rx, tx."""
    a = array.array("h", map(DEC[rxpt].__getitem__, rx)) if rx else array.array("h")
    b = array.array("h", map(DEC[txpt].__getitem__, tx)) if tx else array.array("h")
    if off > 0:
        b = array.array("h", [0] * 0) + b
        a = array.array("h", [0] * off) + a
    elif off < 0:
        b = array.array("h", [0] * (-off)) + b
    n = max(len(a), len(b))
    a.extend([0] * (n - len(a)))
    b.extend([0] * (n - len(b)))
    if mode == "rx":
        out, ch = a, 1
    elif mode == "tx":
        out, ch = b, 1
    elif mode == "stereo":
        out, ch = array.array("h", [0] * (2 * n)), 2
        out[0::2] = a
        out[1::2] = b
    else:
        out, ch = array.array("h", (max(-32768, min(32767, x + y)) for x, y in zip(a, b))), 1
    if sys.byteorder == "big":
        out.byteswap()
    buf = io.BytesIO()
    with wave.open(buf, "wb") as w:
        w.setnchannels(ch)
        w.setsampwidth(2)
        w.setframerate(8000)
        w.writeframes(out.tobytes())
    return buf.getvalue()


def wav_bytes(pcm_payload, pt):
    pcm = array.array("h", map(DEC[pt].__getitem__, pcm_payload))
    if sys.byteorder == "big":
        pcm.byteswap()
    buf = io.BytesIO()
    with wave.open(buf, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(8000)
        w.writeframes(pcm.tobytes())
    return buf.getvalue()


def find_call(node, cid):
    with node.lock:
        c = next((x for x in node.calls.values() if x.id == cid), None)
        if c is None:
            c = next((x for x in reversed(node.history) if x.id == cid), None)
    return c


def update_settings(node, body):
    cfg = node.cfg
    if "cfg" in body:
        n = body["cfg"]
        if "mix" in n:
            for k in cfg["mix"]:
                cfg["mix"][k] = max(0.0, float(n["mix"].get(k, 0) or 0))
        for k in ("ring_ms", "delay_min_ms", "delay_max_ms", "loss_pct", "hangup_after"):
            if k in n:
                cfg[k] = max(0.0, float(n[k] or 0))
        if "dialplan_on" in n:
            cfg["dialplan_on"] = bool(n["dialplan_on"])
        if "early_media" in n:
            cfg["early_media"] = bool(n["early_media"])
        if "rtp_mode" in n:
            if n["rtp_mode"] not in ("normal", "none", "blackhole", "private_ip"):
                raise ValueError("bad rtp_mode")
            cfg["rtp_mode"] = n["rtp_mode"]
        if "codecs" in n:
            cfg["codecs"] = [c for c in n["codecs"] if c in CODEC_PT] or ["PCMU"]
        for k in ("auth_user", "auth_pass"):
            if k in n:
                cfg[k] = str(n[k])
        cfg["delay_max_ms"] = max(cfg["delay_min_ms"], cfg["delay_max_ms"])
    if "thresholds" in body:
        for k in node.thresholds:
            if k in body["thresholds"]:
                node.thresholds[k] = float(body["thresholds"][k])


LOGIN_PAGE = r"""<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>sipload login</title>
<style>:root{--bg:#f4f6f9;--card:#fff;--ink:#1d2330;--mut:#667085;--line:#d5d9e0;--acc:#2563eb;--bad:#c0262d}
@media (prefers-color-scheme:dark){:root{--bg:#12151c;--card:#1b2029;--ink:#e6e9ef;--mut:#98a2b3;--line:#2c3340;--acc:#6ea0ff;--bad:#ff7b80}}
body{margin:0;background:var(--bg);color:var(--ink);font:15px system-ui,sans-serif;display:flex;min-height:100vh;align-items:center;justify-content:center}
form{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:26px;width:300px;max-width:88vw}h1{font-size:20px;margin:0 0 4px}.mut{color:var(--mut);font-size:13px;margin-bottom:14px}
label{display:block;font-size:13px;color:var(--mut);margin-top:10px}input{width:100%;box-sizing:border-box;padding:8px;margin-top:3px;border:1px solid var(--line);border-radius:6px;background:var(--bg);color:var(--ink);font-size:15px}
button{margin-top:16px;width:100%;padding:9px;background:var(--acc);color:#fff;border:0;border-radius:6px;font-size:15px;cursor:pointer}#err{color:var(--bad);font-size:13px;margin-top:10px;min-height:16px}</style></head>
<body><form id="f"><h1>sipload</h1><div class="mut">__ROLE__ tester - sign in</div>
<label>User name<input id="u" autocomplete="username" autofocus></label><label>Password<input id="p" type="password" autocomplete="current-password"></label>
<button>Sign in</button><div id="err"></div></form>
<script>document.getElementById("f").onsubmit=async e=>{e.preventDefault();const r=await fetch("/api/login",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({user:u.value,password:p.value})});
const j=await r.json().catch(()=>({}));if(r.ok)location.href="/";else err.textContent=j.error||"login failed"};</script></body></html>"""


class Auth:
    """Users in users.json (pbkdf2 hashed), cookie sessions, lockout after repeated failures."""
    HOURS = 12

    def __init__(self, path):
        self.path = path
        self.sessions = {}
        self.fails = {}
        self.lock = threading.Lock()
        self.users = {}
        self.load()

    def load(self):
        try:
            self.users = json.load(open(self.path))
        except (OSError, ValueError):
            self.users = {}

    def save(self):
        fd = os.open(self.path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        with os.fdopen(fd, "w") as f:
            json.dump(self.users, f, indent=1)

    @staticmethod
    def _hash(pw, salt):
        return hashlib.pbkdf2_hmac("sha256", pw.encode(), bytes.fromhex(salt), 200000).hex()

    def set_user(self, name, pw, role="admin"):
        if role not in ("admin", "viewer"):
            raise ValueError("role must be admin or viewer")
        if not re.match(r"^[A-Za-z0-9_.@-]{1,40}$", name):
            raise ValueError("user name: letters, digits and _ . @ - only")
        if len(pw) < 8:
            raise ValueError("password must be at least 8 characters")
        salt = secrets.token_hex(16)
        self.users[name] = {"salt": salt, "hash": self._hash(pw, salt), "role": role}
        self.save()

    def check(self, name, pw, ip):
        now = time.time()
        with self.lock:
            f = [t for t in self.fails.get(ip, []) if now - t < 600]
            self.fails[ip] = f
            if len(f) >= 5 and now - f[-1] < 300:
                raise PermissionError("too many failed logins from this address; wait 5 minutes")
        u = self.users.get(name)
        salt = u["salt"] if u else "00" * 16
        good = secrets.compare_digest(self._hash(pw, salt), u["hash"] if u else "x") and u is not None
        if not good:
            with self.lock:
                self.fails[ip].append(now)
            return None
        tok = secrets.token_urlsafe(24)
        with self.lock:
            self.sessions = {k: v for k, v in self.sessions.items() if v[2] > now}
            self.sessions[tok] = (name, u["role"], now + self.HOURS * 3600)
        return tok

    def session(self, tok):
        v = self.sessions.get(tok or "")
        if v and v[2] > time.time():
            return v[0], v[1]
        return None

    def logout(self, tok):
        self.sessions.pop(tok or "", None)


def ensure_admin(auth):
    """First start: create an admin with a random password and show it once."""
    if auth.users:
        return
    pw = secrets.token_urlsafe(9)
    auth.set_user("admin", pw, "admin")
    log("FIRST START: created user 'admin' with password: %s   (saved hashed in %s; add users with: sipload user add NAME)" % (pw, auth.path))


def start_web(node, hostport, auth, peer_key=""):
    host, _, port = hostport.rpartition(":")
    host, port = host or "0.0.0.0", int(port)
    page = PAGE.replace("__ROLE__", node.role).replace("__VERSION__", VERSION)

    class H(BaseHTTPRequestHandler):
        server_version = "sipload"

        def log_message(self, *a):
            pass

        def _send(self, code, body, ctype="application/json", cors=False, extra=None):
            if isinstance(body, str):
                body = body.encode()
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            if cors:
                self.send_header("Access-Control-Allow-Origin", "*")
            for k, v in (extra or {}).items():
                self.send_header(k, v)
            self.end_headers()
            self.wfile.write(body)

        def _json(self, obj, code=200, cors=False):
            self._send(code, json.dumps(obj, default=str), cors=cors)

        def _cookie(self):
            c = self.headers.get("Cookie") or ""
            m = re.search(r"(?:^|;\s*)sl_session=([^;]+)", c)
            return m.group(1) if m else ""

        def _me(self):
            """(user, role) of the logged-in session, or None.  With no login configured everybody is admin."""
            if auth is None:
                return ("local", "admin")
            return auth.session(self._cookie())

        def _ok(self, q):
            return self._me() is not None

        def _peerkey(self, q):
            if not peer_key:
                return False
            given = self.headers.get("X-Peer-Key") or (q.get("key") or [""])[0]
            b = self.headers.get("Authorization") or ""
            if b.startswith("Bearer "):
                given = given or b[7:]
            return bool(given) and secrets.compare_digest(given, peer_key)

        def do_OPTIONS(self):
            self.send_response(204)
            self.send_header("Access-Control-Allow-Origin", "*")
            self.send_header("Access-Control-Allow-Headers", "X-Peer-Key, Content-Type")
            self.end_headers()

        def do_GET(self):
            u = urlparse(self.path)
            q = parse_qs(u.query)
            p = u.path
            try:
                me = self._me()
                if p == "/login":
                    if me is not None and auth is not None:
                        return self._send(302, "", extra={"Location": "/"})
                    return self._send(200, LOGIN_PAGE.replace("__ROLE__", node.role), "text/html; charset=utf-8")
                if p in ("/api/state", "/metrics"):
                    if me is None and not self._peerkey(q):
                        return self._json({"error": "login required"}, 401, cors=True)
                    if p == "/metrics":
                        return self._send(200, node.metrics(), "text/plain; version=0.0.4")
                    st = node.state()
                    st["me"] = {"user": me[0], "role": me[1]} if me else {"user": "peer", "role": "viewer"}
                    return self._json(st, cors=True)
                if me is None:
                    if p == "/" or p.startswith("/report") or p.startswith("/saved/"):
                        return self._send(302, "", extra={"Location": "/login"})
                    return self._json({"error": "login required"}, 401)
                if p == "/":
                    return self._send(200, page, "text/html; charset=utf-8")
                if p == "/api/reports":
                    return self._json(list_reports(node))
                if p.startswith("/saved/"):
                    nm = os.path.basename(p[7:])
                    ext = os.path.splitext(nm)[1]
                    fp = os.path.join(node.args.out or "", nm)
                    if not nm.startswith("sipload-") or ext not in (".html", ".csv", ".json") or not os.path.isfile(fp):
                        return self._json({"error": "not found"}, 404)
                    ct = {".html": "text/html; charset=utf-8", ".csv": "text/csv", ".json": "application/json"}[ext]
                    return self._send(200, open(fp, "rb").read(), ct)
                if p == "/report":
                    S = summarize(node)
                    fmt = (q.get("fmt") or ["html"])[0]
                    if fmt == "json":
                        return self._json({"summary": S, "worst_calls": worst_calls(node, 20), "calls": [c.to_dict() for c in node.history]})
                    if fmt == "csv":
                        return self._send(200, render_csv(node), "text/csv", extra={"Content-Disposition": "attachment; filename=sipload.csv"})
                    if fmt == "txt":
                        return self._send(200, render_text(node, S, node.run), "text/plain; charset=utf-8")
                    return self._send(200, render_html(node, S, node.run), "text/html; charset=utf-8")
                m = re.match(r"^/api/call/(\d+)$", p)
                if m:
                    c = find_call(node, int(m.group(1)))
                    return self._json(c.to_dict(True) if c else {"error": "no such call"}, 200 if c else 404)
                m = re.match(r"^/audio/(\d+)\.wav$", p)
                if m:
                    if not self._ok(q):
                        return self._json({"error": "password required"}, 401)
                    c = find_call(node, int(m.group(1)))
                    if c is None:
                        return self._json({"error": "no such call"}, 404)
                    live = c.rtp is not None and not c.done
                    rec = bytes(c.rtp.rec) if live else c.rec
                    pt = (c.rtp.rec_pt if live else c.rec_pt) or 0
                    txr = bytes(c.rtp.rec_tx) if live else c.rec_tx
                    txpt = ((c.rtp.fkey if c.rtp.fkey is not None else c.rtp.tx_pt) if live else c.tx_pt) or 0
                    off = call_rec_offset(c.rtp) if live else c.rec_off
                    if not rec and not txr:
                        return self._json({"error": "no audio was received on this call"}, 404)
                    mode = (parse_qs(urlparse(self.path).query).get("mode") or ["rx"])[0]
                    if mode in ("mix", "stereo", "tx") or (mode == "rx" and not rec):
                        if txpt not in (0, 8):
                            txr = b""
                        if not rec and mode == "rx":
                            mode = "tx"
                        return self._send(200, wav_both(rec, pt if pt in (0, 8) else 0, txr, txpt, off, mode), "audio/wav",
                                          extra={"Content-Disposition": 'attachment; filename="sipload-call-%d-%s.wav"' % (c.id, mode)} if "dl=1" in (self.path or "") else None)
                    extra = {"Content-Disposition": 'attachment; filename="sipload-call-%d.wav"' % c.id} if "dl=1" in (self.path or "") else None
                    return self._send(200, wav_bytes(rec, pt), "audio/wav", extra=extra) if extra else self._send(200, wav_bytes(rec, pt), "audio/wav")
                m = re.match(r"^/listen/(\d+)$", p)
                if m:
                    return self._listen(int(m.group(1)), q)
                self._json({"error": "not found"}, 404)
            except (BrokenPipeError, ConnectionResetError):
                pass
            except Exception as e:
                try:
                    self._json({"error": repr(e)}, 500)
                except Exception:
                    pass

        def _listen(self, cid, q):
            if not self._ok(q):
                return self._json({"error": "password required"}, 401)
            c = find_call(node, cid)
            if c is None or c.rtp is None or c.done:
                return self._json({"error": "this call is not live; use the recording"}, 404)
            qu = queue.Queue(maxsize=500)
            st = c.rtp
            st.listeners.append(qu)
            try:
                self.send_response(200)
                self.send_header("Content-Type", "application/octet-stream")
                self.send_header("Cache-Control", "no-store")
                self.send_header("X-Audio", "pcm16le 8000 mono")
                self.end_headers()
                while not node.stopping:
                    try:
                        chunk = qu.get(timeout=1.0)
                    except queue.Empty:
                        if c.done:
                            break
                        continue
                    if chunk is None:
                        break
                    buf = [chunk]
                    for _ in range(8):
                        try:
                            nxt = qu.get_nowait()
                        except queue.Empty:
                            break
                        if nxt is None:
                            buf.append(b"")
                            break
                        buf.append(nxt)
                    self.wfile.write(b"".join(buf))
                    self.wfile.flush()
            except (BrokenPipeError, ConnectionResetError, OSError):
                pass
            finally:
                if qu in st.listeners:
                    st.listeners.remove(qu)

        def do_POST(self):
            u = urlparse(self.path)
            q = parse_qs(u.query)
            try:
                if u.path == "/api/login":
                    n = int(self.headers.get("Content-Length") or 0)
                    b = json.loads(self.rfile.read(n) or b"{}")
                    try:
                        tok = auth.check(str(b.get("user", "")), str(b.get("password", "")), self.client_address[0]) if auth else "x"
                    except PermissionError as e:
                        return self._json({"error": str(e)}, 429)
                    if not tok:
                        log("login failed for '%s' from %s" % (str(b.get("user", ""))[:40], self.client_address[0]))
                        return self._json({"error": "wrong user name or password"}, 401)
                    sec = "; Secure" if self.headers.get("X-Forwarded-Proto") == "https" else ""
                    return self._send(200, json.dumps({"ok": True}), extra={"Set-Cookie": "sl_session=%s; HttpOnly; SameSite=Strict; Path=/; Max-Age=%d%s" % (tok, Auth.HOURS * 3600, sec)})
                if u.path == "/api/logout":
                    if auth:
                        auth.logout(self._cookie())
                    return self._send(200, json.dumps({"ok": True}), extra={"Set-Cookie": "sl_session=; HttpOnly; SameSite=Strict; Path=/; Max-Age=0"})
                me = self._me()
                if me is None:
                    return self._json({"error": "login required"}, 401)
                if me[1] != "admin":
                    return self._json({"error": "your account is view-only"}, 403)
                n = int(self.headers.get("Content-Length") or 0)
                if n > 25 * 1024 * 1024:
                    return self._json({"error": "too large"}, 413)
                raw = self.rfile.read(n) if n else b""
                p = u.path
                if p == "/api/audio":
                    name = re.sub(r"[^A-Za-z0-9._-]", "_", (q.get("name") or ["upload.wav"])[0])[:60]
                    if not name.lower().endswith(".wav"):
                        name += ".wav"
                    os.makedirs(node.audio_dir, exist_ok=True)
                    path = os.path.join(node.audio_dir, name)
                    open(path, "wb").write(raw)
                    try:
                        node.audio = Audio(path)
                    except Exception as e:
                        os.remove(path)
                        return self._json({"error": "not a usable WAV (16-bit PCM wanted): %s" % e}, 400)
                    return self._json({"ok": True, "audio": node.audio.name})
                body = json.loads(raw.decode() or "{}") if raw else {}
                if p == "/api/run":
                    if node.role != "customer":
                        raise ValueError("only the customer role starts tests")
                    return self._json({"ok": True, "run": node.start_run(body).to_dict()})
                if p == "/api/stop":
                    if node.run and node.run.state == "running":
                        node.run.stop.set()
                    with node.lock:
                        for c in node.calls.values():
                            c.abort = True
                    return self._json({"ok": True})
                if p == "/api/reset":
                    node.reset_history(keep_active=True)
                    return self._json({"ok": True})
                if p == "/api/settings":
                    update_settings(node, body)
                    return self._json({"ok": True, "cfg": node.cfg, "thresholds": node.thresholds})
                if p == "/api/audio/select":
                    name = body.get("name") or ""
                    if name == "__tonetest__":
                        node.audio = Audio("__tonetest__")
                    else:
                        node.audio = Audio(os.path.join(node.audio_dir, os.path.basename(name))) if name else Audio()
                    return self._json({"ok": True, "audio": node.audio.name})
                if p == "/api/analyze":
                    c = find_call(node, int(body.get("id", 0)))
                    if c is None:
                        raise ValueError("no such call")
                    return self._json({"ok": True, "tone": node.analyze_call(c)})
                if p == "/api/report/save":
                    return self._json({"ok": True, "file": node.save_report(node.run) + ".html"})
                self._json({"error": "not found"}, 404)
            except (ValueError, KeyError, TypeError) as e:
                self._json({"error": str(e)}, 400, cors=True)
            except Exception as e:
                self._json({"error": repr(e)}, 500, cors=True)

    class Srv(ThreadingHTTPServer):
        daemon_threads = True
        request_queue_size = 64

    try:
        srv = Srv((host, port), H)
    except OSError as e:
        log("cannot start dashboard on %s:%d: %s" % (host, port, e))
        return None
    threading.Thread(target=srv.serve_forever, daemon=True, name="web").start()
    shown = node.adv_ip if host in ("0.0.0.0", "") else host
    log("dashboard: http://%s:%d/   %s" % (shown, port, "login required (users in %s)" % auth.path if auth else "NO LOGIN (started with --users '')"))
    return srv


PAGE = r'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>sipload __ROLE__</title>
<style>
:root{--bg:#f4f5f8;--card:#fff;--ink:#1d2330;--mut:#667085;--line:#dfe3ea;--acc:#2456d6;--ok:#12803c;--bad:#c62828;--warn:#b26a00;--okbg:#e6f4ea;--badbg:#fdeaea;--warnbg:#fff4e0}
@media (prefers-color-scheme:dark){:root{--bg:#12151c;--card:#1b2029;--ink:#e6e9ef;--mut:#98a2b3;--line:#2c3340;--acc:#6f9bff;--ok:#4cc77a;--bad:#ff7b7b;--warn:#f0b04a;--okbg:#14301f;--badbg:#3a1a1a;--warnbg:#3a2c12}}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--ink);font:14px/1.4 system-ui,-apple-system,Segoe UI,sans-serif}
header{display:flex;flex-wrap:wrap;gap:12px;align-items:center;padding:10px 18px;background:var(--card);border-bottom:1px solid var(--line);position:sticky;top:0;z-index:5}
header h1{font-size:16px;margin:0}.badge{padding:2px 9px;border-radius:99px;font-size:12px;font-weight:600;background:var(--acc);color:#fff}
.sp{flex:1}label{display:flex;flex-direction:column;font-size:12px;color:var(--mut);gap:2px}
input,select,button,textarea{font:inherit;color:var(--ink);background:var(--card);border:1px solid var(--line);border-radius:6px;padding:6px 8px}
input[type=range]{padding:0;width:100%}input[type=checkbox]{width:auto}
button{cursor:pointer}button.pri{background:var(--acc);color:#fff;border-color:var(--acc);font-weight:600}button.red{background:var(--bad);color:#fff;border-color:var(--bad)}button:disabled{opacity:.45;cursor:default}
main{max-width:1300px;margin:0 auto;padding:16px}
.card{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:14px;margin-bottom:14px}
.card h2{font-size:13px;margin:0 0 10px;color:var(--mut);text-transform:uppercase;letter-spacing:.05em}
.tiles{display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:10px;margin-bottom:14px}
.tile{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:10px 12px}.tile b{display:block;font-size:22px}.tile span{font-size:12px;color:var(--mut)}
.grid{display:grid;grid-template-columns:minmax(320px,430px) 1fr;gap:14px;align-items:start}@media(max-width:900px){.grid{grid-template-columns:1fr}}
.row{display:flex;flex-wrap:wrap;gap:10px;margin-bottom:10px;align-items:flex-end}.row>label{flex:1;min-width:110px}
table{border-collapse:collapse;width:100%}th,td{text-align:left;padding:5px 8px;border-bottom:1px solid var(--line);font-size:13px;white-space:nowrap}th{color:var(--mut);font-weight:600;position:sticky;top:0;background:var(--card)}
tr.sel{outline:2px solid var(--acc)}tr.good td:nth-child(3){color:var(--ok)}tr.bad td:nth-child(3){color:var(--bad)}tr.flt td:first-child{border-left:3px solid var(--warn)}tbody tr{cursor:pointer}
.scroll{max-height:420px;overflow:auto}.mut{color:var(--mut)}.pill{display:inline-block;padding:1px 8px;border-radius:99px;font-size:12px;font-weight:600}
.pass{background:var(--okbg);color:var(--ok)}.fail{background:var(--badbg);color:var(--bad)}.info{background:var(--warnbg);color:var(--warn)}
.banner{display:flex;gap:14px;align-items:center;padding:12px 16px;border-radius:10px;margin-bottom:14px;font-weight:700;font-size:18px}
.banner.pass{background:var(--okbg);color:var(--ok)}.banner.fail{background:var(--badbg);color:var(--bad)}.banner.none{background:var(--card);color:var(--mut);border:1px solid var(--line)}
.checks{display:flex;flex-wrap:wrap;gap:6px;font-size:12px;font-weight:600}.checks span{padding:2px 8px;border-radius:99px}
canvas{width:100%;height:190px;display:block}.legend{display:flex;gap:14px;font-size:12px;color:var(--mut);margin-top:4px}.legend i{display:inline-block;width:10px;height:10px;border-radius:2px;margin-right:4px}
.faults{display:grid;grid-template-columns:1fr 1fr;gap:4px 10px}.faults label{flex-direction:row;align-items:center;gap:6px;color:var(--ink);font-size:13px}
.mixgrid{display:grid;grid-template-columns:1fr 70px 1fr 70px;gap:6px 10px;align-items:center}
.presets{display:flex;flex-wrap:wrap;gap:6px;margin-bottom:10px}.presets button{padding:3px 10px;font-size:13px}.chipbar{display:flex;flex-wrap:wrap;gap:6px;margin-bottom:10px}.chipbar button{padding:3px 10px;font-size:13px}
pre{background:var(--bg);padding:8px;border-radius:6px;overflow:auto;font-size:12px;max-height:240px;margin:4px 0}
#toast{position:fixed;bottom:18px;left:50%;transform:translateX(-50%);background:var(--ink);color:var(--bg);padding:9px 16px;border-radius:8px;display:none;z-index:9;max-width:80vw}
.tag{font-size:11px;color:var(--mut)}details summary{cursor:pointer;color:var(--mut);margin:4px 0}
</style></head><body>
<header><h1>sipload</h1><span class="badge">v__VERSION__</span><span class="badge">__ROLE__</span><span class="mut" id="hinfo"></span><span class="sp"></span>
<label title="Optional. Address of the OTHER tester's dashboard, so this page can show its summary too. Not a password.">Other tester's address (optional)<input id="peer" size="26" placeholder="http://192.0.2.10:8091"></label>
<label title="Only needed if the other tester was started with --peer-key.">Its key<input id="peerkey" size="8" type="password"></label><span class="mut" id="me"></span><button id="logout" style="padding:3px 10px">Log out</button></header>
<main>
<div id="banner" class="banner none">No results yet</div>
<div class="tiles" id="tiles"></div>
<div id="peerbox"></div>
<div class="grid">
 <div><div class="card" id="controls"></div></div>
 <div>
  <div class="card"><h2>Calls over time</h2><canvas id="chart"></canvas>
   <div class="legend"><span><i style="background:var(--acc)"></i>calls in progress</span><span><i style="background:var(--ok)"></i>talking</span><span><i style="background:var(--bad)"></i>failed (total)</span></div></div>
  <div class="card"><h2>Pass / fail checks</h2><div id="checks" class="checks"></div><div id="codes" class="mut" style="margin-top:8px"></div></div>
 </div>
</div>
<div class="card"><h2>Calls <span class="tag" id="ccount"></span></h2>
 <div class="row" style="margin-bottom:6px"><label style="max-width:170px">Show<select id="flt"><option value="all">All calls</option><option value="active">In progress</option><option value="bad">Problems only</option><option value="worst">Worst quality first</option></select></label>
  <span class="sp"></span><a id="rhtml" target="_blank">Report</a><a id="rcsv">CSV</a><a id="rjson" target="_blank">JSON</a><button id="rsave">Save report on this machine</button><button id="rlist">Saved reports</button></div><div id="saved" class="card" style="display:none"></div>
 <div class="scroll"><table><thead><tr><th>#</th><th>Dialed number</th><th>From</th><th>State / result</th><th>Code</th><th>Secs</th><th>PDD ms</th><th>Loss %</th><th>Jitter ms</th><th>MOS</th><th>Tone</th><th>Codec</th><th>RTT ms</th><th>Audio</th><th>Fault / action</th><th></th></tr></thead><tbody id="rows"></tbody></table></div>
</div>
<div class="card" id="detail" style="display:none"></div>
</main><div id="toast"></div>
<script>
const ROLE="__ROLE__";
const $=s=>document.querySelector(s);
const esc=s=>String(s==null?"":s).replace(/[&<>"]/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"}[c]));
let peerKey=localStorage.getItem("sl_peerkey")||"",S=null,sel=null,built=false,peerUrl=localStorage.getItem("sl_peer")||"",PS=null,L=null;
$("#peerkey").value=peerKey;$("#peer").value=peerUrl;
$("#peerkey").onchange=e=>{peerKey=e.target.value;localStorage.setItem("sl_peerkey",peerKey);PS=null;pollPeer()};
$("#logout").onclick=async()=>{await fetch("/api/logout",{method:"POST"});location.href="/login"};
$("#peer").onchange=e=>{peerUrl=e.target.value.trim().replace(/\/$/,"");localStorage.setItem("sl_peer",peerUrl);PS=null;pollPeer()};
function toast(m,bad){const t=$("#toast");t.textContent=m;t.style.background=bad?"var(--bad)":"var(--ink)";t.style.display="block";clearTimeout(toast.t);toast.t=setTimeout(()=>t.style.display="none",bad?6000:2500)}
async function api(path,body){const o={};if(body!==undefined){o.method="POST";o.body=body instanceof Blob?body:JSON.stringify(body)}
 const r=await fetch(path,o);let j={};try{j=await r.json()}catch(e){}if(r.status===401){location.href="/login";return j}if(!r.ok)throw new Error(j.error||r.statusText);return j}
function links(){$("#rhtml").href="/report";$("#rcsv").href="/report?fmt=csv";$("#rjson").href="/report?fmt=json"}links();
const fmt=(v,d)=>v==null?"-":(typeof v==="number"?(d==null?v:v.toFixed(d)):v);

/* ---------- controls ---------- */
function field(id,label,val,extra){return `<label>${label}<input id="${id}" value="${esc(val)}" ${extra||""}></label>`}
function buildControls(){
 const D=S.run_defaults,C=$("#controls");
 const audio=`<h2 style="margin-top:14px">Audio played on calls</h2><div class="row"><label>Now playing<select id="audsel"><option value="">built-in tone sequence</option><option value="__tonetest__" ${S.audio.kind==="tonetest"?"selected":""}>Tone test (DTMF + 1004 Hz, rated)</option>${S.audio.files.map(f=>`<option ${S.audio.name===f?"selected":""}>${esc(f)}</option>`).join("")}</select></label>
  <label>Upload a WAV<input type="file" id="audup" accept=".wav"></label></div><div class="tag">16-bit WAV; any sample rate is converted to 8 kHz mono. Both ends should play a file. To rate audio quality pick <b>Tone test</b> on BOTH ends: each end then compares what it received with the known signal (first calls only, see limit in README).</div>`;
 if(ROLE==="customer"){
  C.innerHTML=`<h2>Run a test</h2>
  <div class="presets"><button data-p="1">1 call</button><button data-p="5">5</button><button data-p="10">10</button><button data-p="25">25</button><button data-p="50">50</button><button data-p="100">100</button><button data-p="250">250</button><button data-p="500">500</button><button data-p="1000">1000 calls</button><button data-p="ladder">Ladder 10→100</button><button data-p="auth">Login-failure test</button></div>
  <div class="row"><label>Test type<select id="kind"><option value="batch">N calls at once (batch)</option><option value="steps">Ladder (steady load in steps)</option><option value="auth">Failed-login test (REGISTER)</option></select></label></div>
  <div class="row"><label>SBC address (host:port)<input id="target" value="${esc(D.target)}"></label></div>
  <div class="row">${field("auth_user","Auth username",D.auth_user)}<label>Auth password<input id="auth_pass" type="password" value=""></label></div>
  <div class="row"><label>What should the carrier do?<select id="plansel"><option value="">custom number range (below)</option>${(S.cfg.dialplan||[]).map((r,i)=>`<option value="${i}">${esc(r.prefix)}xxx - ${esc(r.name)}</option>`).join("")}</select></label>${field("profiles","Mix (optional), e.g. 9990=80,9997=20",D.profiles)}</div>
  <div class="tag">The number dialed tells the carrier what to do (see the carrier's dial plan). Any phone can use it too: dial 9992000 for an echo test.</div>
  <div class="row"><label>Number list (optional): one line per call - dial number[,calling number[,auth user,auth password]]<textarea id="list_csv" rows="3" style="width:100%" placeholder="9992001&#10;9992002,5551234&#10;9990001,5551234,myuser,mypass"></textarea></label></div>
  <div class="row"><label>Load a CSV file<input type="file" id="listfile" accept=".csv,.txt"></label>${field("dtmf","Send DTMF digits (RFC 2833) after answer, e.g. 123#",D.dtmf)}${field("dtmf_after","...after seconds",D.dtmf_after)}</div>
  <div class="row">${field("cid","Contact ID alarm test: account event group zone, e.g. 1234 1130 01 001 (empty = normal calls)",D.cid)}${field("cid_count","Messages per call (1-5)",D.cid_count)}<label>Contact ID fault<select id="cid_fault"><option value="">none (valid message)</option><option value="badsum">wrong check digit</option><option value="short">15 digits only</option></select></label></div>
  <div class="tag">Contact ID: the call acts as an alarm panel. Dial 9980xxx on a sipload carrier (handshake, 16 digits, check digit, kiss-off). 9981xxx never sends the handshake, 9982xxx never sends the kiss-off: those are meant to fail. G.711 only.</div>
  <div class="tag">With a number list the numbers are used in turn (the From user and "Dial numbers" range are ignored). Dial 9992xxx (echo) and the digits must come back; the carrier shows what DTMF it received.</div>
  <div class="row">${field("from_user","Calling number (From)",D.from_user)}${field("callee_start","Dial numbers: from",D.callee_start)}${field("callee_end","Dial numbers: to",D.callee_end)}</div>
  <div id="p_batch"><div class="row"><label>Number of calls: <b id="callsv">10</b><input type="range" id="calls" min="1" max="1000" value="10"></label></div>
   <div class="row">${field("cps","New calls per second",D.cps)}${field("hold_min","Shortest call (seconds)",D.hold_min)}${field("hold_max","Longest call (seconds)",D.hold_max)}</div><div class="tag">Each call lasts a random time between the shortest and longest. Use the same number for both to make every call the same length.</div></div>
  <div id="p_steps" style="display:none"><div class="row"><label>Steps: calls x seconds, comma separated<input id="steps" value="${D.steps.map(s=>s[0]+"x"+s[1]).join(",")}"></label></div>
   <div class="row">${field("cps2","New calls per second",D.cps)}${field("hold_min2","Shortest call (seconds)",D.hold_min)}${field("hold_max2","Longest call (seconds)",D.hold_max)}</div></div>
  <div id="p_auth" style="display:none"><div class="row">${field("auth_count","Attempts",D.auth_count)}${field("auth_per_min","Per minute",D.auth_per_min)}<label>Usernames<select id="auth_users"><option value="random">random unknown (scanner)</option><option value="fixed">the auth username, wrong password</option></select></label></div>
   <div class="tag">Sends REGISTERs that fail. Use it to watch the SBC's auth log and any auto-ban tool. Run it from an address that is not whitelisted.</div></div>
  <div class="row"><label>Codecs to offer, in order (the carrier uses the first one it supports)<input id="codecs" size="34" value="PCMU"></label></div><div class="chipbar" id="chips"></div>
  <div class="tag">Click a codec to add or remove it. Only PCMU and PCMA carry real audio (listen, tone score); the others send correctly sized dummy audio, so they test negotiation, transcoding load, loss and jitter.</div>
  <details><summary>Simulate problems (fault injection)</summary>
   <div class="row"><label>Share of calls affected: <b id="fpv">0</b>%<input type="range" id="fault_pct" min="0" max="100" value="0"></label></div>
   <div class="faults">${Object.keys(S.faults).map(k=>`<label title="${esc(S.fault_help[k])}"><input type="checkbox" class="fault" value="${k}">${esc(S.faults[k])}</label>`).join("")}</div>
   <div class="tag">Hover a choice for what you should see. Calls with a fault are reported separately and do not count against the pass/fail checks.</div></details>
  <details><summary>Pass / fail limits</summary><div class="row">${field("t_min_asr","Min answer rate %",S.thresholds.min_asr)}${field("t_max_pdd_ms","Max PDD p95 ms",S.thresholds.max_pdd_ms)}${field("t_min_mos","Min MOS",S.thresholds.min_mos)}${field("t_min_tone","Min tone score",S.thresholds.min_tone)}${field("t_max_loss_pct","Max loss %",S.thresholds.max_loss_pct)}${field("t_max_jitter_ms","Max jitter ms",S.thresholds.max_jitter_ms)}</div></details>
  <div class="row" style="margin-top:12px"><button class="pri" id="start">Start test</button><button class="red" id="stop">Stop</button><button id="reset">Clear results</button></div>
  <div id="runline" class="mut"></div>`+audio;
  const upd=()=>{["batch","steps","auth"].forEach(k=>$("#p_"+k).style.display=$("#kind").value===k?"":"none")};
  $("#plansel").onchange=e=>{const r=(S.cfg.dialplan||[])[e.target.value];if(r){$("#callee_start").value=r.prefix+"001";$("#callee_end").value=r.prefix+"100";$("#profiles").value="";if(/Contact ID/.test(r.name)&&!$("#cid").value)$("#cid").value="1234 1602 00 000"}};
  chips();
  $("#listfile").onchange=e=>{const f=e.target.files[0];if(!f)return;const r=new FileReader();r.onload=()=>{$("#list_csv").value=r.result;toast("Loaded "+f.name)};r.readAsText(f)};
  $("#kind").onchange=upd;$("#calls").oninput=e=>$("#callsv").textContent=e.target.value;$("#fault_pct").oninput=e=>$("#fpv").textContent=e.target.value;
  C.querySelectorAll(".presets button").forEach(b=>b.onclick=()=>{const p=b.dataset.p;
   if(p==="ladder"){$("#kind").value="steps"}else if(p==="auth"){$("#kind").value="auth"}else{$("#kind").value="batch";$("#calls").value=p;$("#callsv").textContent=p;$("#cps").value=Math.max(1,Math.min(20,Math.round(p/5)))}upd()});
  $("#start").onclick=async()=>{
   const k=$("#kind").value,p={kind:k,target:$("#target").value,auth_user:$("#auth_user").value,auth_pass:$("#auth_pass").value,from_user:$("#from_user").value,callee_start:$("#callee_start").value,callee_end:$("#callee_end").value,list_csv:$("#list_csv").value,dtmf:$("#dtmf").value.trim(),cid:$("#cid").value.trim(),cid_fault:$("#cid_fault").value,cid_count:+$("#cid_count").value||1,dtmf_after:+$("#dtmf_after").value||0,profiles:$("#profiles").value.trim(),
    codecs:$("#codecs").value.split(","),faults:[...document.querySelectorAll(".fault:checked")].map(x=>x.value),fault_pct:+$("#fault_pct").value};
   if(k==="batch"){p.calls=+$("#calls").value;p.cps=+$("#cps").value;p.hold_min=+$("#hold_min").value;p.hold_max=+$("#hold_max").value}
   if(k==="steps"){p.steps=$("#steps").value.split(",").map(s=>s.trim().split("x").map(Number)).filter(a=>a.length===2&&a[0]>0&&a[1]>0);p.cps=+$("#cps2").value;p.hold_min=+$("#hold_min2").value;p.hold_max=+$("#hold_max2").value}
   if(k==="auth"){p.auth_count=+$("#auth_count").value;p.auth_per_min=+$("#auth_per_min").value;p.auth_users=$("#auth_users").value}
   try{await api("/api/settings",{thresholds:{min_asr:+$("#t_min_asr").value,max_pdd_ms:+$("#t_max_pdd_ms").value,min_mos:+$("#t_min_mos").value,min_tone:+$("#t_min_tone").value,max_loss_pct:+$("#t_max_loss_pct").value,max_jitter_ms:+$("#t_max_jitter_ms").value}});
    await api("/api/run",p);toast("Test started")}catch(e){toast(e.message,1)}};
 }else{
  const m=S.cfg.mix,names={answer:"Answer",busy:"486 Busy",notfound:"404 Not found",unavail:"503 Unavailable",servererr:"500 Server error",forbidden:"403 Forbidden",decline:"603 Decline",temp:"480 Temp. unavailable",redirect:"302 Redirect",badmedia:"488 Not acceptable",noanswer:"Ring, never answer",timeout:"Say nothing (dead)"};
  const dp=`<label class="chk"><input type="checkbox" id="dialplan_on" ${S.cfg.dialplan_on?"checked":""}> Dial plan on: the number dialed decides what happens (overrides the reply mix below for matching numbers)</label>
   <details open><summary>Dial plan</summary><table><thead><tr><th>Number starts with</th><th>Behaviour</th><th>Audio</th></tr></thead><tbody>${(S.cfg.dialplan||[]).map(r=>`<tr><td>${esc(r.prefix)}</td><td>${esc(r.name)}</td><td>${esc(r.audio||"")}</td></tr>`).join("")}</tbody></table></details>`;
  C.innerHTML=`<h2>How this carrier behaves</h2>${dp}<div class="tag" style="margin-bottom:8px">Changes apply to the next call. Numbers are relative weights.</div>
  <div class="mixgrid">${Object.keys(m).map(k=>`<span>${names[k]}</span><input class="mix" data-k="${k}" type="number" min="0" value="${m[k]}">`).join("")}</div>
  <div class="row" style="margin-top:12px">${field("ring_ms","Ring time ms",S.cfg.ring_ms)}${field("delay_min_ms","Extra answer delay min ms",S.cfg.delay_min_ms)}${field("delay_max_ms","max ms",S.cfg.delay_max_ms)}</div>
  <div class="row"><label>Audio problem<select id="rtp_mode"><option value="normal">none, audio normal</option><option value="none">never send audio</option><option value="blackhole">tell caller a wrong audio port</option><option value="private_ip">tell caller a private audio IP</option></select></label>${field("loss_pct","Drop % of audio",S.cfg.loss_pct)}${field("hangup_after","We hang up after (s, 0=never)",S.cfg.hangup_after)}</div>
  <div class="row"><label><span><input type="checkbox" id="early_media"> send early media (183)</span></label><label>Codecs we accept<input id="codecs" size="40"></label></div><div class="chipbar" id="chips"></div>
  <div class="row">${field("auth_user","Require auth: username (blank = none)",S.cfg.auth_user)}<label>password<input id="auth_pass" type="password" value=""></label></div>
  <div class="row"><button class="pri" id="apply">Apply</button><button id="reset">Clear results</button></div>`+audio;
  $("#rtp_mode").value=S.cfg.rtp_mode;$("#early_media").checked=S.cfg.early_media;$("#codecs").value=S.cfg.codecs.join(",");chips();
  $("#apply").onclick=async()=>{const mix={};document.querySelectorAll(".mix").forEach(i=>mix[i.dataset.k]=+i.value||0);
   try{await api("/api/settings",{cfg:{mix,dialplan_on:$("#dialplan_on").checked,ring_ms:+$("#ring_ms").value,delay_min_ms:+$("#delay_min_ms").value,delay_max_ms:+$("#delay_max_ms").value,rtp_mode:$("#rtp_mode").value,loss_pct:+$("#loss_pct").value,hangup_after:+$("#hangup_after").value,early_media:$("#early_media").checked,codecs:$("#codecs").value.split(","),auth_user:$("#auth_user").value,auth_pass:$("#auth_pass").value}});toast("Applied")}catch(e){toast(e.message,1)}};
 }
 if($("#stop"))$("#stop").onclick=()=>api("/api/stop",{}).then(()=>toast("Stopping...")).catch(e=>toast(e.message,1));
 $("#reset").onclick=()=>api("/api/reset",{}).then(()=>{sel=null;toast("Cleared")}).catch(e=>toast(e.message,1));
 $("#audsel").onchange=e=>api("/api/audio/select",{name:e.target.value}).then(j=>toast("Audio: "+j.audio)).catch(x=>toast(x.message,1));
 $("#audup").onchange=async e=>{const f=e.target.files[0];if(!f)return;try{const j=await api("/api/audio?name="+encodeURIComponent(f.name),f);toast("Audio: "+j.audio);S.audio.files.push(f.name);const o=document.createElement("option");o.textContent=f.name;o.selected=true;$("#audsel").appendChild(o)}catch(x){toast(x.message,1)}};
 async function showSaved(){const j=await (await fetch("/api/reports")).json(),B=$("#saved");B.style.display="";
  B.innerHTML=`<b>Saved reports</b> <span class="mut">(folder on this machine: ${esc(j.dir)})</span> <a href="#" id="sclose" style="float:right">close</a>`+(j.reports.length?`<table><thead><tr><th>Saved</th><th>Result</th><th>Report</th><th>CSV</th><th>JSON</th></tr></thead><tbody>${j.reports.map(r=>{const b=r.name.replace(/\.html$/,"");return `<tr><td>${esc(r.time)}</td><td>${esc(r.verdict||"")}</td><td><a target="_blank" href="/saved/${encodeURIComponent(r.name)}">${esc(r.name)}</a></td><td><a href="/saved/${encodeURIComponent(b+".csv")}">csv</a></td><td><a target="_blank" href="/saved/${encodeURIComponent(b+".json")}">json</a></td></tr>`}).join("")}</tbody></table>`:`<div class="mut">No saved reports yet. Press "Save report on this machine" after a test.</div>`);
  $("#sclose").onclick=e=>{e.preventDefault();B.style.display="none"}}
 $("#rlist").onclick=()=>showSaved().catch(e=>toast(e.message,1));
 $("#rsave").onclick=()=>api("/api/report/save",{}).then(j=>{toast("Saved "+j.file);showSaved()}).catch(e=>toast(e.message,1));
 built=true;
}

/* ---------- live view ---------- */
function tiles(){const s=S.summary,r=[["In progress",S.active.length],["Peak",s.peak_concurrent],["Calls done",s.calls_total],["Answered",s.answered],["Answer rate",s.asr_pct==null?"-":s.asr_pct+"%"],
 ["PDD p95",s.pdd_p95==null?"-":s.pdd_p95+" ms"],["Loss avg",s.loss_avg==null?"-":s.loss_avg+"%"],["Jitter p95",s.jitter_p95==null?"-":s.jitter_p95+" ms"],["MOS avg",s.mos_avg==null?"-":s.mos_avg],...(s.tone_calls?[["Tone score",s.tone_avg+" (min "+s.tone_min+")"]]:[]),["Dropped",s.dropped+s.no_ack]];
 $("#tiles").innerHTML=r.map(x=>`<div class="tile"><b>${esc(x[1])}</b><span>${x[0]}</span></div>`).join("")}
function banner(){const s=S.summary,b=$("#banner"),o=s.overall;b.className="banner "+(o==="PASS"?"pass":o==="FAIL"?"fail":"none");
 b.textContent=o==="NO DATA"?(S.active.length?"Calls in progress - results appear as calls finish":"No results yet - start a test or send calls"):("Overall: "+o+(S.run?"   ("+S.run.state+(S.run.note?", "+S.run.note:"")+")":""));
 $("#checks").innerHTML=s.verdict.map(v=>`<span class="${v.status==="PASS"?"pass":"fail"}" title="rule ${esc(v.rule)}">${v.status} ${esc(v.name)}: ${esc(v.value)}</span>`).join("")||'<span class="mut">no checks yet</span>';
 $("#codes").innerHTML="SIP final codes: "+(Object.entries(s.codes).map(([k,v])=>k+" ×"+v).join(", ")||"none")+" &nbsp;|&nbsp; results: "+(Object.entries(s.results).map(([k,v])=>k+" ×"+v).join(", ")||"none")+
  `<br>tester: RTP timer lag ${S.rtp.lag_ms} ms, SIP retransmits ${S.sip.retx}`;
 $("#hinfo").textContent=`${S.ip}:${S.sip_port}  ·  audio: ${S.audio.name} (${S.audio.seconds}s)  ·  up ${Math.round(S.uptime/60)} min`;
 const rl=$("#runline");if(rl&&S.run)rl.textContent=`Run ${S.run.id}: ${S.run.state}, ${S.run.launched} launched${S.run.note?" - "+S.run.note:""}`;
 const run=S.run&&S.run.state==="running";if($("#start")){$("#start").disabled=run;$("#stop").disabled=!run}}
function chart(){const c=$("#chart"),dpr=window.devicePixelRatio||1,w=c.clientWidth,h=c.clientHeight;c.width=w*dpr;c.height=h*dpr;const x=c.getContext("2d");x.scale(dpr,dpr);x.clearRect(0,0,w,h);
 const d=S.series;if(d.length<2){x.fillStyle="#888";x.fillText("waiting for data...",10,20);return}
 const css=getComputedStyle(document.documentElement),mx=Math.max(5,...d.map(p=>Math.max(p[1],p[2],p[4])))*1.1,pad=28,t0=d[0][0],t1=d[d.length-1][0]||t0+1;
 x.strokeStyle=css.getPropertyValue("--line");x.fillStyle=css.getPropertyValue("--mut");x.font="11px system-ui";
 for(let i=0;i<=4;i++){const y=h-18-(h-26)*i/4;x.beginPath();x.moveTo(pad,y);x.lineTo(w-4,y);x.stroke();x.fillText(Math.round(mx*i/4),2,y+4)}
 const line=(k,col)=>{x.strokeStyle=css.getPropertyValue(col);x.lineWidth=2;x.beginPath();d.forEach((p,i)=>{const px=pad+(w-pad-4)*(p[0]-t0)/Math.max(1,t1-t0),py=h-18-(h-26)*p[k]/mx;i?x.lineTo(px,py):x.moveTo(px,py)});x.stroke()};
 line(1,"--acc");line(2,"--ok");line(4,"--bad");x.fillStyle=css.getPropertyValue("--mut");x.fillText(Math.round((t1-t0)/60*10)/10+" min window",w-90,h-3)}
function rows(){const all=[...S.active.slice().reverse(),...S.finished.slice().reverse()];let l=all;
 if(flt.value==="worst")l=all.filter(c=>c.answered&&!c.fault&&c.mos!=null).sort((a,b)=>a.mos-b.mos||(a.tone==null?9:a.tone)-(b.tone==null?9:b.tone)).slice(0,20);else if(flt.value==="active")l=S.active.slice().reverse();else if(flt.value==="bad")l=all.filter(c=>c.fault||["failed","dropped","no_ack","timeout","error"].includes(c.result)||(c.answered&&c.audio_ok===false));
 $("#ccount").textContent=`${S.active.length} active, ${S.finished.length} recent`;
 const html=l.slice(0,400).map(c=>{const bad=["failed","dropped","no_ack","timeout","error"].includes(c.result),good=c.result==="completed"||c.result==="accepted";
  const st=c.result?c.result:c.state;const act=c.live&&c.rx>=0?`<button data-l="${c.id}">▶ Listen</button>`:(c.rx>0?`<button data-w="${c.id}">▶ Play</button>`:"");
  return `<tr data-id="${c.id}" class="${bad?"bad":good?"good":""} ${c.fault?"flt":""} ${sel===c.id?"sel":""}"><td>${c.id}</td><td>${esc(c.number)}</td><td>${esc(c.caller||"")}</td><td>${esc(st)}${c.method==="REGISTER"?" (REG)":""}</td><td>${c.code||""}</td><td>${c.dur}</td><td>${fmt(c.pdd_ms)}</td><td>${fmt(c.loss)}</td><td>${fmt(c.jitter)}</td><td>${fmt(c.mos)}</td><td>${c.tone_err?"<b style='color:var(--bad)'>no tone</b>":(c.tone==null?"":c.tone)}</td><td>${esc(c.codec||"")}</td><td>${fmt(c.rtt)}</td><td>${c.audio_ok==null?"":c.audio_ok?"yes":"<b style='color:var(--bad)'>none</b>"}</td><td>${esc(c.fault||c.action||"")}</td><td>${act}</td></tr>`}).join("");
 if(html!==window._rowsHtml){window._rowsHtml=html;$("#rows").innerHTML=html}}
const flt=$("#flt");flt.onchange=()=>S&&rows();
$("#rows").onclick=e=>{const b=e.target.closest("button");if(b){e.stopPropagation();if(b.dataset.l)listen(+b.dataset.l);else if(b.dataset.w)play(+b.dataset.w);return}
 };
// select on mouse-down: the table is redrawn every second, which can swallow a normal click
$("#rows").addEventListener("mousedown",e=>{if(e.target.closest("button")||e.target.closest("a"))return;const tr=e.target.closest("tr");
 if(tr&&tr.dataset.id){sel=+tr.dataset.id;showDetail().then(()=>{const d=$("#detail");if(d&&d.scrollIntoView)d.scrollIntoView({behavior:"smooth",block:"start"})})}});
function toneBox(c){const t=c.tone_detail;
 if(!t){return (c.rx>0&&S.audio.kind==="tonetest")?`<div class="row"><button data-a="${c.id}">Analyse tone test</button></div>`:""}
 if(t.error)return `<div class="tag">Tone test: ${esc(t.error)} (score ${fmt(t.score)})</div>`;
 return `<div class="row"><span class="pill ${t.score>=4?"pass":t.score>=3?"info":"fail"}">Tone score ${t.score} / 4.5</span><span>SNR ${fmt(t.snr_db)} dB</span><span>level error ${fmt(t.level_db)} dB</span><span>frequency error ${fmt(t.freq_hz)} Hz</span><span>digits ok ${fmt(t.digits_pct)}% (missing ${t.digits_missing}, wrong ${t.digits_wrong})</span><span>dropouts ${t.dropout_ms} ms</span><span>noise floor ${fmt(t.noise_floor_dbfs)} dBFS</span></div>`}
function callerBox(c){const i=c.callerinfo;if(!i||c.dir!=="in")return "";
 const id=(i.identity||[]).filter(x=>x.ok_format)[0];
 return `<h2>Caller ID and STIR/SHAKEN (as received)</h2><div class="row"><span><b>From</b> ${esc(i.from)}</span><span><b>P-Asserted-Identity</b> ${esc((i.pai||[]).join(", ")||"none")}</span>${i.ppi?`<span><b>P-Preferred</b> ${esc(i.ppi)}</span>`:""}${i.rpid?`<span><b>Remote-Party-ID</b> ${esc(i.rpid)}</span>`:""}</div>
 <div class="row"><span><b>STIR/SHAKEN</b> <span class="badge ${i.attest==="A"?"pass":i.attest?"":"fail"}">${esc(i.stir)}</span></span>${i.verstat?`<span><b>verstat</b> ${esc(i.verstat)}</span>`:""}</div>
 ${id?`<div class="row"><span><b>Attestation</b> ${esc(id.attest)}</span><span><b>Signed from (orig)</b> ${esc(id.orig)}</span><span><b>Signed to (dest)</b> ${esc((id.dest||[]).join(", "))}</span><span><b>Signed</b> ${id.age_s==null?"-":id.age_s+" s before the call"}</span><span><b>Algorithm</b> ${esc(id.alg||"-")} / ${esc(id.ppt||"-")}</span><span><b>Certificate</b> ${esc(id.info||(id.header&&id.header.x5u)||"-")}</span></div>`:""}
 ${i.gate&&i.gate.required?`<div class="row"><span><b>Password gate</b> <span class="badge ${i.gate.result==="accepted"?"pass":"fail"}">${esc(i.gate.result)}</span></span></div>`:""}<div class="tag">${esc(i.note)}</div>`}
function cidBox(c){const i=c.cid;if(!i)return "";const ok=i.ok;
 const rows=i.role==="panel"?`<span><b>Sent</b> ${esc(i.sent)}</span><span><b>Messages accepted</b> ${i.msgs}/${i.count||1}</span><span><b>Tries</b> ${i.tries}</span><span><b>Handshake heard after</b> ${i.hs_ms==null?"-":i.hs_ms+" ms ("+i.hs_len+" ms long)"}</span><span><b>Kiss-off</b> ${i.kiss_ms==null?"none":i.kiss_ms+" ms"}</span><span><b>Total</b> ${i.total_ms==null?"-":i.total_ms+" ms"}</span>`
  :`<span><b>Messages accepted</b> ${(i.messages||[]).length}</span><span><b>Digits received</b> ${esc((i.messages&&i.messages.length>1)?i.messages.join(" , "):(i.digits||"-"))}</span><span><b>Tries</b> ${i.tries}</span>${i.account?`<span><b>Account</b> ${esc(i.account)}</span><span><b>Event</b> ${esc(i.event)} ${esc(i.event_name)} (${esc(i.qualifier)})</span><span><b>Group/zone</b> ${esc(i.group)}/${esc(i.zone)}</span>`:""}`;
 return `<h2>Contact ID (${i.role==="panel"?"alarm panel":"receiver"}) - <span class="badge ${ok?"pass":"fail"}">${ok?"message accepted, kiss-off heard":"FAILED"}</span></h2><div class="row">${rows}</div>${i.why?`<div class="tag">${esc(i.why)}</div>`:""}`}
function chips(){const B=$("#chips");if(!B)return;const inp=$("#codecs");
 const cur=()=>inp.value.split(",").map(x=>x.trim().toUpperCase()).filter(Boolean);
 const draw=()=>{B.innerHTML=S.codec_list.map(c=>`<button type="button" data-c="${c}" style="${cur().includes(c)?"background:var(--acc);color:#fff":""}">${c}</button>`).join("");
  B.querySelectorAll("button").forEach(b=>b.onclick=()=>{let l=cur();l=l.includes(b.dataset.c)?l.filter(x=>x!==b.dataset.c):l.concat(b.dataset.c);inp.value=l.join(",");draw()})};
 inp.oninput=draw;draw()}
async function showDetail(){if(sel==null)return;try{const c=await (await fetch("/api/call/"+sel)).json();const D=$("#detail");D.style.display="";
 const s=c.stats||{};D.innerHTML=`<h2>Call ${c.id} - dialed ${esc(c.number)} from ${esc(c.caller||"?")} - ${esc(c.result||c.state)} ${c.code||""} ${esc(c.reason)}</h2>
  <div class="row"><span><b>Peer</b> ${esc(c.peer)}</span><span><b>Fault</b> ${esc(c.fault||"none")}</span><span><b>Hung up by</b> ${esc(c.hungup_by||"-")}</span><span><b>Setup</b> ${fmt(c.setup_ms)} ms</span><span><b>Retransmits</b> ${c.retx}</span>
  <span><b>Codec</b> ${esc(s.rx_codec||"-")}</span>${s.dtmf?`<span><b>DTMF received (RFC 2833)</b> ${esc(s.dtmf)}${c.dtmf_expect?(s.dtmf===c.dtmf_expect?" ✓":" ✗ expected "+esc(c.dtmf_expect)):""}</span>`:""}<span><b>Round trip</b> ${s.rtt_ms==null?"-":s.rtt_ms+" ms (min "+s.rtt_min+", max "+s.rtt_max+")"}</span>
  <span><b>Audio</b> rx ${s.rx_packets||0}/${s.rx_expected||0} pkts, loss ${fmt(s.loss_pct)}%, jitter ${fmt(s.jitter_ms)} ms, MOS ${fmt(s.mos)}, codec ${esc(s.rx_codec||"-")}, bit-exact ${fmt(s.exact_pct)}%</span></div>
  ${toneBox(c)}${cidBox(c)}${callerBox(c)}
  ${c.expect?`<div class="tag">Expected with this fault: ${esc(c.expect)}</div>`:""}
  <div class="row">${c.live?`<button data-l="${c.id}">▶ Listen live</button>`:""}${(c.rx>0)?`<button data-w="${c.id}">▶ Play recording (both sides)</button><a href="/audio/${c.id}.wav?mode=mix&dl=1" download>download both sides (mixed)</a> <a href="/audio/${c.id}.wav?mode=stereo&dl=1" download>stereo (left = heard, right = sent)</a> <a href="/audio/${c.id}.wav?dl=1" download>heard only</a>`:""}<button id="stoplisten" style="display:none">■ Stop</button><audio id="aud" controls style="display:none"></audio></div>
  <h2>SIP messages</h2>${(c.trace||[]).map(t=>`<details><summary>${t[0].toFixed(3)} s &nbsp; ${t[1]==="tx"?"→ sent":"← received"} &nbsp; <b>${esc(t[2].split("\r\n")[0])}</b></summary><pre>${esc(t[2])}</pre></details>`).join("")}`;
 D.querySelectorAll("button[data-a]").forEach(b=>b.onclick=async()=>{try{await api("/api/analyze",{id:+b.dataset.a});showDetail()}catch(x){toast(x.message,1)}});D.querySelectorAll("button[data-l]").forEach(b=>b.onclick=()=>listen(+b.dataset.l));D.querySelectorAll("button[data-w]").forEach(b=>b.onclick=()=>play(+b.dataset.w))}catch(e){}}
function stopListen(){if(L){try{L.ctl.abort();L.ctx.close()}catch(e){}L=null}const a=$("#aud");if(a){a.pause()}const b=$("#stoplisten");if(b)b.style.display="none"}
async function play(id){stopListen();const a=$("#aud");if(!a){sel=id;await showDetail()}const el=$("#aud");el.style.display="";el.src="/audio/"+id+".wav?mode=mix&_="+Date.now();el.play().catch(()=>{})}
async function listen(id){stopListen();if(sel!==id){sel=id;await showDetail()}
 const ctx=new (window.AudioContext||window.webkitAudioContext)(),ctl=new AbortController();L={ctx,ctl};const sb=$("#stoplisten");if(sb){sb.style.display="";sb.onclick=stopListen}
 try{const r=await fetch("/listen/"+id,{signal:ctl.signal});if(!r.ok){const j=await r.json().catch(()=>({}));throw new Error(j.error||"cannot listen")}
  toast("Listening live to call "+id);const rd=r.body.getReader();let carry=new Uint8Array(0),t=ctx.currentTime+0.6;
  for(;;){const {done,value}=await rd.read();if(done)break;const b=new Uint8Array(carry.length+value.length);b.set(carry);b.set(value,carry.length);const n=b.length>>1;carry=b.slice(n*2);if(!n)continue;
   const dv=new DataView(b.buffer,0,n*2),f=new Float32Array(n);for(let i=0;i<n;i++)f[i]=dv.getInt16(i*2,true)/32768;
   const buf=ctx.createBuffer(1,n,8000);buf.copyToChannel(f,0);const src=ctx.createBufferSource();src.buffer=buf;src.connect(ctx.destination);if(t<ctx.currentTime+0.05)t=ctx.currentTime+0.4;src.start(t);t+=buf.duration}
  toast("Call ended")}catch(e){if(e.name!=="AbortError")toast(e.message,1)}stopListen()}

/* ---------- peer ---------- */
async function pollPeer(){const box=$("#peerbox");if(!peerUrl){box.innerHTML="";return}
 try{const r=await fetch(peerUrl+"/api/state"+(peerKey?"?key="+encodeURIComponent(peerKey):""));if(r.status===401){box.innerHTML=`<div class="card"><span class="mut">Other tester needs its key (box at the top right)</span></div>`;PS=null;return}PS=await r.json()}catch(e){PS=null;box.innerHTML=`<div class="card"><span class="mut">Peer ${esc(peerUrl)} not reachable</span></div>`;return}
 const s=PS.summary;const mism=S&&S.audio.kind!==PS.audio.kind&&!(PS.cfg&&PS.cfg.dialplan_on);box.innerHTML=(mism?`<div class="banner fail" style="display:block;margin-bottom:6px">Audio mismatch: this end plays "${esc(S.audio.name)}" but the other end plays "${esc(PS.audio.name)}". The tone test only works when BOTH ends are set to Tone test.</div>`:"")+`<div class="card"><div class="row" style="margin:0"><b>Other end: ${esc(PS.role)}</b><span>${esc(PS.ip)}:${PS.sip_port}</span><span>in progress <b>${PS.active.length}</b></span><span>done <b>${s.calls_total}</b></span><span>answered <b>${s.answered}</b></span>
  <span>loss ${fmt(s.loss_avg)}%</span><span>jitter p95 ${fmt(s.jitter_p95)} ms</span><span>MOS ${fmt(s.mos_avg)}</span><span class="pill ${s.overall==="PASS"?"pass":s.overall==="FAIL"?"fail":"info"}">${esc(s.overall)}</span><a href="${esc(peerUrl)}/" target="_blank">open its dashboard</a></div>${(s.verdict||[]).filter(v=>v.status==="FAIL").map(v=>`<div style="color:var(--bad);margin-top:4px">FAIL on ${esc(PS.role)}: ${esc(v.name)} = ${esc(v.value)} (rule ${esc(v.rule)})</div>`).join("")}</div>`}

async function tick(){try{const rr=await fetch("/api/state");if(rr.status===401){location.href="/login";return}S=await rr.json();if(S.me)$("#me").textContent=S.me.user+" ("+S.me.role+")"}catch(e){$("#banner").className="banner fail";$("#banner").textContent="Lost contact with sipload";return}
 if(!built)buildControls();tiles();banner();chart();rows();
 if(sel!=null){const c=S.active.concat(S.finished).find(x=>x.id===sel);const sig=c?sel+"|"+c.state+"|"+c.result+"|"+(c.rx>0)+"|"+c.tone:"";if(sig!==tick.sig){tick.sig=sig;if(!L)showDetail()}}}
tick();setInterval(tick,1500);pollPeer();setInterval(pollPeer,2500);
</script></body></html>'''


# ------------------------------------------------------------------ command line
def build_parser():
    ap = argparse.ArgumentParser(prog="sipload", description="SIP / RTP load and fault tester (carrier and customer roles)")
    ap.add_argument("--version", action="version", version="sipload " + VERSION)
    sub = ap.add_subparsers(dest="cmd", required=True)

    def common(p, web_default):
        p.add_argument("--bind", default="0.0.0.0", help="local IP for SIP and RTP (default all)")
        p.add_argument("--advertise-ip", default="", help="IP to put in SIP and SDP (default: auto-detect)")
        p.add_argument("--sip-port", type=int, default=5060)
        p.add_argument("--rtp-min", type=int, default=20000)
        p.add_argument("--rtp-max", type=int, default=29998)
        p.add_argument("--audio", default="", help="WAV file to play, or 'tonetest' for the DTMF + 1004 Hz fidelity test (default: built-in tones)")
        p.add_argument("--dialplan", default="", help="JSON file with your own dial plan (number prefix -> carrier behaviour); see README")
        p.add_argument("--readback-password", default="", help="carrier: dialing 9989xxx plays a restricted-number message until this keypad password (keys 0-9 * # A-D) is entered (default empty = no password; set your own to require one)")
        p.add_argument("--tone-limit", type=int, default=5000, help="analyse the tone test on at most this many calls per test")
        p.add_argument("--audio-dir", default="audio", help="folder for uploaded WAV files")
        p.add_argument("--record-seconds", type=int, default=30, help="seconds of received audio kept per call for playback")
        p.add_argument("--web", default=web_default, help="dashboard address host:port, or 'off'")
        p.add_argument("--users", default="", help="turn on the login page: users file, e.g. users.json (created on first start with an 'admin' user). Default: no login - keep the dashboard on a private network")
        p.add_argument("--peer-key", default="", help="key the other tester (or Prometheus) can use to read /api/state and /metrics without logging in")
        p.add_argument("--out", default="sipload-reports", help="folder for saved reports ('' = do not save)")

    c = sub.add_parser("carrier", help="answer calls like an upstream carrier")
    common(c, "0.0.0.0:8091")
    c.add_argument("--auth", default="", help="require digest auth user:password on incoming calls")
    c.add_argument("--codecs", default=",".join(CODECS), help="codecs we accept: " + ",".join(CODECS))
    c.add_argument("--mix", default="", help="reply mix, e.g. answer=70,busy=10,notfound=10,unavail=10")
    c.add_argument("--ring-ms", type=int, default=500)
    c.add_argument("--delay-ms", default="0", help="extra answer delay, ms or min-max")
    c.add_argument("--rtp-mode", default="normal", choices=["normal", "none", "blackhole", "private_ip"])
    c.add_argument("--loss-pct", type=float, default=0.0)
    c.add_argument("--hangup-after", type=int, default=0, help="we hang up after N seconds (0 = wait for caller)")
    c.add_argument("--early-media", action="store_true")

    u = sub.add_parser("customer", help="place calls like a customer")
    common(u, "0.0.0.0:8090")
    u.set_defaults(sip_port=5090)
    u.add_argument("--target", default=RUN_DEFAULTS["target"], help="SBC address host:port")
    u.add_argument("--auth", default="", help="digest credentials user:password")
    u.add_argument("--from-user", default=RUN_DEFAULTS["from_user"])
    u.add_argument("--callee-start", default=RUN_DEFAULTS["callee_start"], help="first number to dial")
    u.add_argument("--callee-end", default=RUN_DEFAULTS["callee_end"], help="last number to dial (used in turn)")
    u.add_argument("--kind", default="batch", choices=["batch", "steps", "auth"])
    u.add_argument("--calls", type=int, default=10)
    u.add_argument("--cps", type=float, default=2.0)
    u.add_argument("--hold", default="20", help="call length seconds, or min-max")
    u.add_argument("--steps", default="10x60,25x60,50x60,100x60", help="ladder: callsxseconds,...")
    u.add_argument("--codecs", default="PCMU", help="codecs to offer, in order: " + ",".join(CODECS))
    u.add_argument("--profiles", default="", help="mix of dial-plan prefixes, e.g. 9990=80,9997=20 (overrides the number range)")
    u.add_argument("--faults", default="", help="comma list: " + ",".join(FAULTS))
    u.add_argument("--fault-pct", type=float, default=0.0)
    u.add_argument("--open-report", action="store_true", help="with --run: open the saved HTML report in the browser when done")
    u.add_argument("--list", default="", help="CSV/text file: dial number[,calling number[,auth user,auth password]] per line, used in turn")
    u.add_argument("--dtmf", default="", help="digits to send as RFC 2833 events after the call is answered, e.g. 123#")
    u.add_argument("--dtmf-after", type=float, default=2.0)
    u.add_argument("--cid", default="", help='Contact ID alarm test: "account event group zone", e.g. "1234 1130 01 001"; dial 9980xxx (a sipload carrier)')
    u.add_argument("--cid-count", type=int, default=1, help="Contact ID: messages sent per call (1-5)")
    u.add_argument("--cid-fault", default="", help="Contact ID: badsum (wrong check digit) or short (15 digits)")
    u.add_argument("--run", action="store_true", help="start the test now, print the report and exit (exit code 1 on FAIL)")

    us = sub.add_parser("user", help="manage dashboard logins:  user add NAME [--role viewer] | user del NAME | user list")
    us.add_argument("action", choices=["add", "del", "list"])
    us.add_argument("name", nargs="?", default="")
    us.add_argument("--role", default="admin", choices=["admin", "viewer"])
    us.add_argument("--password", default="", help="(otherwise you are asked)")
    us.add_argument("--users", default="users.json")
    m = sub.add_parser("mkaudio", help="write a test WAV file")
    m.add_argument("path")
    m.add_argument("--text", default="", help="speech text (uses ffmpeg flite when available)")
    m.add_argument("--tonetest", action="store_true", help="write the DTMF + 1004 Hz tone test signal")
    s = sub.add_parser("selftest", help="run carrier and customer on this machine and print the report")
    s.add_argument("--calls", type=int, default=20)
    s.add_argument("--hold", default="4")
    return ap


def _range(s, default=0):
    a, _, b = str(s).partition("-")
    lo = float(a or default)
    return lo, float(b) if b else lo


def make_node(role, args):
    args.target_host = parse_hostport(getattr(args, "target", "") or "192.0.2.1")[0] if role == "customer" else None
    node = Node(role, args)
    return node


def apply_carrier_args(node, a):
    c = node.cfg
    c["codecs"] = [x.strip().upper() for x in a.codecs.split(",") if x.strip().upper() in CODEC_PT] or ["PCMU"]
    if a.auth:
        c["auth_user"], _, c["auth_pass"] = a.auth.partition(":")
    if a.mix:
        for k in c["mix"]:
            c["mix"][k] = 0
        for part in a.mix.split(","):
            k, _, v = part.partition("=")
            if k.strip() in c["mix"]:
                c["mix"][k.strip()] = float(v or 0)
    c["ring_ms"] = a.ring_ms
    lo, hi = _range(a.delay_ms)
    c["delay_min_ms"], c["delay_max_ms"] = lo, hi
    c["rtp_mode"], c["loss_pct"], c["hangup_after"], c["early_media"] = a.rtp_mode, a.loss_pct, a.hangup_after, a.early_media


def customer_params(a):
    p = {"kind": a.kind, "target": a.target, "from_user": a.from_user, "callee_start": a.callee_start,
         "callee_end": a.callee_end, "profiles": a.profiles, "dtmf": a.dtmf, "dtmf_after": a.dtmf_after, "cid": a.cid, "cid_fault": a.cid_fault, "cid_count": a.cid_count, "list_csv": (open(a.list).read() if a.list else ""), "calls": a.calls, "cps": a.cps,
         "codecs": [x.strip().upper() for x in a.codecs.split(",") if x.strip()],
         "faults": [x.strip() for x in a.faults.split(",") if x.strip()], "fault_pct": a.fault_pct}
    p["hold_min"], p["hold_max"] = _range(a.hold, 20)
    if a.auth:
        p["auth_user"], _, p["auth_pass"] = a.auth.partition(":")
    if a.steps:
        p["steps"] = [[int(x.split("x")[0]), int(x.split("x")[1])] for x in a.steps.split(",") if "x" in x]
    return p


def main(argv=None):
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(errors="replace")
        except (AttributeError, ValueError):
            pass
    if os.name == "nt" and sys.version_info < (3, 11):
        print("WARNING: on Windows use Python 3.11 or newer; older versions have a coarse sleep timer and audio timing will be poor.")
    a = build_parser().parse_args(argv)
    if a.cmd == "user":
        import getpass
        au = Auth(a.users)
        if a.action == "list":
            for n, v in sorted(au.users.items()):
                print("%-20s %s" % (n, v["role"]))
            return 0
        if not a.name:
            print("give a user name")
            return 2
        if a.action == "del":
            print("deleted" if au.users.pop(a.name, None) and au.save() is None else "no such user")
            return 0
        pw = a.password or getpass.getpass("password for %s: " % a.name)
        try:
            au.set_user(a.name, pw, a.role)
        except ValueError as e:
            print(e)
            return 2
        print("saved user %s (%s)" % (a.name, a.role))
        return 0
    if a.cmd == "mkaudio":
        print("wrote %s (%s)" % (a.path, make_wav(a.path, a.text or None, a.tonetest)))
        return 0
    if a.cmd == "selftest":
        return selftest(a)
    if a.audio == "tonetest":
        a.audio = "__tonetest__"
    if a.audio and a.audio != "__tonetest__" and not os.path.exists(a.audio):
        print("audio file not found:", a.audio)
        return 2
    node = make_node(a.cmd, a)
    if a.dialplan:
        try:
            plan = json.load(open(a.dialplan))
            assert isinstance(plan, list) and all("prefix" in r for r in plan)
            have = set(str(r["prefix"]) for r in plan)
            plan = plan + [dict(r) for r in DEFAULT_DIALPLAN if r["prefix"] not in have]     # numbers the file does not mention (e.g. 9989) still work and are listed
            node.cfg["dialplan"] = plan
        except Exception as e:
            print("cannot use --dialplan %s: %s" % (a.dialplan, e))
            return 2
    if a.cmd == "carrier":
        apply_carrier_args(node, a)
    log("sipload %s: SIP udp %s:%d, advertising %s, audio '%s' (%.1f s)" % (a.cmd, a.bind, node.sip_port, node.adv_ip, node.audio.name, node.audio.seconds))
    if a.web != "off":
        au = None
        if a.users:
            au = Auth(a.users)
            ensure_admin(au)
        else:
            log("dashboard has no login (private network use; add --users users.json to require one)")
        start_web(node, a.web, au, a.peer_key)
    if a.cmd == "customer" and a.run:
        if not getattr(a, "target", ""):
            print("error: --target host:port is required with --run (the SBC to call)", file=sys.stderr)
            return 2
        run = node.start_run(customer_params(a))
        while run.state == "running":
            time.sleep(0.5)
        time.sleep(0.5)
        S = summarize(node)
        if not a.out:
            print(render_text(node, S, run))
        elif getattr(node, "last_report", None):
            print("\nReport files are in: %s" % os.path.dirname(node.last_report))
            if a.open_report:
                import webbrowser
                webbrowser.open("file:///" + node.last_report.replace("\\", "/") + ".html")
        return 0 if S["overall"] != "FAIL" else 1
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        node.stopping = True
        if a.out and node.history:
            node.save_report(node.run)
    return 0


def selftest(a):
    import types
    base = dict(bind="127.0.0.1", advertise_ip="127.0.0.1", rtp_min=30000, rtp_max=34998, audio="", audio_dir="audio",
                record_seconds=30, web="off", users="", peer_key="", out="", readback_password="")
    ca = types.SimpleNamespace(sip_port=15060, target_host=None, **base)
    cu = types.SimpleNamespace(sip_port=15090, target_host="127.0.0.1", **dict(base, rtp_min=36000, rtp_max=40998))
    car, cus = Node("carrier", ca), Node("customer", cu)
    run = cus.start_run({"target": "127.0.0.1:15060", "calls": a.calls, "cps": 20, "hold_min": float(a.hold), "hold_max": float(a.hold)})
    while run.state == "running":
        time.sleep(0.3)
    time.sleep(1.0)
    S = summarize(cus)
    print(render_text(cus, S, run))
    print(render_text(car, summarize(car)))
    return 0 if S["overall"] != "FAIL" else 1


if __name__ == "__main__":
    sys.exit(main())
