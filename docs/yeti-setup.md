# Using sipload with a Yeti Switch

sipload plays two roles around your Yeti: the **customer** tester calls *in* through Yeti as if it were a real customer, and the **carrier**
tester is the *termination* that Yeti routes the calls to. Menu and field names below follow the Yeti web admin; they can differ slightly
between versions.

```
 customer tester  --SIP/RTP-->  Yeti (origination gateway -> routing -> dialpeer)  --SIP/RTP-->  carrier tester
   (sipload customer)                                                                            (sipload carrier)
```

## 1. Carrier side (termination)
1. Run `python3 sipload.py carrier` on a host Yeti can reach (default SIP port 5060, RTP 36000-40998; open these on that host's firewall).
2. In Yeti: **Routing > Gateways** - add a *termination* gateway: host = the carrier tester's IP, port 5060, transport UDP, codecs PCMU/PCMA,
   no registration, no auth (or set `--auth` on the carrier and mirror the credentials here).
3. **Routing > Routing groups** - create `sipload-test`.
4. **Routing > Dialpeers** - add one for prefix `999` (matches the whole dial plan `9980`-`9999`) in that routing group, vendor = a test vendor,
   gateway = the one above. Give it a rate you accept (a zero-rate test vendor and customer keep the test out of billing).

## 2. Customer side (origination)
1. **Contractors**: create a test customer and a test vendor (or reuse existing ones).
2. **Accounts**: create a customer account with enough balance/credit (or no limit) for the planned call volume and the concurrency cap you want to test.
3. **Gateways**: add an *origination* gateway for the customer tester - either by **source IP** (the tester's public IP) or **auth user/password**
   (then give the same in the dashboard's *Auth username / password*, or `--auth`). Set the max-calls limit if you want to test it.
4. **Routing plans**: a plan that uses the `sipload-test` routing group, and attach it to the customer authorization (the origination gateway/customer auth).
5. **Rate plans**: any rate plan that prices prefix `999`.
6. Run `python3 sipload.py customer`, open `http://127.0.0.1:8090/`, set **SBC address** to your Yeti's SIP address and port, pick a preset, press **Start test**.

## 3. Firewalls, NAT and fail2ban-style tools
- Allow the customer tester's public IP on the Yeti SIP interface, and allow Yeti to reach the carrier tester's SIP and RTP ports.
- Behind NAT, Yeti needs symmetric RTP / NAT handling for that gateway or audio will not come back (calls would show "no audio").
- The login-failure test and `bad_password` fault deliberately fail authentication - run them from a non-whitelisted address to see your
  auto-ban or alerting react, and from a whitelisted one if you do not want to be banned.

## 4. Checking results in Yeti
Calls appear in the CDR (**CDR > CDR**) with their disposition code; compare Yeti's counts with the sipload report (answered, 486/404/503, durations).
For deeper debugging, capture SIP with your usual tools (for example Homer/heplify).

## Troubleshooting
| Symptom | Check |
|---|---|
| 403 / 401 | origination gateway IP or credentials not matching the customer auth |
| 404 on every call | no dialpeer matches prefix `999`, or the routing plan does not include the routing group |
| 503 / 480 | no active termination gateway, carrier tester unreachable, or customer balance/limit exhausted |
| Calls answer, no audio | RTP ports blocked or NAT without symmetric RTP; codec mismatch (use PCMU/PCMA for real audio) |
| Tone test cannot be measured | choose *Tone test* on both testers, or dial 9990xxx |
