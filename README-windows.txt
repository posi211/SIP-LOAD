sipload for Windows - customer-side tester
==========================================
Runs on the customer's network, sends calls through Yeti to the sipload carrier (dial plan 999xxxx), and rates the result.

1. Install Python 3.11 or newer once (python.org, tick "Add python.exe to PATH", or: winget install Python.Python.3.12).
2. Unzip this folder anywhere. Double-click start-customer-tester.bat, enter the SBC address (for example sbc.example.com:5060)
   and, if the Yeti gateway uses a login, user:password. Your browser opens the dashboard on http://127.0.0.1:8090/ (this PC only).
3. In the dashboard: pick "What should the carrier do?" (tone test, echo, busy, 404 ...), press a call-count preset, watch it, then
   "Report" or "Save report on this machine" (saved in the sipload-reports folder next to the program).
   quick-echo-test.bat does a 10-call echo test without the dashboard and opens the report in your browser.

Reports: every report is saved automatically (and by the dashboard button "Save report on this machine") in the folder
   sipload-reports   next to sipload.py, as .html (open in a browser, has charts), .csv (Excel) and .json.
   The file name ends in PASS or FAIL. Double-click open-reports.bat to open that folder. In the dashboard, "Saved reports" lists them.

Windows firewall: the first start asks to allow Python; allow it on Private networks (and Public if the customer network is marked public).
It needs outbound UDP to Yeti and the replies back (SIP port 5060 locally, RTP ports 36000-40998 by default - change with --rtp-min/--rtp-max).

Before you go, on the Yeti side:
 * the customer's public IP must be allowed (a gateway for the test customer on the SBC, plus any firewall or IP whitelist in front of it), or use gateway login with the
   user:password you enter above;
 * a dialpeer for prefix 999 pointing at the machine running the sipload carrier.
If the PC is behind the customer's NAT, Yeti must handle NAT for that gateway (symmetric RTP) or the audio will not come back.
Developed and tested on Linux; Windows is lightly tested. If something fails, open an issue and include the text in the window.
