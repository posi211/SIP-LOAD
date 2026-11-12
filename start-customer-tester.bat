@echo off
rem sipload customer tester for Windows. Double-click, enter the Yeti address, and the dashboard opens in your browser.
cd /d "%~dp0"
set TARGET=
set /p TARGET=Yeti address to test (host:port, e.g. sbc.example.com:5060): 
if "%TARGET%"=="" (echo No address entered. & pause & exit /b 1)
set AUTH=
set /p AUTH=Gateway login user:password (press Enter if Yeti identifies us by IP): 
where py >nul 2>nul
if errorlevel 1 (echo Python is not installed. Install Python 3.12 from python.org or run: winget install Python.Python.3.12 & pause & exit /b 1)
start "" http://127.0.0.1:8090/
if "%AUTH%"=="" (
  py -3 sipload.py customer --web 127.0.0.1:8090 --target %TARGET% --audio tonetest
) else (
  py -3 sipload.py customer --web 127.0.0.1:8090 --target %TARGET% --auth %AUTH% --audio tonetest
)
pause
