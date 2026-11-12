@echo off
rem One-shot test with no dashboard: 10 calls to the echo number 9992xxx. The report opens in your browser and is saved in the sipload-reports folder.
cd /d "%~dp0"
set TARGET=
set /p TARGET=Yeti address to test (host:port): 
set AUTH=
set /p AUTH=Gateway login user:password (Enter if none): 
if "%AUTH%"=="" (
  py -3 sipload.py customer --web off --target %TARGET% --audio tonetest --callee-start 9992001 --callee-end 9992100 --calls 10 --cps 2 --hold 12 --run --open-report
) else (
  py -3 sipload.py customer --web off --target %TARGET% --auth %AUTH% --audio tonetest --callee-start 9992001 --callee-end 9992100 --calls 10 --cps 2 --hold 12 --run --open-report
)
pause
