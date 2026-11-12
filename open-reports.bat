@echo off
cd /d "%~dp0"
if not exist sipload-reports mkdir sipload-reports
start "" explorer "%~dp0sipload-reports"
