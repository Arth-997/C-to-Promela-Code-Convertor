@echo off
echo Starting CIL to Promela Converter GUI...

:: Check if pip is available
where pip >nul 2>&1
if %ERRORLEVEL% neq 0 (
    echo Python or pip is not installed or not in PATH.
    echo Please install Python from https://www.python.org/downloads/
    pause
    exit /b 1
)

:: Install requirements if needed
echo Installing required packages...
pip install -r requirements.txt

:: Run the Streamlit application
echo Starting Streamlit application...
streamlit run streamlit_app.py

pause 