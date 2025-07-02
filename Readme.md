# CToPromelaAgentic: C to Promela Converter
 
## Overview  
CToPromelaAgentic is a powerful tool for converting C/C++ code (through C Intermediate Language - CIL) to Promela, the specification language used by the SPIN model checker. This tool leverages AI with large language models to automate the conversion process, making formal verification more accessible to software developers.

## Features
- **Intelligent Conversion**: Converts CIL code to Promela using Google's Gemini AI models
- **Error Handling**: Sophisticated error detection and correction mechanisms
- **User-friendly GUI**: Streamlit-based interface for easy interaction
- **Verification Support**: Integrates with SPIN for model checking
- **Test Suite**: Comprehensive testing framework for conversion quality assurance
- **Learning System**: Improves over time by learning from past errors and fixes

## System Requirements
- **Operating System**: Windows 10/11, Linux (Ubuntu 20.04+), or macOS 10.15+
- **Python**: Version 3.8 or higher
- **RAM**: Minimum 4GB, recommended 8GB+
- **Storage**: At least 1GB free space
- **Internet Connection**: Required for AI model access

## Installation Guide

### 1. Download and Extract
1. Download the latest release from the releases page
2. Extract the ZIP file to your preferred location
3. Note the path where you extracted the files

### 2. Python Setup
1. Install Python 3.8 or higher from [python.org](https://python.org)
2. Verify installation:
   ```bash
   python --version
   pip --version
   ```

### 3. Virtual Environment Setup
```bash
# Navigate to the project directory
cd path/to/CToPromelaAgentic

# Create virtual environment
python -m venv venv

# Activate virtual environment
# On Windows:
venv\Scripts\activate
# On Linux/macOS:
source venv/bin/activate
```

### 4. Install Dependencies
```bash
# Install required Python packages
pip install -r requirements.txt
```

### 5. Install CIL (C Intermediate Language)
#### Windows:
1. Install WSL (Windows Subsystem for Linux)
2. Open WSL terminal and run:
   ```bash
   sudo apt-get update
   sudo apt-get install cil
   ```

#### Linux (Ubuntu/Debian):
```bash
sudo apt-get update
sudo apt-get install cil
```

#### macOS:
```bash
brew install cil
```

### 6. Install SPIN Model Checker
#### Windows:
1. Download SPIN from [SPIN's official website](https://spinroot.com/spin/whatispin.html)
2. Extract to a directory (e.g., C:\spin)
3. Add to PATH:
   - Open System Properties > Advanced > Environment Variables
   - Add C:\spin to Path variable

#### Linux:
```bash
sudo apt-get install spin
```

#### macOS:
```bash
brew install spin
```

### 7. Google API Setup
1. Visit [Google AI Studio](https://makersuite.google.com/app/apikey)
2. Sign in with your Google account
3. Create a new API key
4. Set the API key:
   ```bash
   # Windows
   set GOOGLE_API_KEY=your_api_key_here
   
   # Linux/macOS
   export GOOGLE_API_KEY=your_api_key_here
   ```

## Running the Application

### GUI Mode (Recommended)

#### Windows:
1. Double-click `run_gui.bat`
   OR
2. Open Command Prompt:
   ```bash
   cd path\to\CToPromelaAgentic
   run_gui.bat
   ```

#### Linux/macOS:
1. Open Terminal
2. Navigate to project directory:
   ```bash
   cd path/to/CToPromelaAgentic
   chmod +x run_gui.sh
   ./run_gui.sh
   ```

### Manual GUI Start
```bash
# Activate virtual environment
source venv/bin/activate  # Linux/macOS
# or
venv\Scripts\activate     # Windows

# Run Streamlit app
streamlit run streamlit_app.py
```

### Command Line Mode
```bash
# Single file conversion
python test_unified.py --single input.cil --output output.pml

# Multiple file conversion
python test_unified.py --multi input_directory --output output_directory

# Run test suite
python test_unified.py --all
```

## Using the GUI

### 1. Initial Setup
1. Open the application in your web browser (typically http://localhost:8501)
2. Enter your Google API key if not set as environment variable
3. Select verification target:
   - General: Standard verification
   - Memory: Memory safety analysis
   - Concurrency: Concurrent behavior analysis
   - Security: Security vulnerability detection

### 2. Converting C Code
1. Click "Upload C File" or "Upload CIL File"
2. Select your input file
3. Choose conversion options:
   - Model: Select Gemini model version
   - Verification Level: Choose verification depth
   - Error Handling: Select error handling strategy

### 3. Monitoring Conversion
The GUI provides real-time feedback:
- Conversion Progress
- Error Detection
- Fix Attempts
- Verification Results

### 4. Reviewing Results
Access different tabs for:
- Status Log: Conversion process details
- Error Analysis: Detected issues
- Fix Iterations: Error resolution steps
- Final Code: Generated Promela code

### 5. Saving Results
1. Click "Download Promela" to save the output
2. Choose save location
3. Verify the saved file

## Troubleshooting

### Common Issues

1. **Python Version Error**
   ```bash
   # Check Python version
   python --version
   # Should be 3.8 or higher
   ```

2. **Missing Dependencies**
   ```bash
   # Reinstall requirements
   pip install -r requirements.txt --upgrade
   ```

3. **CIL Installation Issues**
   - Windows: Ensure WSL is properly installed
   - Linux: Check package manager repositories
   - macOS: Verify Homebrew installation

4. **SPIN Not Found**
   - Verify PATH environment variable
   - Check SPIN installation
   - Restart terminal/command prompt

5. **API Key Issues**
   - Verify API key format
   - Check environment variable
   - Ensure internet connection

### Getting Help
1. Check the logs in the `logs/` directory
2. Review error messages in the GUI
3. Check the `error_data/` directory for specific error patterns

## Directory Structure
```
CToPromelaAgentic/
├── agent.py              # Core conversion logic
├── CtoCILConvertor.py    # C to CIL conversion
├── error_database.py     # Error handling
├── streamlit_app.py      # GUI interface
├── test_unified.py       # Test suite
├── requirements.txt      # Dependencies
├── data/                 # Data files
├── logs/                 # Log files
├── test_cases/          # Test cases
└── results/             # Output directory
```

## Best Practices

1. **Code Preparation**
   - Use standard C/C++ syntax
   - Avoid complex macros
   - Keep functions modular
   - Document complex logic

2. **Conversion Process**
   - Start with small code segments
   - Verify each conversion step
   - Review error messages carefully
   - Save intermediate results

3. **Performance**
   - Use appropriate verification level
   - Monitor memory usage
   - Clean up old results
   - Regular system maintenance

## License
This software is proprietary and confidential. Unauthorized copying, distribution, or use is strictly prohibited.

## Support
For technical support or questions:
1. Check the documentation
2. Review error logs
3. Contact the development team

## Screenshots

Below are some screenshots demonstrating the application's interface and features:

### Main Interface
![Main Interface](Screenshot%20from%202025-06-24%2017-17-29.png)
*The main dashboard of the CToPromelaAgentic application.*

### File Upload
![File Upload](Screenshot%20from%202025-06-24%2017-17-12.png)
*Uploading a C or CIL file for conversion.*

### Conversion Progress
![Conversion Progress](Screenshot%20from%202025-06-24%2017-16-55.png)
*Real-time feedback during the conversion process.*

### Results and Analysis
![Results and Analysis](Screenshot%20from%202025-06-24%2017-14-54.png)
*Viewing the results, error analysis, and final Promela code.*
