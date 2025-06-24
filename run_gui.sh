#!/bin/bash

# Script to run the CIL to Promela Converter GUI

echo "Starting CIL to Promela Converter GUI..."

# Check if streamlit is installed
if ! command -v streamlit &> /dev/null; then
    echo "Streamlit is not installed. Installing required packages..."
    pip install streamlit google-generativeai tenacity
fi

# Run the Streamlit application
cd "$(dirname "$0")"
streamlit run streamlit_app.py