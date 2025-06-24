#!/usr/bin/env python3
"""
Diagnostic script to check what's wrong with the Promela files
"""

import os
import subprocess
import sys

def check_file_with_spin(file_path):
    """Run SPIN on a file and capture detailed error output"""
    print(f"Checking file: {file_path}")
    
    # Check if file exists
    if not os.path.exists(file_path):
        print(f"Error: File {file_path} does not exist")
        return False
    
    # Run spin with -a (same as test script)
    result = subprocess.run(['spin', '-a', file_path], 
                          capture_output=True, text=True)
    
    if result.returncode == 0:
        print(f"✅ Success: {file_path} is syntactically valid Promela")
        return True
    else:
        print(f"❌ Error: {file_path} has syntax errors")
        if result.stderr:
            print("\nError output:")
            print(result.stderr)
        if result.stdout:
            print("\nStandard output:")
            print(result.stdout)
        return False

def main():
    # Check if file is provided as argument
    if len(sys.argv) > 1:
        file_path = sys.argv[1]
        check_file_with_spin(file_path)
    else:
        # Try to check all pml files in test_cases
        test_dir = "test_cases"
        if os.path.exists(test_dir):
            for file_name in os.listdir(test_dir):
                if file_name.endswith(".pml"):
                    check_file_with_spin(os.path.join(test_dir, file_name))
                    print("\n" + "-"*50 + "\n")

if __name__ == "__main__":
    main() 