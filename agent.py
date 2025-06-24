#!/usr/bin/env python3
"""
CIL to Promela converter agent.
Converts C Intermediate Language (CIL) code to Promela for verification.
"""

import os
import re
import json
import logging
import subprocess
import datetime
import tempfile
import argparse
from typing import List, Tuple, Dict, Any, Optional
from collections import defaultdict
import sys

# You'll need to install these dependencies:
# pip install requests tenacity google-generativeai langchain
import requests
from tenacity import retry, stop_after_attempt, wait_exponential
# Use the appropriate API based on your needs
import google.generativeai as genai

from test_case_manager import TestCaseManager

# Set up logging
logging.basicConfig(level=logging.INFO, 
                    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Default API key
DEFAULT_API_KEY = "AIzaSyC88vGjUkqyu4Ux_9zVCdk7Z88cpQi7uEM"
# Gemini models
DEFAULT_MODEL = "gemini-2.0-flash"
FREE_TIER_MODEL = "gemini-2.0-flash"  # Lower-tier model

class ErrorHandler:
    """
    Enhanced error handling system for Promela/SPIN verification errors
    """
    def __init__(self):
        self.logger = logging.getLogger('ErrorHandler')
        # Map error types to their descriptions and potential fixes
        self.error_map = {
            'redeclaration': {
                'description': 'Variable or type has been declared more than once',
                'recovery': [
                    'Rename one of the variables to avoid the name conflict',
                    'Use typedefs to create distinct types for different scopes',
                    'Ensure variables with the same name are in different processes'
                ]
            },
            'undeclared_variable': {
                'description': 'Variable is used but not declared',
                'recovery': [
                    'Declare the variable before using it',
                    'Check for typos in variable names',
                    'Verify scope - the variable might be declared in a different scope'
                ]
            },
            'syntax_error': {
                'description': 'Promela syntax is incorrect',
                'recovery': [
                    'Check Promela language reference for correct syntax',
                    'Verify placement of semicolons, braces, and parentheses',
                    'Look for missing or extra keywords'
                ]
            },
            'type_error': {
                'description': 'Type mismatch in expression or assignment',
                'recovery': [
                    'Ensure variable types match on both sides of an assignment',
                    'Add explicit type casting if necessary',
                    'Verify array indices are integers'
                ]
            },
            'channel_error': {
                'description': 'Issue with channel operations',
                'recovery': [
                    'Verify channel capacity is sufficient',
                    'Check message structure matches channel definition',
                    'Ensure proper use of send (!) and receive (?) operators'
                ]
            },
            'assertion_violation': {
                'description': 'An assertion in the model has been violated',
                'recovery': [
                    'Examine the state where assertion failed',
                    'Verify the logic leading to the assertion',
                    'Consider if the assertion correctly expresses the desired property'
                ]
            },
            'invalid_end_state': {
                'description': 'Process ended in a non-end state',
                'recovery': [
                    'Add proper termination states',
                    'Use labels and goto to ensure proper end states',
                    'Verify that all paths have proper termination'
                ]
            },
            'deadlock': {
                'description': 'System has reached a state where no further progress is possible',
                'recovery': [
                    'Review synchronization between processes',
                    'Check for circular wait conditions',
                    'Add timeout or else statements to handle blocked states'
                ]
            },
            'livelock': {
                'description': 'System makes progress but doesn\'t advance its overall computation',
                'recovery': [
                    'Review loops for exit conditions',
                    'Use progress labels to detect livelocks',
                    'Add fairness constraints to scheduler'
                ]
            },
            'acceptance_cycle': {
                'description': 'Detected an infinite execution cycle that continuously visits acceptance states',
                'recovery': [
                    'Review your LTL properties',
                    'Check for unintended infinite loops',
                    'Consider adding fairness constraints'
                ]
            },
            'ltl_violation': {
                'description': 'The model violates an LTL property',
                'recovery': [
                    'Examine the counter-example trace',
                    'Verify if the property correctly expresses the desired behavior',
                    'Check if the model correctly implements the intended behavior'
                ]
            },
            'resource_exhaustion': {
                'description': 'SPIN ran out of memory or exceeded step limits',
                'recovery': [
                    'Apply state space reduction techniques',
                    'Use partial order reduction',
                    'Consider bitstate hashing or other compression techniques',
                    'Simplify the model or property'
                ]
            },
            'never_claim_error': {
                'description': 'Issue with the never claim (LTL property automaton)',
                'recovery': [
                    'Check for syntax errors in the LTL formula',
                    'Verify the never claim is correctly specified',
                    'Ensure the never claim is compatible with the model'
                ]
            },
            'array_index_error': {
                'description': 'Array index out of bounds',
                'recovery': [
                    'Verify array indices are within declared bounds',
                    'Add bounds checking before accessing arrays',
                    'Ensure arrays are properly initialized'
                ]
            },
            'divide_by_zero': {
                'description': 'Division by zero detected',
                'recovery': [
                    'Add guards to prevent division by zero',
                    'Check denominators before division operations',
                    'Verify variable initialization'
                ]
            }
        }
        
    def get_error_details(self, error_type: str) -> dict:
        """Get detailed information about a specific error type"""
        if error_type in self.error_map:
            return self.error_map[error_type]
        return {
            'description': 'Unknown error type',
            'recovery': ['Examine SPIN output for detailed error message']
        }
    
    def format_error_report(self, error_info: dict) -> str:
        """Format error information into a human-readable report"""
        report = []
        report.append("=== Error Report ===")
        
        # Add error location information
        if error_info.get('line_number'):
            report.append(f"Location: Line {error_info['line_number']}")
        
        # Add error message
        if error_info.get('message'):
            report.append(f"Message: {error_info['message']}")
        
        # Add detailed information for each error type
        if error_info.get('error_types'):
            report.append("\nDetected error types:")
            for error_type in error_info['error_types']:
                details = self.get_error_details(error_type)
                report.append(f"\n- {error_type.upper()}: {details['description']}")
                report.append("  Potential solutions:")
                for i, solution in enumerate(details['recovery'], 1):
                    report.append(f"  {i}. {solution}")
        
        # Add code snippet if available
        if error_info.get('code_snippet'):
            report.append("\nRelevant code:")
            report.append(error_info['code_snippet'])
        
        report.append("\n=== End of Error Report ===")
        return "\n".join(report)
    
    def analyze_verification_trace(self, trace_file: str) -> dict:
        """Analyze a SPIN verification trail file to extract insights"""
        trace_info = {
            'state_count': 0,
            'key_states': [],
            'transitions': [],
            'variables': defaultdict(list)
        }
        
        try:
            if not os.path.exists(trace_file):
                self.logger.error(f"Trace file not found: {trace_file}")
                return trace_info
                
            # Run SPIN to get the guided simulation from the trail
            cmd = f"spin -t -p {trace_file.replace('.trail', '.pml')}"
            result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
            
            if result.returncode != 0:
                self.logger.error(f"Failed to analyze trace: {result.stderr}")
                return trace_info
                
            # Parse the simulation output
            lines = result.stdout.split('\n')
            current_state = 0
            
            for line in lines:
                # Count states
                if "STATE" in line:
                    current_state = int(re.search(r"STATE\s+(\d+)", line).group(1))
                    trace_info['state_count'] = max(trace_info['state_count'], current_state + 1)
                
                # Extract key events (assertions, printf, etc.)
                if "ASSERT" in line or "printf" in line:
                    trace_info['key_states'].append({
                        'state': current_state,
                        'event': line.strip()
                    })
                
                # Track variable values
                var_match = re.search(r"(\w+)\s+=\s+(\d+)", line)
                if var_match:
                    var_name, var_value = var_match.groups()
                    trace_info['variables'][var_name].append({
                        'state': current_state,
                        'value': var_value
                    })
                
                # Track process transitions
                proc_match = re.search(r"proc\s+(\d+)\s+\((\w+)\)", line)
                if proc_match:
                    proc_id, proc_name = proc_match.groups()
                    trace_info['transitions'].append({
                        'state': current_state,
                        'process': f"{proc_name}[{proc_id}]",
                        'action': line.strip()
                    })
            
        except Exception as e:
            self.logger.error(f"Error analyzing trace: {e}")
            self.logger.debug(traceback.format_exc())
        
        return trace_info
    
    def suggest_fixes(self, error_info: dict, promela_code: str) -> List[str]:
        """Generate specific fix suggestions based on error information"""
        fixes = []
        
        # Different fix strategies based on error type
        for error_type in error_info.get('error_types', []):
            if error_type == 'redeclaration':
                # Suggest renaming or scoping
                var_match = re.search(r"redeclaration of '(\w+)'", error_info.get('message', ''))
                if var_match:
                    var_name = var_match.group(1)
                    fixes.append(f"Consider renaming one instance of '{var_name}' or moving it to a different scope")
                    fixes.append(f"You could use a typedef to create a scoped version of '{var_name}'")
            
            elif error_type == 'undeclared_variable':
                # Suggest declaration
                var_match = re.search(r"undeclared variable: (\w+)", error_info.get('message', ''))
                if var_match:
                    var_name = var_match.group(1)
                    fixes.append(f"Declare variable '{var_name}' before using it")
                    fixes.append(f"Check for typos in the name '{var_name}'")
            
            elif error_type == 'syntax_error':
                # Syntax correction suggestions
                if 'semicolon' in error_info.get('message', '').lower():
                    fixes.append("Add missing semicolon (;) at the end of the statement")
                elif 'bracket' in error_info.get('message', '').lower():
                    fixes.append("Check for mismatched brackets { } or parentheses ( )")
                else:
                    fixes.append("Review Promela syntax documentation for the correct syntax")
            
            elif error_type == 'deadlock':
                fixes.append("Add timeout or else guards to handle blocking conditions")
                fixes.append("Check for circular wait conditions between processes")
                fixes.append("Review channel operations for potential blocking")
            
            elif error_type == 'array_index_error':
                fixes.append("Add bounds checking before accessing array elements")
                fixes.append("Verify array size declarations match expected usage")
        
        # Add generic fixes if no specific fixes were generated
        if not fixes:
            fixes = [
                "Review the error message and location carefully",
                "Refer to the Promela language reference manual for syntax guidance",
                "Consider simplifying the model to isolate the error"
            ]
        
        return fixes

from error_database import ErrorDatabase

class CILToPromelaConverter:
    def __init__(self, api_key: str, model: str = DEFAULT_MODEL, spin_path: str = "spin", verification_target: str = "general", advanced_features: bool = False, reduction_techniques: List[str] = None, max_iterations: int = 5):
        """
        Initialize the CIL to Promela converter.
        
        Args:
            api_key: Gemini API key
            model: LLM model to use
            spin_path: Path to the SPIN executable
            verification_target: Target verification domain ('general', 'memory', 'concurrency', 'security')
            advanced_features: Enable advanced SPIN features
            reduction_techniques: List of model reduction techniques to apply
            max_iterations: Maximum number of iterations for fixing code
        """
        self.api_key = api_key
        self.model = model
        self.spin_path = spin_path
        self.verification_target = verification_target
        self.advanced_features = advanced_features
        self.reduction_techniques = reduction_techniques or []
        self.max_iterations = max_iterations
        self.error_handler = ErrorHandler()
        self.logger = logging.getLogger('CILToPromelaConverter')
        
        # Initialize Gemini API
        genai.configure(api_key=api_key)
        self.model = genai.GenerativeModel(model)
        
        # Initialize test case manager
        self.test_manager = TestCaseManager("test_suite/results")
        
        # Verify SPIN installation
        try:
            subprocess.run([spin_path, "-V"], capture_output=True, check=True)
        except subprocess.CalledProcessError as e:
            raise RuntimeError(f"Failed to verify SPIN installation: {e}")
        except FileNotFoundError:
            raise RuntimeError(f"SPIN executable not found at {spin_path}")
            
        # Set up conversion prompt
        self.conversion_prompt = """
# CIL to Promela Conversion Expert

You are an expert agent specializing in formal verification, translating C Intermediate Language (CIL) code to Promela for verification with the Spin model checker. Your goal is to produce accurate Promela models that faithfully capture the semantics of the input code, focusing on detecting potential concurrency defects.

## Verification Target: {verification_target}

{target_guidance}

## Detailed Translation Guidelines

### Data Structures
1. *Primitive Types*: Translate all integer-like types (int, long, signed) to Promela's int type.
2. *Structures*: Translate struct fields to variable declarations within the appropriate Promela proctype.
3. *Pointers*:
   - Represent pointers as integer variables (indices into simulated memory arrays)
   - Create global arrays for each pointed-to type: type_mem for data and type_valid for tracking memory availability
   - For malloc, find a free location in _valid array, assign its index to the pointer variable, and mark as occupied
   - For free, mark the location in _valid array as free
   - For pointer dereference, access the _mem array using the pointer variable as index
   - For pointer assignment, directly assign the integer value

### Expressions and Statements
1. *Function Calls*:
   - Create Promela `inline` functions for each C function
   - Function parameters become inline parameters
   - Functions that return values must use output parameters
   - Example: `inline calculate(input, result) {{ result = input * 2; }}`

2. *Control Flow*:
   - If statements: `if :: condition -> action :: else -> default_action fi`
   - Loops: `do :: condition -> action od`
   - Labels: use `label_name:` for jumps and `goto label_name` for control flow

3. *Atomic Operations*:
   - Use `atomic {{ ... }}` for operations that should not be interleaved
   - Use `d_step {{ ... }}` for deterministic sequences

### LTL Properties and Assertions
1. *Safety Properties*: 
   ```
   ltl safety {{ [](!unsafe_condition) }}
   ```

2. *Liveness Properties*: 
   ```
   ltl liveness {{ <>(request -> <>response) }}
   ```

3. *Assertions*: 
   ```
   assert(condition)
   ```

## Output Format
Return ONLY the Promela code with NO additional explanations or formatting characters.

Here is the CIL code:

{cil_code}

Translate this CIL code to Promela following the guidelines above, with particular attention to CORRECT PROMELA SYNTAX. Only return valid Promela code that will compile with Spin.
"""
        
        self.error_fix_prompt = """
# Promela Error Fix Expert

You are an expert in fixing syntax and semantic errors in Promela code for the SPIN model checker. The Promela code below failed validation with SPIN.

## Original Promela code:

{promela_code}


## Error messages from SPIN:

{error_message}


## Common Promela Error Patterns and Fixes:

1. *C-style function declarations*: Replace with `inline` functions.
2. *Return statements*: Replace with output parameters.
3. *C-style if statements*: Replace with `if :: condition -> action fi` syntax.
4. *C-style loops*: Replace with `do :: condition -> action od` syntax.
5. *Missing semicolons*: Ensure all statements end with semicolons.
6. *Incorrect variable types*: Use `byte` for small integers (0-255), `bit` for 0-1 values.
7. *Redeclaration errors*: Rename variables to avoid conflicts.
8. *Channel declarations*: Ensure proper format `chan name = [size] of {type}`.
9. *Label conflicts*: Ensure unique label names.

## Instructions:
1. Carefully analyze the error message to identify the specific issues
2. Focus on converting any C-style syntax to Promela syntax
3. Replace any return statements with output parameters
4. Fix conditional statements with proper if-fi structure
5. Fix loops with proper do-od structure
6. Return ONLY the complete fixed Promela code with NO explanations

Fix the errors in the Promela code and return only the raw corrected code:
"""

        # Initialize error database
        self.error_db = ErrorDatabase()
        
    def convert(self, cil_code: str, context: Dict = None, fix_prompt: str = None) -> str:
        """
        Convert CIL code to Promela with optional context and fix prompt.
        
        Args:
            cil_code: CIL code to convert
            context: Optional context with global variables and function signatures
            fix_prompt: Optional fix prompt
            
        Returns:
            Promela code
        """
        try:
            # If context is provided, add it to the CIL code
            if context:
                # Create context preamble
                context_code = self._create_context_preamble(
                    context.get('global_vars', {}), 
                    context.get('function_signatures', {})
                )
                # Add context to CIL code
                augmented_code = f"{context_code}\n\n{cil_code}"
            else:
                augmented_code = cil_code
                
            # Initial conversion
            promela_code = self.convert_cil_to_promela(augmented_code)
            
            # Apply fixes if provided
            if fix_prompt:
                promela_code = self._apply_fix(promela_code, fix_prompt)
            
            # Post-process the code
            promela_code = self._post_process_promela_code(promela_code)
            
            return promela_code
            
        except Exception as e:
            self.logger.error(f"Error during conversion: {str(e)}")
            raise
    
    def convert_cil_to_promela(self, cil_code: str) -> str:
        """Convert CIL code to Promela."""
        # Construct the prompt
        prompt = f"""
        Convert the following C Intermediate Language (CIL) code to Promela.
        Follow these rules:
        1. Convert all data types to Promela types (bit, bool, byte, short, int)
        2. Convert functions to inline or proctype as appropriate
        3. Handle printf statements correctly
        4. Convert loops to do...od format
        5. Convert arrays and structs to Promela format
        6. Handle channel operations correctly
        7. Add proper process declarations
        8. Ensure atomic operations are handled correctly
        
        CIL Code:
        {cil_code}
        """
        
        # Call LLM
        response = self.call_llm(prompt)
        
        # Extract code from response
        promela_code = self._extract_code_from_response(response)
        
        # Apply initial fixes through post-processing
        promela_code = self._post_process_promela_code(promela_code)
        
        return promela_code
    
    def _fix_data_types(self, promela_code: str) -> str:
        """Fix data type declarations in Promela code."""
        # Convert C types to Promela types
        replacements = {
            r'\bint\s+(\w+)': r'int \1',
            r'\bchar\s+(\w+)': r'byte \1',
            r'\bshort\s+(\w+)': r'short \1',
            r'\bbool\s+(\w+)': r'bool \1',
            r'\bunsigned\s+(\w+)\s+(\w+)': r'byte \2',
            r'\bsigned\s+(\w+)\s+(\w+)': r'int \2',
            r'\bfloat\s+(\w+)': r'int \1',
            r'\bdouble\s+(\w+)': r'int \1'
        }
        
        for pattern, replacement in replacements.items():
            promela_code = re.sub(pattern, replacement, promela_code)
        
        return promela_code
    
    def _fix_control_structures(self, promela_code: str) -> str:
        """Fix control structures in Promela code."""
        # Fix if statements
        promela_code = re.sub(
            r'if\s*\((.*?)\)\s*{(.*?)}\s*else\s*{(.*?)}',
            lambda m: f'if\n:: ({m.group(1)}) -> {m.group(2)}\n:: else -> {m.group(3)}\nfi',
            promela_code, flags=re.DOTALL
        )
        
        promela_code = re.sub(
            r'if\s*\((.*?)\)\s*{(.*?)}',
            lambda m: f'if\n:: ({m.group(1)}) -> {m.group(2)}\n:: else -> skip\nfi',
            promela_code, flags=re.DOTALL
        )
        
        # Fix for loops
        promela_code = re.sub(
            r'for\s*\((.*?);\s*(.*?);\s*(.*?)\)\s*{(.*?)}',
            lambda m: f'{m.group(1)};\ndo\n:: ({m.group(2)}) -> {m.group(4)}\n{m.group(3)};\n:: else -> break\nod',
            promela_code, flags=re.DOTALL
        )
        
        # Fix while loops
        promela_code = re.sub(
            r'while\s*\((.*?)\)\s*{(.*?)}',
            lambda m: f'do\n:: ({m.group(1)}) -> {m.group(2)}\n:: else -> break\nod',
            promela_code, flags=re.DOTALL
        )
        
        # Fix do-while loops
        promela_code = re.sub(
            r'do\s*{(.*?)}\s*while\s*\((.*?)\)',
            lambda m: f'do\n:: true -> {m.group(1)}\nif\n:: ({m.group(2)}) -> skip\n:: else -> break\nfi\nod',
            promela_code, flags=re.DOTALL
        )
        
        # Fix do-loops with improper structure
        # Find all do blocks without :: guards
        do_blocks = re.finditer(r'do\s+(?!::)([^;]+?)\s+od', promela_code, flags=re.DOTALL)
        for match in do_blocks:
            block_content = match.group(1)
            fixed_block = f"do\n:: true -> {block_content}\nod"
            promela_code = promela_code.replace(match.group(0), fixed_block)
        
        # Add parentheses to conditions
        condition_patterns = [
            (r'if\s*\n\s*::\s*([^(].+?)\s*->', r'if\n:: (\1) ->'),
            (r'do\s*\n\s*::\s*([^(].+?)\s*->', r'do\n:: (\1) ->'),
        ]
        for pattern, replacement in condition_patterns:
            promela_code = re.sub(pattern, replacement, promela_code, flags=re.DOTALL)
        
        return promela_code
    
    def _apply_fix(self, promela_code: str, fix_prompt: str) -> str:
        """Apply a fix to the Promela code based on the fix prompt."""
        # Construct the fix prompt
        prompt = f"""
        Fix the following Promela code according to this guidance:
        {fix_prompt}
        
        Current code:
        {promela_code}
        """
        
        # Call LLM
        response = self.call_llm(prompt)
        
        # Extract fixed code
        fixed_code = self._extract_code_from_response(response)
        
        # Apply post-processing
        fixed_code = self._post_process_promela_code(fixed_code)
        
        return fixed_code
    
    def _post_process_promela_code(self, code: str) -> str:
        """Post-process Promela code to fix common issues."""
        # Remove spurious declarations at the start of the file
        # Look for the first comment or standard declaration or init block
        valid_start_patterns = [
            r'/\*',           # Comment start
            r'#define',       # Define statement
            r'mtype',         # mtype declaration
            r'proctype',      # Process definition
            r'init\s*{',      # Init block
            r'byte\s+\w+\s*=', # Variable with initialization
            r'bool\s+\w+\s*=', # Boolean with initialization
            r'int\s+\w+\s*=',  # Integer with initialization
            r'chan\s+\w+\s*='  # Channel with initialization
        ]
        
        # Find first valid start
        first_valid = len(code)
        for pattern in valid_start_patterns:
            match = re.search(pattern, code)
            if match and match.start() < first_valid:
                first_valid = match.start()
        
        # If found, remove everything before it
        if first_valid < len(code):
            code = code[first_valid:]
        
        # Remove declarations of Promela keywords
        promela_keywords = ['if', 'fi', 'do', 'od', 'break', 'goto', 'skip', 'assert',
                           'print', 'printm', 'len', 'timeout', 'np_', 'enabled', 'active',
                           'priority', 'provided', 'hidden', 'show', 'unless', 'xr', 'xs',
                           'of', 'eval', 'trace', 'notrace', 'STDIN', 'STDOUT', 'true', 'false']
        
        for keyword in promela_keywords:
            code = re.sub(rf'\b(?:byte|bool|int|short|mtype)\s+{keyword}\b.*?[;=].*?\n', '', code)
        
        # Remove any malformed printf macros or defines
        code = re.sub(r'#define\s+printf\s*\([^)]*\).*', '', code)
        
        # Remove extern printf declarations, typedefs, etc. - these cause problems
        code = re.sub(r'(?:extern\s+)?(?:void|int)\s+printf\s*\([^)]*\)\s*(?:{[^}]*}|;)', '', code)
        code = re.sub(r'extern\s+printf\s*\([^)]*\)\s*;', '', code)
        code = re.sub(r'typedef\s+[^;]+;', '', code)
        
        # Fix printf statements 
        # This handles: printf("format", args) and printf(format, args)
        code = re.sub(r'printf\s*\(\s*"([^"]*)"(?:\s*,\s*([^)]+))?\s*\)\s*;?',
                     lambda m: f'printf("{m.group(1)}"{ ", " + m.group(2) if m.group(2) else ""})',
                     code)
                     
        # If printf without quotes: printf(message) -> printf("%s", message)
        code = re.sub(r'printf\s*\(\s*([^")\s,][^),]*)\s*\)',
                     r'printf("%s", \1)',
                     code)
        
        # Ensure no semicolon inside printf parentheses
        code = re.sub(r'printf\s*\([^)]*;\s*\)', 
                     lambda m: m.group(0).replace(';', ','), 
                     code)
        
        # Fix channel declarations
        code = re.sub(r'chan\s+(\w+)\s*=\s*\[\s*(\d+)\s*\]\s*of\s*{([^}]+)}',
                     r'chan \1 = [\2] of {\3}',
                     code)
        
        # Fix process declarations
        code = re.sub(r'(?:void|int)\s+(\w+)\s*\(\s*(?:void)?\s*\)',
                     r'proctype \1()',
                     code)
        
        # Fix atomic blocks
        code = re.sub(r'atomic\s*{([^}]+)}',
                     r'd_step {\1}',
                     code)
        
        # Fix boolean declarations
        code = re.sub(r'(?:bool|_Bool)\s+(\w+)',
                     r'bool \1',
                     code)
        
        # Fix array declarations
        code = re.sub(r'(\w+)\s+(\w+)\s*\[\s*(\d+)\s*\]',
                     r'\1 \2[\3]',
                     code)
        
        # Fix semicolons
        code = re.sub(r';\s*\n\s*}', r'\n}', code)
        code = re.sub(r';\s*\n\s*od', r'\nod', code)
        code = re.sub(r';\s*\n\s*fi', r'\nfi', code)
        
        # Add standard defines if not present
        if '#define' not in code:
            std_defines = """/* Standard defines */
#define NULL 0
#define TRUE 1
#define FALSE 0
#define MAX_SIZE 255

"""
            code = std_defines + code
        
        # Fix do-while loops that don't have proper structure
        # First, find all do...od blocks that don't start with ::
        do_blocks = re.finditer(r'do\s+(?!::)([^;]+?)\s+od', code, re.DOTALL)
        for match in do_blocks:
            block_content = match.group(1)
            # Find if there's an if-fi inside that determines loop continuation
            if_fi_match = re.search(r'if\s*::.*?break.*?fi', block_content, re.DOTALL)
            
            if if_fi_match:
                # There's already an if-fi for continuation control, wrap the whole block in a ::true->
                fixed_block = f"do\n:: true -> {block_content}\nod"
                code = code.replace(match.group(0), fixed_block)
            else:
                # No if-fi for control, add a generic true condition
                fixed_block = f"do\n:: true -> {block_content}\n:: else -> break\nod"
                code = code.replace(match.group(0), fixed_block)
        
        # Replace extern main with init for Promela
        code = re.sub(r'(?:extern\s+)?(?:void|int)\s+main\s*\(\s*(?:void|int\s+argc,\s*char\s*\*\s*argv\[\])?\s*\)\s*{',
                    r'init {',
                    code)
        
        # Fix extern declarations in Promela (which doesn't support extern)
        code = re.sub(r'extern\s+(\w+)', r'\1', code)
        
        return code
    
    def call_llm(self, prompt: str) -> str:
        """Call the LLM with retry logic."""
        try:
            response = self.model.generate_content(prompt)
            return response.text
        except Exception as e:
            self.logger.error(f"Error calling LLM: {str(e)}")
            raise
    
    def _extract_code_from_response(self, response: str) -> str:
        """Extract code from LLM response."""
        # Look for code blocks
        code_blocks = re.findall(r'```(?:promela)?\n(.*?)```', response, re.DOTALL)
        if code_blocks:
            return code_blocks[0].strip()
        
        # If no code blocks, try to extract the code directly
        lines = response.split('\n')
        code_lines = []
        in_code = False
        
        for line in lines:
            if line.strip().startswith('/*') or line.strip().startswith('//'):
                continue
            if line.strip() and not line.startswith(('Here', 'This', 'The', 'Note', 'Remember')):
                code_lines.append(line)
        
        return '\n'.join(code_lines).strip()
    
    def get_target_specific_guidance(self) -> str:
        """Get target-specific guidance for conversion."""
        guidance = {
            "general": """
            - Use appropriate Promela data types
            - Convert functions to inline or proctype
            - Handle printf statements correctly
            - Convert loops to do...od format
            """,
            "verification": """
            - Add assert statements for critical properties
            - Use atomic sections for state updates
            - Add progress labels for liveness properties
            - Include never claims for LTL properties
            """,
            "concurrency": """
            - Use channels for communication
            - Handle atomic operations correctly
            - Add proper synchronization
            - Consider race conditions
            """
        }
        return guidance.get(self.verification_target, guidance["general"])

    def parse_spin_error(self, error_message: str) -> dict:
        """
        Parse SPIN error messages to extract useful information.
        Args:
            error_message: The error message from SPIN
        Returns:
            Dictionary with parsed error information
        """
        error_info = {
            'line_numbers': [],
            'error_types': [],
            'details': error_message,
            'message': None
        }

        # Extract line numbers
        line_matches = re.findall(r'line\s+(\d+)', error_message, re.IGNORECASE)
        if line_matches:
            error_info['line_numbers'] = [int(line) for line in line_matches]

        # Identify error types and set user-friendly message
        lower_msg = error_message.lower()
        if 'undeclared variable' in lower_msg:
            error_info['error_types'].append('undeclared_variable')
            error_info['message'] = 'Undeclared variable found.'
        if 'syntax error' in lower_msg:
            error_info['error_types'].append('syntax_error')
            error_info['message'] = 'Syntax error detected in Promela code.'
        if 'type error' in lower_msg:
            error_info['error_types'].append('type_error')
            error_info['message'] = 'Type error detected in Promela code.'
        if 'invalid channel' in lower_msg:
            error_info['error_types'].append('channel_error')
            error_info['message'] = 'Invalid channel operation.'
        if 'redeclaration' in lower_msg:
            error_info['error_types'].append('redeclaration')
            error_info['message'] = 'Redeclaration of variable or type.'
        if 'array index' in lower_msg:
            error_info['error_types'].append('array_index_error')
            error_info['message'] = 'Array index out of bounds.'
        if 'deadlock' in lower_msg:
            error_info['error_types'].append('deadlock')
            error_info['message'] = 'Deadlock detected.'
        if 'invalid end state' in lower_msg:
            error_info['error_types'].append('invalid_end_state')
            error_info['message'] = 'Invalid end state in process.'
        if 'assertion violated' in lower_msg:
            error_info['error_types'].append('assertion_violation')
            error_info['message'] = 'Assertion violation.'
        if 'livelock' in lower_msg:
            error_info['error_types'].append('livelock')
            error_info['message'] = 'Livelock detected.'
        if 'acceptance cycle' in lower_msg:
            error_info['error_types'].append('acceptance_cycle')
            error_info['message'] = 'Acceptance cycle detected.'
        if 'ltl violation' in lower_msg:
            error_info['error_types'].append('ltl_violation')
            error_info['message'] = 'LTL property violation.'
        if 'resource exhausted' in lower_msg:
            error_info['error_types'].append('resource_exhaustion')
            error_info['message'] = 'Resource exhaustion in SPIN.'
        if 'never claim' in lower_msg:
            error_info['error_types'].append('never_claim_error')
            error_info['message'] = 'Never claim error.'
        if 'divide by zero' in lower_msg:
            error_info['error_types'].append('divide_by_zero')
            error_info['message'] = 'Division by zero detected.'

        # If no known error type was found, set message to unknown error
        if not error_info['error_types']:
            error_info['error_types'].append('other')
            error_info['message'] = 'Unknown error (see details).'

        logger.debug(f"Parsed error info: {error_info}")
        return error_info

    def verify_promela_code(self, promela_code: str) -> tuple[bool, str]:
        """
        Verify Promela code using Spin.
        
        Args:
            promela_code: The Promela code to verify
            
        Returns:
            Tuple of (success, error_message)
        """
        # Create a temporary file for the Promela code
        with tempfile.NamedTemporaryFile(mode='w', suffix='.pml', delete=False) as f:
            f.write(promela_code)
            temp_file = f.name
        
        try:
            # Run Spin to check syntax
            cmd = [self.spin_path, '-a', temp_file]
            self.logger.info(f"Running Spin syntax check: {' '.join(cmd)}")
            result = subprocess.run(cmd, capture_output=True, text=True)
            
            if result.returncode != 0:
                error_msg = result.stderr or result.stdout
                self.logger.error(f"Spin verification failed: {error_msg}")
                return False, error_msg
            
            # If we've reached here, syntax is valid
            self.logger.info("Syntax check passed")
            return True, "Syntax check passed"
                
        except Exception as e:
            self.logger.error(f"Error during verification: {e}")
            return False, str(e)
            
        finally:
            # Clean up temporary files
            try:
                os.unlink(temp_file)
            except Exception as e:
                self.logger.warning(f"Error cleaning up temporary files: {e}")

    def fix_promela_code(self, promela_code: str, error_message: str) -> str:
        """
        Fix Promela code based on error messages from Spin.
        
        Args:
            promela_code: The Promela code to fix
            error_message: Error message from Spin
            
        Returns:
            Fixed Promela code
        """
        # Parse the error message
        error_info = self.parse_spin_error(error_message)
        
        # Get similar errors and their fixes from test cases
        similar_errors = self.test_manager.get_similar_errors(
            error_info.get('type', ''),
            error_info.get('context', '')
        )
        
        # Get fix suggestions
        fix_suggestions = self.test_manager.get_fix_suggestions(
            error_info.get('type', ''),
            error_info.get('context', '')
        )
        
        # Apply specific fixes from the error database if available
        error_types = error_info.get('error_types', [])
        if error_types:
            error_type = error_types[0]
            fix_prompts = self.error_db.get_fix_prompts(error_type)
            if fix_prompts:
                # Use the most recent fix prompt
                fix_prompt = fix_prompts[-1].get('prompt', '')
                fixed_code = self._apply_fix(promela_code, fix_prompt)
                logger.info(f"Applied fix from database for {error_type}")
                
                # Verify if the fix worked
                success, _ = self.verify_promela_code(fixed_code)
                if success:
                    return fixed_code
        
        # If no database fixes worked or were available, use LLM with enhanced prompt
        instruction = self._construct_error_fix_prompt(promela_code, error_info, similar_errors, fix_suggestions)
        response = self.call_llm(instruction)
        fixed_code = self._extract_code_from_response(response)
        
        # Apply post-processing fixes
        fixed_code = self._post_process_promela_code(fixed_code)
        
        return fixed_code

    def _construct_error_fix_prompt(self, promela_code: str, error_info: dict, similar_errors=None, fix_suggestions=None) -> str:
        """
        Construct a prompt for fixing errors in Promela code.
        
        Args:
            promela_code: The Promela code with errors
            error_info: Information about the error
            similar_errors: Similar errors from database (optional)
            fix_suggestions: Fix suggestions (optional)
            
        Returns:
            Prompt for fixing the errors
        """
        error_types = error_info.get('error_types', ['syntax_error'])
        error_lines = error_info.get('line_numbers', [])
        error_details = error_info.get('details', 'Unknown error')
        
        # Format error lines
        line_info = ""
        if error_lines:
            line_info = f"Error occurred on line(s): {', '.join(map(str, error_lines))}\n"
        
        # Format similar errors
        similar_errors_text = ""
        if similar_errors:
            similar_errors_text = "Similar errors encountered previously:\n"
            for i, error in enumerate(similar_errors[:3], 1):
                similar_errors_text += f"{i}. {error.get('context', 'No context')}\n"
        
        # Format fix suggestions
        fix_suggestions_text = ""
        if fix_suggestions:
            fix_suggestions_text = "Fix suggestions:\n"
            for i, suggestion in enumerate(fix_suggestions[:3], 1):
                fix_suggestions_text += f"{i}. {suggestion}\n"
        
        # Gather common fixes based on error types
        common_fixes = self._get_common_fixes_for_error_types(error_types)
        common_fixes_text = "\n".join([f"{i+1}. {fix}" for i, fix in enumerate(common_fixes)])
        
        # Construct the prompt
        prompt = f"""
# Promela Error Fix Expert

You are an expert in fixing syntax and semantic errors in Promela code for the SPIN model checker. The Promela code below failed validation with SPIN.

## Original Promela code:

```promela
{promela_code}
```

## Error messages from SPIN:

```
{error_details}
```

{line_info}
Error types identified: {', '.join(error_types)}

{similar_errors_text}
{fix_suggestions_text}

## Common Promela Error Patterns and Fixes:

{common_fixes_text}

## Instructions:
1. Carefully analyze the error message to identify the specific issues
2. Focus on converting any C-style syntax to Promela syntax
3. Fix the error on or around the line numbers mentioned
4. Return ONLY the complete fixed Promela code with NO explanations

Fix the errors in the Promela code and return only the raw corrected code:
"""
        
        return prompt

    def _get_common_fixes_for_error_types(self, error_types: list) -> list:
        """
        Get common fixes for specific error types to include in the LLM prompt.
        
        Args:
            error_types: List of error types
            
        Returns:
            List of common fixes for the given error types
        """
        # Base fixes that apply to most Promela errors
        common_fixes = [
            "*C-style function declarations*: Replace with `inline` functions or `proctype`.",
            "*Return statements*: Replace with output parameters.",
            "*C-style if statements*: Replace with `if :: condition -> action fi` syntax.",
            "*C-style loops*: Replace with `do :: condition -> action od` syntax.",
            "*Missing semicolons*: Ensure all statements end with semicolons.",
            "*Channel declarations*: Ensure proper format `chan name = [size] of { type }`."
        ]
        
        # Add error-specific fixes
        for error_type in error_types:
            if error_type == 'syntax_error':
                common_fixes.extend([
                    "*Semicolons*: Add semicolons at the end of each statement.",
                    "*Braces*: Replace C-style braces with Promela block structure (do/od, if/fi).",
                    "*Keywords*: Check for correct Promela keywords (od instead of done, fi instead of endif)."
                ])
            
            elif error_type == 'undeclared_variable':
                common_fixes.extend([
                    "*Variable declarations*: Declare all variables before use with proper types.",
                    "*Scope issues*: Variables must be declared in the correct scope.",
                    "*Global vs local*: Consider if the variable should be global or local to a process."
                ])
            
            elif error_type == 'redeclaration':
                common_fixes.extend([
                    "*Variable name conflicts*: Rename variables to avoid redeclaration.",
                    "*Shadowing*: Avoid declaring variables with the same name in nested scopes."
                ])
            
            elif error_type == 'type_error':
                common_fixes.extend([
                    "*Type conversion*: Use appropriate Promela types (byte, int, bool).",
                    "*Type compatibility*: Ensure operations involve compatible types."
                ])
            
            elif error_type == 'array_index_error':
                common_fixes.extend([
                    "*Array access*: Use square brackets instead of parentheses for array access.",
                    "*Array bounds*: Ensure array indices are within declared bounds."
                ])
            
            elif error_type == 'channel_error':
                common_fixes.extend([
                    "*Channel declaration*: Format should be `chan name = [size] of { types }`.",
                    "*Channel operations*: Use `!` for send and `?` for receive operations.",
                    "*Message types*: Ensure message structure matches channel definition."
                ])
                
            elif error_type == 'deadlock':
                common_fixes.extend([
                    "*Deadlock prevention*: Add timeout or else conditions to break potential deadlocks.",
                    "*Process synchronization*: Review synchronization between processes.",
                    "*Channel operations*: Ensure non-blocking channel operations where needed."
                ])
                
        return common_fixes

    def process_cil_file(self, cil_file: str, output_file: str = None) -> tuple[bool, str]:
        """
        Process a CIL file and convert it to Promela.
        
        Args:
            cil_file: Path to the CIL file
            output_file: Path to save the Promela code (optional)
            
        Returns:
            Tuple of (success, message)
        """
        try:
            # Read the CIL file
            with open(cil_file, 'r') as f:
                cil_code = f.read()
            
            # Convert to Promela
            logger.info(f"Converting {cil_file} to Promela...")
            promela_code = self.convert(cil_code)
            
            # Save the initial Promela code if output file is specified
            if output_file:
                with open(output_file, 'w') as f:
                    f.write(promela_code)
                logger.info(f"Saved initial Promela code to {output_file}")
            
            # Verify the Promela code
            logger.info("Verifying Promela code...")
            success, message = self.verify_promela_code(promela_code)
            
            # Try to fix the code iteratively if there are errors
            if not success:
                success, message = self._fix_iterations(promela_code, message, output_file)
            
            return success, message
            
        except Exception as e:
            logger.error(f"Error processing CIL file: {e}")
            return False, str(e)

    def process_cil_files(self, cil_files: List[str], output_dir: str = None, with_context: bool = True) -> Dict[str, Tuple[bool, str]]:
        """
        Process multiple CIL files and convert them to Promela.
        
        Args:
            cil_files: List of paths to CIL files to process
            output_dir: Directory to save the Promela code files (optional)
            with_context: Whether to provide context from other files
            
        Returns:
            Dictionary mapping file paths to (success, message) tuples
        """
        try:
            # Create output directory if needed
            if output_dir and not os.path.exists(output_dir):
                os.makedirs(output_dir)
            
            # Dictionary to store all processed code
            processed_files = {}
            
            # First pass: read all files to collect declarations
            context = {
                'global_vars': {},
                'function_signatures': {}
            }
            
            if with_context:
                for cil_file in cil_files:
                    try:
                        with open(cil_file, 'r') as f:
                            content = f.read()
                            
                        # Extract declarations and global variables
                        file_globals = self._extract_global_variables(content)
                        file_functions = self._extract_function_signatures(content)
                        
                        # Add to collection
                        context['global_vars'].update(file_globals)
                        context['function_signatures'].update(file_functions)
                        
                    except Exception as e:
                        logger.error(f"Error processing {cil_file} during first pass: {e}")
                        processed_files[cil_file] = (False, f"Error during dependency analysis: {str(e)}")
            
            # Second pass: convert each file
            for cil_file in cil_files:
                if cil_file in processed_files and not processed_files[cil_file][0]:
                    # Skip files that failed in first pass
                    continue
                    
                try:
                    # Generate output file path
                    output_file = None
                    if output_dir:
                        base_name = os.path.basename(cil_file)
                        name_without_ext = os.path.splitext(base_name)[0]
                        output_file = os.path.join(output_dir, f"{name_without_ext}.pml")
                    
                    # Process the file
                    if with_context:
                        # Get all context except from this file
                        this_file_context = {
                            'global_vars': {},
                            'function_signatures': {}
                        }
                        
                        # Read the file
                        with open(cil_file, 'r') as f:
                            cil_code = f.read()
                            
                        # Extract declarations from this file
                        this_file_globals = self._extract_global_variables(cil_code)
                        this_file_functions = self._extract_function_signatures(cil_code)
                        
                        # Add context from other files (excluding this file's declarations)
                        for var_name, var_decl in context['global_vars'].items():
                            if var_name not in this_file_globals:
                                this_file_context['global_vars'][var_name] = var_decl
                                
                        for func_name, func_decl in context['function_signatures'].items():
                            if func_name not in this_file_functions:
                                this_file_context['function_signatures'][func_name] = func_decl
                                
                        # Convert with context
                        promela_code = self.convert(cil_code, this_file_context)
                        
                        # Save the Promela code
                        if output_file:
                            with open(output_file, 'w') as f:
                                f.write(promela_code)
                            logger.info(f"Saved Promela code to {output_file}")
                            
                        # Verify the code
                        success, message = self.verify_promela_code(promela_code)
                        
                        # Try to fix the code if there are errors
                        if not success:
                            success, message = self._fix_iterations(promela_code, message, output_file)
                            
                        processed_files[cil_file] = (success, message)
                    else:
                        # Just use the standard process_cil_file method
                        success, message = self.process_cil_file(cil_file, output_file)
                        processed_files[cil_file] = (success, message)
                    
                except Exception as e:
                    logger.error(f"Error processing {cil_file}: {e}")
                    processed_files[cil_file] = (False, str(e))
            
            # Third pass: create merged model if all files processed successfully
            if output_dir and with_context:
                all_successful = all(success for success, _ in processed_files.values())
                if all_successful:
                    self._merge_promela_files(output_dir)
            
            return processed_files
            
        except Exception as e:
            logger.error(f"Error processing multiple CIL files: {e}")
            return {file: (False, str(e)) for file in cil_files}

    def _fix_iterations(self, promela_code: str, error_message: str, output_file: str = None) -> tuple[bool, str]:
        """Run multiple fix iterations on problematic Promela code."""
        iteration = 1
        current_code = promela_code
        current_error = error_message
        
        # Track each error we've seen to avoid loops
        seen_errors = set()
        seen_errors.add(current_error)
        
        # Try to fix the code iteratively
        while iteration <= self.max_iterations:
            # Try to fix the code
            logger.info(f"Fix attempt {iteration}/{self.max_iterations}: {current_error[:100]}...")
            
            # Fix the code using LLM-based approach
            fixed_code = self.fix_promela_code(current_code, current_error)
            logger.info("Applied LLM-based fixes")
            
            # Verify the fixed code
            success, new_error = self.verify_promela_code(fixed_code)
            
            # Check if we're making progress or stuck in a loop
            if success:
                if output_file:
                    with open(output_file, 'w') as f:
                        f.write(fixed_code)
                    logger.info(f"Saved successful Promela code to {output_file}")
                
                # Record successful fix
                error_type = self.parse_spin_error(current_error).get('error_types', ['syntax_error'])[0]
                self.error_db.store_successful_fix(
                    error_type,
                    'iterative_fix',
                    promela_code,  # original code
                    fixed_code     # final fixed code
                )
                
                logger.info(f"Successfully fixed code after {iteration} iterations")
                return True, "Fixed successfully"
                
            if new_error in seen_errors or fixed_code == current_code:
                logger.warning(f"Fix attempt {iteration} did not improve the code, stopping iterations")
                break
            
            # Update for next iteration
            current_code = fixed_code
            current_error = new_error
            seen_errors.add(new_error)
            iteration += 1
            
            # Save the intermediate fixed code if output file is specified
            if output_file:
                with open(output_file, 'w') as f:
                    f.write(current_code)
                logger.info(f"Saved iteration {iteration-1} Promela code to {output_file}")
        
        # Failed to fix after max iterations
        logger.error(f"Failed to fix code after {iteration-1} iterations")
        
        # Use the best version so far
        if output_file:
            with open(output_file, 'w') as f:
                f.write(current_code)
            logger.info(f"Saved best effort Promela code to {output_file}")
        
        return False, current_error

    def _create_context_preamble(self, global_vars: Dict[str, str], function_signatures: Dict[str, str]) -> str:
        """Create a preamble with context information from other files."""
        if not global_vars and not function_signatures:
            return "/* No external context needed */"
            
        preamble = ["/* External declarations from other files */"]
        
        # Add global variables
        if global_vars:
            preamble.append("\n/* Global variables */")
            for var_name, var_decl in global_vars.items():
                # Don't include extern for Promela definitions
                if "printf" in var_name:
                    continue  # Skip printf as it's built-in in Promela
                preamble.append(var_decl)
        
        # Add function signatures - convert to inline for Promela
        if function_signatures:
            preamble.append("\n/* Function declarations */")
            for func_name, func_decl in function_signatures.items():
                if func_name != "printf" and func_name != "main":  # Skip printf and main
                    # Extract return type and parameters
                    match = re.match(r'(\w+(?:\s+\w+)*)\s+(\w+)\s*\(([^)]*)\);', func_decl)
                    if match:
                        return_type, func_name, params = match.groups()
                        
                        # For non-void functions, add an output parameter
                        if return_type.strip() != "void":
                            if params.strip():
                                params += f", {return_type} result"
                            else:
                                params = f"{return_type} result"
                        
                        # Create inline function declaration
                        inline_decl = f"inline {func_name}({params}) {{"
                        preamble.append(inline_decl)
                        preamble.append("  /* Function implementation will be provided in separate file */")
                        preamble.append("}")
        
        return "\n".join(preamble)

    def _merge_promela_files(self, output_dir: str) -> str:
        """
        Merge multiple Promela files into a single file.
        
        Args:
            output_dir: Directory containing Promela files
            
        Returns:
            Path to the merged file
        """
        merged_file_path = os.path.join(output_dir, "merged_model.pml")
        
        # Collect all .pml files
        promela_files = [f for f in os.listdir(output_dir) if f.endswith('.pml') and f != "merged_model.pml"]
        
        if not promela_files:
            logger.warning(f"No Promela files found in {output_dir} to merge")
            return None
        
        # Extract sections from all files
        declarations = []
        proctypes = []
        inits = []
        ltl_properties = []
        
        for file in promela_files:
            file_path = os.path.join(output_dir, file)
            with open(file_path, 'r') as f:
                content = f.read()
                
            # Extract declarations (at the top, outside blocks)
            decl_pattern = r'^[^{]+;'
            declarations.extend(re.findall(decl_pattern, content, re.MULTILINE))
            
            # Extract proctype definitions
            proc_pattern = r'((?:active\s+)?proctype\s+\w+\s*\([^)]*\)\s*{[^}]*})'
            proctypes.extend(re.findall(proc_pattern, content, re.DOTALL))
            
            # Extract init blocks
            init_pattern = r'(init\s*{[^}]*})'
            init_blocks = re.findall(init_pattern, content, re.DOTALL)
            if init_blocks:
                inits.extend(init_blocks)
            
            # Extract LTL properties
            ltl_pattern = r'(ltl\s+\w+\s*{[^}]*})'
            ltl_properties.extend(re.findall(ltl_pattern, content, re.DOTALL))
        
        # Remove duplicates while preserving order
        def remove_duplicates(items):
            seen = set()
            return [x for x in items if not (x in seen or seen.add(x))]
        
        declarations = remove_duplicates(declarations)
        proctypes = remove_duplicates(proctypes)
        inits = remove_duplicates(inits)
        ltl_properties = remove_duplicates(ltl_properties)
        
        # Create merged file
        with open(merged_file_path, 'w') as f:
            f.write("/* Standard defines */\n")
            f.write("#define NULL 0\n")
            f.write("#define TRUE 1\n")
            f.write("#define FALSE 0\n")
            f.write("#define MAX_SIZE 255\n\n")
            
            f.write("/* Merged Promela model from multiple files */\n\n")
            
            # Write declarations
            f.write("/* Global declarations */\n")
            for decl in declarations:
                f.write(f"{decl.strip()}\n")
            f.write("\n")
            
            # Write proctypes
            f.write("/* Process definitions */\n")
            for proc in proctypes:
                f.write(f"{proc.strip()}\n\n")
            
            # Handle init blocks
            if inits:
                f.write("/* Combined initialization */\n")
                if len(inits) == 1:
                    # Just one init block, use it directly
                    f.write(f"{inits[0].strip()}\n\n")
                else:
                    # Multiple init blocks, merge them
                    f.write("init {\n")
                    for i, init_block in enumerate(inits):
                        # Extract the body of each init block
                        body_match = re.search(r'init\s*{(.*)}', init_block, re.DOTALL)
                        if body_match:
                            body = body_match.group(1).strip()
                            f.write(f"  /* Init block from file {i+1} */\n")
                            f.write(f"  d_step {{\n    {body}\n  }}\n")
                    f.write("}\n\n")
            
            # Write LTL properties
            if ltl_properties:
                f.write("/* Verification properties */\n")
                for ltl in ltl_properties:
                    f.write(f"{ltl.strip()}\n\n")
        
        logger.info(f"Merged Promela model created at {merged_file_path}")
        return merged_file_path

    def _extract_global_variables(self, cil_code: str) -> Dict[str, str]:
        """Extract global variables from CIL code."""
        global_vars = {}
        
        # Find global variable declarations
        # Pattern: type name = value; OR type name;
        var_pattern = r'^(?:extern\s+)?(?:const\s+)?(\w+(?:\s+\w+)*)\s+(\w+)(?:\s*=\s*([^;]+))?;'
        for match in re.finditer(var_pattern, cil_code, re.MULTILINE):
            var_type = match.group(1)
            var_name = match.group(2)
            var_value = match.group(3)
            
            # Skip if it's a function declaration (has parentheses)
            if re.search(rf'{var_name}\s*\(', cil_code):
                continue
                
            if var_value:
                global_vars[var_name] = f"{var_type} {var_name} = {var_value};"
            else:
                global_vars[var_name] = f"{var_type} {var_name};"
        
        # Find array declarations
        array_pattern = r'^(?:extern\s+)?(?:const\s+)?(\w+(?:\s+\w+)*)\s+(\w+)\s*\[([^\]]*)\](?:\s*=\s*{([^}]*)})?;'
        for match in re.finditer(array_pattern, cil_code, re.MULTILINE):
            array_type = match.group(1)
            array_name = match.group(2)
            array_size = match.group(3)
            array_init = match.group(4)
            
            if array_init:
                global_vars[array_name] = f"{array_type} {array_name}[{array_size}] = {{{array_init}}};"
            else:
                global_vars[array_name] = f"{array_type} {array_name}[{array_size}];"
        
        return global_vars

    def _extract_function_signatures(self, cil_code: str) -> Dict[str, str]:
        """Extract function signatures from CIL code."""
        function_signatures = {}
        
        # Function declaration pattern
        func_pattern = r'^(?:extern\s+)?(?:static\s+)?(\w+(?:\s+\w+)*)\s+(\w+)\s*\(([^)]*)\)\s*(?:{|;)'
        for match in re.finditer(func_pattern, cil_code, re.MULTILINE):
            return_type = match.group(1)
            func_name = match.group(2)
            parameters = match.group(3)
            
            # Skip if it's a variable declaration that looks like a function
            if return_type in ["if", "while", "for", "switch", "do"]:
                continue
                
            function_signatures[func_name] = f"{return_type} {func_name}({parameters});"
        
        return function_signatures

def main():
    """
    Main function for the CIL to Promela converter.
    """
    # Set up argument parser
    parser = argparse.ArgumentParser(description='Convert CIL code to Promela and verify with Spin')
    parser.add_argument('cil_file', help='Path to the CIL file to convert')
    parser.add_argument('--output', '-o', help='Path to save the Promela code')
    parser.add_argument('--api-key', default=DEFAULT_API_KEY, help='API key for the language model')
    parser.add_argument('--model', default=DEFAULT_MODEL, help='Language model to use')
    parser.add_argument('--spin-path', default='spin', help='Path to the Spin executable')
    parser.add_argument('--verification-target', choices=['safety', 'liveness', 'deadlock', 'general'], default='general', help='Verification target')
    parser.add_argument('--advanced-features', action='store_true', help='Enable advanced Spin features')
    parser.add_argument('--reduction-techniques', nargs='+', choices=['partial_order', 'collapse', 'minimize', 'bitstate', 'fairness', 'symmetry', 'data_flow', 'invariant', 'progress', 'acceptance'], help='Model reduction techniques to apply')
    parser.add_argument('--ltl-properties', help='Path to file containing custom LTL properties')
    parser.add_argument('--log-level', choices=['DEBUG', 'INFO', 'WARNING', 'ERROR', 'CRITICAL'], default='INFO', help='Logging level')
    parser.add_argument('--max-iterations', type=int, default=10, help='Maximum number of iterations for fixing code')
    parser.add_argument('--verbose', action='store_true', help='Enable verbose logging')
    
    # Parse arguments
    args = parser.parse_args()
    
    # Set up logging
    log_level = logging.DEBUG if args.verbose else getattr(logging, args.log_level)
    logging.basicConfig(
        level=log_level,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    )
    
    try:
        # Initialize the converter
        converter = CILToPromelaConverter(
            api_key=args.api_key,
            model=args.model,
            spin_path=args.spin_path,
            verification_target=args.verification_target,
            advanced_features=args.advanced_features,
            reduction_techniques=args.reduction_techniques,
            max_iterations=args.max_iterations
        )
        
        # Load custom LTL properties if specified
        if args.ltl_properties:
            try:
                with open(args.ltl_properties, 'r') as f:
                    ltl_properties = f.read()
                converter.custom_properties = ltl_properties
                logger.info(f"Loaded custom LTL properties from {args.ltl_properties}")
            except Exception as e:
                logger.warning(f"Failed to load custom LTL properties: {e}")
        
        # Process the CIL file
        success, message = converter.process_cil_file(args.cil_file, args.output)
        
        # Print the result
        if success:
            print("Verification successful!")
            print(message)
            # Note which model was actually used
            used_model = converter.fallback_model if converter.using_fallback else converter.model
            print(f"Conversion completed using model: {used_model}")
        else:
            print("Verification failed!")
            print(message)
            sys.exit(1)
            
    except Exception as e:
        logger.error(f"Error: {e}")
        sys.exit(1)

if __name__ == '__main__':
    main()