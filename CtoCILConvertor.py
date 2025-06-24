#!/usr/bin/env python3
"""
C to CIL (C Intermediate Language) Converter

This script converts C code to CIL format based on patterns observed in the test cases.
CIL (C Intermediate Language) is an intermediate representation of C code that is simpler
and more uniform than C, making it easier to analyze and transform.
"""

import os
import re
import sys
import argparse
from typing import List, Dict, Tuple


class CToCILConverter:
    """Class to convert C code to CIL format"""

    def __init__(self):
        self.function_declarations = []
        self.global_variables = []
        self.structs = []
        self.typedefs = []
        self.enums = []
        self.typedef_enums = []
        self.processed_declarations = set()  # Track processed declarations to avoid duplicates

    def convert(self, c_code: str) -> str:
        """Convert C code to CIL format"""
        print("Starting conversion...")
        
        # Preprocessing: We'll preserve comments for better readability
        print("Step 1: Preserving comments...")
        preprocessed_code = self._preserve_comments(c_code)
        
        print("Step 2: Removing preprocessor directives...")
        preprocessed_code = self._remove_preprocessor_directives(preprocessed_code)
        
        # Structure analysis
        print("Step 3: Analyzing structure...")
        self._analyze_structure(preprocessed_code)
        
        # Apply transformations
        print("Step 4: Transforming to CIL...")
        cil_code = self._transform_to_cil(preprocessed_code)
        
        # Add comment header
        print("Step 5: Adding header...")
        cil_code = f"/* CIL test file */\n\n{cil_code}"
        
        print("Conversion complete!")
        return cil_code

    def _preserve_comments(self, code: str) -> str:
        """Preserve C comments while removing preprocessor directives"""
        # This function keeps the comments instead of removing them
        return code

    def _remove_preprocessor_directives(self, code: str) -> str:
        """Remove preprocessor directives and keep track of #includes"""
        # Remove #include, #define, #pragma, etc.
        pattern = r'^\s*#.*?$'
        return re.sub(pattern, '', code, flags=re.MULTILINE)

    def _analyze_structure(self, code: str) -> None:
        """Analyze C code structure to extract functions, variables, and types"""
        print("  - Extracting function declarations...")
        # Extract function declarations - simplified pattern to avoid backtracking issues
        # The old pattern could cause catastrophic backtracking with nested braces
        # function_pattern = r'(\w+)\s+(\w+)\s*\(([^)]*)\)\s*{([^{}]*({[^{}]*})*[^{}]*)*}'
        
        # Use a simpler pattern first to identify function signatures
        function_pattern = r'(\w+)\s+(\w+)\s*\(([^)]*)\)\s*{'
        function_matches = re.finditer(function_pattern, code)
        
        self.function_declarations = []
        for match in function_matches:
            return_type = match.group(1)
            func_name = match.group(2)
            params = match.group(3)
            self.function_declarations.append((return_type, func_name, params, ''))  # Empty body for now
            
        print(f"    Found {len(self.function_declarations)} function declarations")
        
        # Rest of the function remains the same
        # Extract global variables (excluding function declarations)
        print("  - Extracting global variables...")
        global_var_pattern = r'^\s*(\w+)\s+(\w+)(?:\s*=\s*[^;]+)?;'
        global_vars = re.findall(global_var_pattern, code, re.MULTILINE)
        
        # Filter out function names
        func_names = [func[1] for func in self.function_declarations if len(func) > 1]
        self.global_variables = [var for var in global_vars 
                                if var[0] not in ['void', 'static', 'typedef', 'struct', 'enum']
                                and var[1] not in func_names]
        print(f"    Found {len(self.global_variables)} global variables")
        
        # Extract struct definitions
        print("  - Extracting struct definitions...")
        struct_pattern = r'struct\s+(\w+)\s*{([^}]*)};'
        self.structs = re.findall(struct_pattern, code)
        print(f"    Found {len(self.structs)} struct definitions")
        
        # Extract typedefs
        print("  - Extracting typedefs...")
        typedef_pattern = r'typedef\s+([^;]+);'
        self.typedefs = re.findall(typedef_pattern, code)
        print(f"    Found {len(self.typedefs)} typedefs")
        
        # Extract enum definitions
        print("  - Extracting enum definitions...")
        enum_pattern = r'enum\s+(\w+)\s*{([^}]*)}'
        self.enums = re.findall(enum_pattern, code)
        print(f"    Found {len(self.enums)} enum definitions")
        
        # Extract typedef enum definitions  
        print("  - Extracting typedef enum definitions...")
        typedef_enum_pattern = r'typedef\s+enum\s*{([^}]*?)}\s*(\w+)\s*;'
        self.typedef_enums = re.findall(typedef_enum_pattern, code)
        print(f"    Found {len(self.typedef_enums)} typedef enum definitions")
        print("  - Structure analysis complete")

    def _transform_to_cil(self, code: str) -> str:
        """Apply CIL transformations to the C code"""
        # Start with cleaned code
        cil_code = code
        
        # Normalize variable declarations
        print("  - Normalizing variable declarations...")
        cil_code = self._normalize_variable_declarations(cil_code)
        
        # Normalize function declarations and parameters
        print("  - Normalizing function declarations...")
        cil_code = self._normalize_function_declarations(cil_code)
        
        # Normalize control structures
        print("  - Normalizing control structures...")
        cil_code = self._normalize_control_structures(cil_code)
        
        # Normalize struct access
        print("  - Normalizing struct access...")
        cil_code = self._normalize_struct_access(cil_code)
        
        # Normalize array access
        print("  - Normalizing array access...")
        cil_code = self._normalize_array_access(cil_code)
        
        # Normalize pointer operations
        print("  - Normalizing pointer operations...")
        cil_code = self._normalize_pointer_operations(cil_code)
        
        # Format the code
        print("  - Formatting code...")
        cil_code = self._format_code(cil_code)
        
        return cil_code

    def _normalize_function_declarations(self, code: str) -> str:
        """Normalize function declarations to CIL format"""
        function_pattern = r'(\w+)\s+(\w+)\s*\(([^)]*)\)\s*{'
        
        def normalize_function(match):
            return_type = match.group(1)
            function_name = match.group(2)
            params_str = match.group(3)
            
            # Skip if empty parameters
            if not params_str.strip():
                return f"{return_type} {function_name}() {{"
            
            # Parse parameters with respect to arrays and complex types
            params = []
            current_param = ""
            bracket_level = 0
            brace_level = 0
            
            for char in params_str:
                if char == '[':
                    bracket_level += 1
                    current_param += char
                elif char == ']':
                    bracket_level -= 1
                    current_param += char
                elif char == '{':
                    brace_level += 1
                    current_param += char
                elif char == '}':
                    brace_level -= 1
                    current_param += char
                elif char == ',' and bracket_level == 0 and brace_level == 0:
                    if current_param.strip():
                        params.append(current_param.strip())
                    current_param = ""
                else:
                    current_param += char
            
            # Add the last parameter
            if current_param.strip():
                params.append(current_param.strip())
            
            # Clean parameters (remove const, etc.)
            clean_params = []
            for param in params:
                param = re.sub(r'const\s+', '', param)
                param = re.sub(r'volatile\s+', '', param)
                param = re.sub(r'register\s+', '', param)
                clean_params.append(param)
            
            # Format function declaration
            formatted_params = ", ".join(clean_params)
            return f"{return_type} {function_name}({formatted_params}) {{"
        
        return re.sub(function_pattern, normalize_function, code)

    def _normalize_variable_declarations(self, code: str) -> str:
        """Normalize variable declarations to CIL format"""
        # In CIL, variable declarations are simplified
        # Example: int x, y, z; -> int x; int y; int z;
        
        def process_declaration(match):
            type_name = match.group(1)
            full_declaration = match.group(2)
            
            # Skip if already processed
            match_text = match.group(0)
            if match_text in self.processed_declarations:
                return match_text
            self.processed_declarations.add(match_text)
            
            # Split by commas, but ignore commas in initializers like {1, 2, 3}
            vars_to_process = []
            current_var = ""
            brace_level = 0
            bracket_level = 0
            
            for char in full_declaration:
                if char == '{':
                    brace_level += 1
                    current_var += char
                elif char == '}':
                    brace_level -= 1
                    current_var += char
                elif char == '[':
                    bracket_level += 1
                    current_var += char
                elif char == ']':
                    bracket_level -= 1
                    current_var += char
                elif char == ',' and brace_level == 0 and bracket_level == 0:
                    vars_to_process.append(current_var.strip())
                    current_var = ""
                else:
                    current_var += char
            
            # Add the last variable
            if current_var.strip():
                vars_to_process.append(current_var.strip())
            
            # Only split if multiple variables
            if len(vars_to_process) <= 1:
                return match_text
                
            result = []
            for var in vars_to_process:
                result.append(f"{type_name} {var};")
            
            return '\n'.join(result)
        
        # Process variable declarations, but not function parameters
        # Expanded to include more C types including typedefs and enum types
        var_pattern = r'(?<!\()\s*(int|float|char|double|long|short|unsigned|bool|void|[A-Za-z_][A-Za-z0-9_]*)\s+([^;()]+);'
        result = re.sub(var_pattern, process_declaration, code)
        
        return result

    def _normalize_control_structures(self, code: str) -> str:
        """Normalize control structures to CIL format"""
        # In CIL, control structures have explicit braces
        # We'll add braces to statements without them
        
        print("    - Processing if statements...")
        # Fix if statements without braces - limit greediness with +? pattern
        code = re.sub(r'if\s*\(([^)]+)\)\s*([^{;].*?);', lambda m: f'if ({m.group(1)}) {{{m.group(2)};}}', code)
        code = re.sub(r'else\s*([^{;].*?);', lambda m: f'else {{{m.group(1)};}}', code)
        
        print("    - Processing for loops...")
        # Fix for loops without braces - limit greediness with +? pattern
        code = re.sub(r'for\s*\(([^)]+)\)\s*([^{;].*?);', lambda m: f'for ({m.group(1)}) {{{m.group(2)};}}', code)
        
        print("    - Processing while loops...")
        # Fix while loops without braces - limit greediness with +? pattern
        code = re.sub(r'while\s*\(([^)]+)\)\s*([^{;].*?);', lambda m: f'while ({m.group(1)}) {{{m.group(2)};}}', code)
        
        print("    - Processing do-while loops...")
        # Fix do-while loops without braces - limit greediness with +? pattern
        code = re.sub(r'do\s*([^{;].*?);\s*while\s*\(([^)]+)\);', lambda m: f'do {{{m.group(1)};}} while ({m.group(2)});', code)
        
        print("    - Control structure normalization complete")
        return code

    def _normalize_struct_access(self, code: str) -> str:
        """Normalize struct access to CIL format"""
        # In CIL, struct access remains the same
        return code

    def _normalize_array_access(self, code: str) -> str:
        """Normalize array access to CIL format"""
        # In CIL, array access remains the same
        return code

    def _normalize_pointer_operations(self, code: str) -> str:
        """Normalize pointer operations to CIL format"""
        # In CIL, pointer declarations use the form "int* p" not "int *p"
        code = re.sub(r'(\w+)\s+\*\s*(\w+)', r'\1* \2', code)
        
        return code

    def _format_code(self, code: str) -> str:
        """Format the code for better readability"""
        # Remove excessive blank lines
        print("    - Removing excessive blank lines...")
        code = re.sub(r'\n\s*\n\s*\n', '\n\n', code)
        
        # Ensure braces are on the same line for functions
        print("    - Formatting function braces...")
        code = re.sub(r'(\w+\s+\w+\s*\([^)]*\))\s*\n\s*{', r'\1 {', code)
        
        # Add space after keywords
        print("    - Adding space after keywords...")
        code = re.sub(r'\b(if|for|while|switch|return|else)\(', r'\1 (', code)
        
        # Normalize spacing around operators
        print("    - Normalizing operator spacing...")
        code = re.sub(r'(\w+)\s*=\s*(\w+)', r'\1 = \2', code)
        
        # Ensure consistent indentation (this is a basic implementation)
        print("    - Applying indentation...")
        lines = code.split('\n')
        indent_level = 0
        formatted_lines = []
        
        for line in lines:
            # Adjust indent level based on braces
            stripped = line.strip()
            
            # Don't change empty lines
            if not stripped:
                formatted_lines.append('')
                continue
                
            # Closing braces decrease indent before the line
            if stripped.startswith('}'):
                indent_level = max(0, indent_level - 1)
            
            # Add the line with proper indentation
            formatted_lines.append('  ' * indent_level + stripped)
            
            # Opening braces increase indent after the line
            if stripped.endswith('{'):
                indent_level += 1
            # Closing braces decrease indent after the line (if alone)
            elif stripped == '}':
                indent_level = max(0, indent_level - 1)
        
        print("    - Formatting complete")
        return '\n'.join(formatted_lines)


def process_file(input_file: str, output_file: str) -> None:
    """Process a single C file and convert it to CIL"""
    try:
        print(f"Processing file: {input_file}")
        with open(input_file, 'r') as f:
            c_code = f.read()
            
        print(f"File read successfully, length: {len(c_code)} chars")
        converter = CToCILConverter()
        cil_code = converter.convert(c_code)
        
        print(f"Writing output to: {output_file}")
        os.makedirs(os.path.dirname(output_file) or '.', exist_ok=True)
        with open(output_file, 'w') as f:
            f.write(cil_code)
            
        print(f"Successfully converted {input_file} to {output_file}")
        
    except Exception as e:
        print(f"Error processing file {input_file}: {str(e)}")
        sys.exit(1)


def process_directory(input_dir: str, output_dir: str) -> None:
    """Process all C files in a directory and convert them to CIL"""
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
        
    for root, _, files in os.walk(input_dir):
        for file in files:
            if file.endswith('.c'):
                input_file = os.path.join(root, file)
                
                # Create relative path to maintain directory structure
                rel_path = os.path.relpath(input_file, input_dir)
                output_file = os.path.join(output_dir, rel_path.replace('.c', '.cil'))
                
                # Create output directory if it doesn't exist
                os.makedirs(os.path.dirname(output_file), exist_ok=True)
                
                process_file(input_file, output_file)


def main():
    parser = argparse.ArgumentParser(description='Convert C code to CIL format')
    parser.add_argument('input', help='Input C file or directory')
    parser.add_argument('-o', '--output', help='Output CIL file or directory')
    parser.add_argument('-r', '--recursive', action='store_true',
                        help='Process directories recursively')
    
    args = parser.parse_args()
    
    if os.path.isfile(args.input):
        # Process a single file
        output_file = args.output if args.output else args.input.replace('.c', '.cil')
        process_file(args.input, output_file)
    
    elif os.path.isdir(args.input) and args.recursive:
        # Process a directory recursively
        output_dir = args.output if args.output else os.path.join(args.input, 'cil_output')
        process_directory(args.input, output_dir)
    
    elif os.path.isdir(args.input):
        # Process only C files in the root of the directory
        output_dir = args.output if args.output else os.path.join(args.input, 'cil_output')
        
        if not os.path.exists(output_dir):
            os.makedirs(output_dir)
            
        for file in os.listdir(args.input):
            if file.endswith('.c'):
                input_file = os.path.join(args.input, file)
                output_file = os.path.join(output_dir, file.replace('.c', '.cil'))
                process_file(input_file, output_file)
    
    else:
        print(f"Error: {args.input} is neither a file nor a directory")
        sys.exit(1)


if __name__ == "__main__":
    main() 