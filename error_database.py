"""
Error database for storing and retrieving error information.
"""

import json
import os
import datetime
import logging
import re
from typing import List, Dict, Any, Optional
from datetime import datetime

logger = logging.getLogger(__name__)

class ErrorDatabase:
    """
    Database for storing and retrieving error information.
    """
    def __init__(self, db_file: str = None):
        """Initialize the error database."""
        self.logger = logging.getLogger('ErrorDatabase')
        self.db_file = db_file or os.path.join(os.path.dirname(__file__), 'error_database.json')
        self.data_dir = os.path.dirname(self.db_file)
        
        # Create data directory if it doesn't exist
        os.makedirs(self.data_dir, exist_ok=True)
        
        # Initialize data structures
        self.error_patterns = {}
        self.fix_prompts = {}
        self.successful_fixes = {}
        self.errors = self._load_db()
        
        # Initialize common fix prompts
        self.initialize_common_fix_prompts()
    
    def _load_db(self):
        """Load the error database from file."""
        if os.path.exists(self.db_file):
            try:
                with open(self.db_file, 'r') as f:
                    return json.load(f)
            except json.JSONDecodeError:
                self.logger.error(f"Error decoding JSON from {self.db_file}. Starting with empty database.")
                return {'errors': [], 'fixes': []}
        else:
            return {'errors': [], 'fixes': []}
    
    def _save_db(self):
        """Save the error database to file."""
        try:
            with open(self.db_file, 'w') as f:
                json.dump(self.errors, f, indent=2)
        except Exception as e:
            self.logger.error(f"Error saving database: {e}")
    
    def _save_data(self):
        """Save data to separate files for error patterns, fix prompts, etc."""
        try:
            error_file = os.path.join(self.data_dir, "error_patterns.json")
            fix_file = os.path.join(self.data_dir, "fix_prompts.json")
            success_file = os.path.join(self.data_dir, "successful_fixes.json")
            
            with open(error_file, 'w') as f:
                json.dump(self.error_patterns, f, indent=2)
            
            with open(fix_file, 'w') as f:
                json.dump(self.fix_prompts, f, indent=2)
            
            with open(success_file, 'w') as f:
                json.dump(self.successful_fixes, f, indent=2)
                
        except Exception as e:
            self.logger.error(f"Error saving data: {e}")
    
    def add_error(self, error_type: str, error_message: str, promela_code: str = None):
        """
        Add an error to the database.
        
        Args:
            error_type: Type of error (e.g., 'syntax_error')
            error_message: Error message
            promela_code: Promela code that caused the error (optional)
        """
        error_entry = {
            'type': error_type,
            'message': error_message,
            'timestamp': datetime.now().isoformat(),
        }
        if promela_code:
            error_entry['code'] = promela_code
        
        self.errors['errors'].append(error_entry)
        self._save_db()
        
        # Also store in error patterns
        self.store_error_pattern(error_type, self._extract_context(error_message), promela_code or "")
    
    def _extract_context(self, error_message: str) -> str:
        """Extract context from error message."""
        # Try to identify the context (like which statement has the error)
        if "if" in error_message.lower():
            return "if statement"
        elif "do" in error_message.lower() or "while" in error_message.lower():
            return "loop statement"
        elif "chan" in error_message.lower():
            return "channel operation"
        elif "array" in error_message.lower() or "[" in error_message:
            return "array access"
        elif "redeclaration" in error_message.lower():
            return "variable declaration"
        else:
            return "unknown context"
    
    def store_error_pattern(self, error_type: str, error_context: str, code: str):
        """
        Store a new error pattern.
        
        Args:
            error_type: Type of error (syntax, semantic, etc.)
            error_context: Context where error occurred
            code: Code that caused the error
        """
        timestamp = datetime.now().isoformat()
        
        if error_type not in self.error_patterns:
            self.error_patterns[error_type] = []
            
        self.error_patterns[error_type].append({
            "timestamp": timestamp,
            "context": error_context,
            "code": code
        })
        
        self._save_data()
    
    def add_fix(self, error_type: str, fix_type: str, original_code: str, fixed_code: str):
        """
        Add a fix to the database.
        
        Args:
            error_type: Type of error (e.g., 'syntax_error')
            fix_type: Type of fix (e.g., 'llm', 'manual')
            original_code: Original code with the error
            fixed_code: Fixed code
        """
        fix_entry = {
            'error_type': error_type,
            'fix_type': fix_type,
            'original_code': original_code,
            'fixed_code': fixed_code,
            'timestamp': datetime.now().isoformat(),
        }
        
        self.errors['fixes'].append(fix_entry)
        self._save_db()
        
        # Also store as a fix prompt and successful fix
        self.store_fix_prompt(error_type, fix_type, 
                             f"Fix for {error_type}", 
                             original_code, fixed_code)
        self.store_successful_fix(error_type, fix_type, 
                                 original_code, fixed_code)
    
    def store_fix_prompt(self, error_type: str, fix_type: str, prompt: str, original_code: str, fixed_code: str):
        """
        Store a fix prompt.
        
        Args:
            error_type: Type of error
            fix_type: Type of fix
            prompt: The fix prompt
            original_code: Original code with error
            fixed_code: Fixed code
        """
        timestamp = datetime.now().isoformat()
        
        if error_type not in self.fix_prompts:
            self.fix_prompts[error_type] = []
            
        self.fix_prompts[error_type].append({
            "timestamp": timestamp,
            "fix_type": fix_type,
            "prompt": prompt,
            "original_code": original_code,
            "fixed_code": fixed_code
        })
        
        self._save_data()
    
    def store_successful_fix(self, error_type: str, fix_type: str, original_code: str, fixed_code: str):
        """
        Store a successful fix.
        
        Args:
            error_type: Type of error
            fix_type: Type of fix
            original_code: Original code with error
            fixed_code: Fixed code
        """
        timestamp = datetime.now().isoformat()
        
        if error_type not in self.successful_fixes:
            self.successful_fixes[error_type] = []
            
        self.successful_fixes[error_type].append({
            "timestamp": timestamp,
            "fix_type": fix_type,
            "original_code": original_code,
            "fixed_code": fixed_code
        })
        
        self._save_data()
    
    def get_similar_errors(self, error_type: str, error_message: str = None, limit: int = 5):
        """
        Get similar errors from the database.
        
        Args:
            error_type: Type of error (e.g., 'syntax_error')
            error_message: Error message (optional)
            limit: Maximum number of errors to return
            
        Returns:
            List of similar errors
        """
        similar_errors = []
        
        for error in self.errors['errors']:
            if error['type'] == error_type:
                # If error message is provided, check similarity
                if error_message and 'message' in error:
                    # Simple similarity check - could be improved
                    if error_message.lower() in error['message'].lower() or \
                       error['message'].lower() in error_message.lower():
                        similar_errors.append(error)
                else:
                    similar_errors.append(error)
        
        # Sort by timestamp (newest first) and limit
        similar_errors.sort(key=lambda x: x.get('timestamp', ''), reverse=True)
        return similar_errors[:limit]
    
    def get_fix_prompts(self, error_type: str, limit: int = 3):
        """
        Get fix prompts for an error type.
        
        Args:
            error_type: Type of error
            limit: Maximum number of prompts to return
            
        Returns:
            List of fix prompts
        """
        prompts = self.fix_prompts.get(error_type, [])
        if not prompts:
            return []
            
        # Sort by timestamp (newest first) and limit
        prompts.sort(key=lambda x: x.get('timestamp', ''), reverse=True)
        return prompts[:limit]
    
    def get_similar_errors_from_patterns(self, error_info: Dict[str, Any]) -> List[Dict[str, Any]]:
        """
        Get similar errors from the error patterns.
        
        Args:
            error_info: Current error information
            
        Returns:
            List of similar errors
        """
        error_type = error_info.get('type')
        if not error_type:
            return []
            
        return self.error_patterns.get(error_type, [])
    
    def get_successful_fixes(self, error_type: str) -> List[Dict[str, Any]]:
        """
        Get successful fixes for an error type.
        
        Args:
            error_type: Type of error
            
        Returns:
            List of successful fixes
        """
        return self.successful_fixes.get(error_type, [])
    
    def get_fixes_for_error(self, error_type: str, limit: int = 5):
        """
        Get fixes for a specific error type.
        
        Args:
            error_type: Type of error (e.g., 'syntax_error')
            limit: Maximum number of fixes to return
            
        Returns:
            List of fixes
        """
        fixes = []
        
        for fix in self.errors['fixes']:
            if fix['error_type'] == error_type:
                fixes.append(fix)
        
        # Sort by timestamp (newest first) and limit
        fixes.sort(key=lambda x: x.get('timestamp', ''), reverse=True)
        return fixes[:limit]
    
    def get_fix_prompts(self, error_type: str, limit: int = 3):
        """
        Generate fix prompts based on successful fixes for an error type.
        
        Args:
            error_type: Type of error (e.g., 'syntax_error')
            limit: Maximum number of prompts to return
            
        Returns:
            List of fix prompts
        """
        fixes = self.get_fixes_for_error(error_type, limit=10)
        prompts = []
        
        for fix in fixes:
            # Generate a diff or highlight the changes
            original = fix.get('original_code', '')
            fixed = fix.get('fixed_code', '')
            
            # Skip if missing code
            if not original or not fixed:
                continue
                
            # Create a prompt based on the fix
            prompt = {
                'prompt': f"""
When fixing {error_type} errors, consider this example:

Original code with error:

Apply similar fixes to the current code.
                """,
                'timestamp': fix.get('timestamp', '')
            }
            
            prompts.append(prompt)
            
            # Break if we have enough prompts
            if len(prompts) >= limit:
                break
        
        return prompts
    
    def classify_error(self, error_message: str):
        """
        Classify an error message into error types.
        
        Args:
            error_message: Error message from SPIN
            
        Returns:
            List of error types
        """
        error_types = []
        lower_msg = error_message.lower()
        
        # Check for various error patterns
        error_patterns = {
            'syntax_error': [
                'syntax error', 
                'expected', 
                'found',
                'bad assignment', 
                'missing semicolon'
            ],
            'undeclared_variable': [
                'undeclared variable', 
                'not defined', 
                'undefined', 
                'unknown identifier'
            ],
            'redeclaration': [
                'redeclaration', 
                'already defined', 
                'duplicate'
            ],
            'type_error': [
                'type error', 
                'type mismatch', 
                'incompatible types', 
                'cannot convert'
            ],
            'channel_error': [
                'invalid channel', 
                'channel access', 
                'wrong channel type'
            ],
            'array_index_error': [
                'array index', 
                'out of bounds', 
                'invalid subscript'
            ],
            'deadlock': [
                'deadlock', 
                'invalid end state'
            ],
            'assertion_violation': [
                'assertion violated', 
                'assertion failed'
            ],
            'verification': [
                'verification failed',
                'never claim', 
                'ltl formula'
            ]
        }
        
        # Check each pattern
        for error_type, patterns in error_patterns.items():
            for pattern in patterns:
                if pattern in lower_msg:
                    error_types.append(error_type)
                    break
        
        # If no specific type was identified, mark as other
        if not error_types:
            error_types.append('other')
        
        return error_types
    
    def clear_database(self):
        """Clear the error database."""
        self.errors = {'errors': [], 'fixes': []}
        self.error_patterns = {}
        self.fix_prompts = {}
        self.successful_fixes = {}
        self._save_db()
        self._save_data()
    
    def initialize_common_fix_prompts(self):
        """Initialize common fix prompts for various error types."""
        common_fix_prompts = {
            "syntax_error": {
                "printf": {
                    "description": "Fix printf format string usage",
                    "examples": [
                        {
                            "original": 'printf("Value: %d\\n", x)',
                            "fixed": 'printf("Value: "); printf("%d", x); printf("\\n")'
                        }
                    ]
                },
                "process_declaration": {
                    "description": "Fix process declarations",
                    "examples": [
                        {
                            "original": "void process() { ... }",
                            "fixed": "proctype process() { ... }"
                        }
                    ]
                },
                "channel_declaration": {
                    "description": "Fix channel declarations",
                    "examples": [
                        {
                            "original": "chan ch = [2] of {int}",
                            "fixed": "chan ch = [2] of { int }"
                        }
                    ]
                }
            },
            "undeclared_variable": {
                "missing_declaration": {
                    "description": "Add missing variable declarations",
                    "examples": [
                        {
                            "original": "x = 10;",
                            "fixed": "int x;\nx = 10;"
                        }
                    ]
                }
            },
            "redeclaration": {
                "variable_redeclaration": {
                    "description": "Fix variable redeclarations",
                    "examples": [
                        {
                            "original": "int x;\nint x;",
                            "fixed": "int x;"
                        }
                    ]
                }
            },
            "type_error": {
                "type_mismatch": {
                    "description": "Fix type mismatches",
                    "examples": [
                        {
                            "original": "byte x;\nx = -10;",
                            "fixed": "int x;\nx = -10;"
                        }
                    ]
                }
            },
            "channel_error": {
                "channel_usage": {
                    "description": "Fix channel usage",
                    "examples": [
                        {
                            "original": "ch!msg;",
                            "fixed": "ch!msg"
                        }
                    ]
                }
            },
            "array_index_error": {
                "array_bounds": {
                    "description": "Fix array bounds checking",
                    "examples": [
                        {
                            "original": "arr[i] = x;",
                            "fixed": "if\n:: i < N -> arr[i] = x\n:: else -> assert(false)\nfi"
                        }
                    ]
                }
            }
        }
        
        # Store the common fix prompts if the database is empty
        if not self.fix_prompts:
            for error_type, prompts in common_fix_prompts.items():
                for fix_type, data in prompts.items():
                    for example in data["examples"]:
                        self.store_fix_prompt(
                            error_type,
                            fix_type,
                            data["description"],
                            example["original"],
                            example["fixed"]
                        )


def main():
    """Main function to demonstrate database usage."""
    # Initialize database
    db = ErrorDatabase()
    
    # Add some test cases
    db.add_error("syntax_error", "Syntax error: expected ';' found '}'", "if (x > 0) { y = 1 }")
    db.add_fix("syntax_error", "manual", "if (x > 0) { y = 1 }", "if\n:: x > 0 -> y = 1\nfi")
    
    # Print some information
    print("Error types in database:")
    for error_type in db.error_patterns.keys():
        print(f"- {error_type}")
    
    # Get fix prompts
    fix_prompts = db.get_fix_prompts("syntax_error")
    if fix_prompts:
        print("\nFix prompt example:")
        print(fix_prompts[0].get('prompt', 'No prompt available'))


if __name__ == '__main__':
    main()