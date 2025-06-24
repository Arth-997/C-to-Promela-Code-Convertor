import os
import json
import logging
from typing import Dict, List, Any, Optional
from datetime import datetime

# Set up logging
logging.basicConfig(level=logging.INFO,
                   format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

class TestCaseManager:
    def __init__(self, test_results_dir: str):
        """
        Initialize the test case manager.
        
        Args:
            test_results_dir: Directory containing test results
        """
        self.test_results_dir = test_results_dir
        self.error_patterns = {}
        self.fix_patterns = {}
        self._load_test_results()
        
    def _load_test_results(self):
        """Load all test results from the directory."""
        if not os.path.exists(self.test_results_dir):
            logger.warning(f"Test results directory {self.test_results_dir} does not exist")
            return
            
        # Load all JSON files in the directory
        for filename in os.listdir(self.test_results_dir):
            if filename.endswith('.json'):
                try:
                    with open(os.path.join(self.test_results_dir, filename), 'r') as f:
                        data = json.load(f)
                        self._process_test_results(data)
                except Exception as e:
                    logger.error(f"Error loading {filename}: {e}")
                    
    def _process_test_results(self, data: Dict[str, Any]):
        """
        Process test results and extract error and fix patterns.
        
        Args:
            data: Test results data
        """
        for test_result in data.get('test_results', []):
            # Process error patterns
            for error in test_result.get('error_patterns', []):
                error_key = self._get_error_key(error)
                if error_key not in self.error_patterns:
                    self.error_patterns[error_key] = {
                        'count': 0,
                        'examples': [],
                        'fixes': []
                    }
                
                self.error_patterns[error_key]['count'] += 1
                self.error_patterns[error_key]['examples'].append({
                    'test_name': test_result['test_name'],
                    'error': error,
                    'timestamp': test_result['timestamp']
                })
                
            # Process successful fixes
            if test_result.get('success'):
                for error in test_result.get('error_patterns', []):
                    error_key = self._get_error_key(error)
                    if error_key in self.error_patterns:
                        # Record the successful fix
                        self.error_patterns[error_key]['fixes'].append({
                            'test_name': test_result['test_name'],
                            'timestamp': test_result['timestamp']
                        })
                        
    def _get_error_key(self, error: Dict[str, Any]) -> str:
        """
        Generate a unique key for an error pattern.
        
        Args:
            error: Error information
            
        Returns:
            Unique key for the error pattern
        """
        # Combine error type and context to create a unique key
        error_type = error.get('type', 'unknown')
        context = error.get('context', '').split('\n')[0]  # Use first line of context
        return f"{error_type}:{context}"
        
    def get_similar_errors(self, error_type: str, context: str) -> List[Dict[str, Any]]:
        """
        Find similar errors from the test suite.
        
        Args:
            error_type: Type of error
            context: Error context
            
        Returns:
            List of similar errors and their fixes
        """
        similar_errors = []
        error_key = f"{error_type}:{context}"
        
        # Look for exact matches first
        if error_key in self.error_patterns:
            similar_errors.append(self.error_patterns[error_key])
            
        # Look for partial matches
        for key, pattern in self.error_patterns.items():
            if error_type in key or context in key:
                similar_errors.append(pattern)
                
        return similar_errors
        
    def get_fix_suggestions(self, error_type: str, context: str) -> List[str]:
        """
        Get fix suggestions for an error.
        
        Args:
            error_type: Type of error
            context: Error context
            
        Returns:
            List of fix suggestions
        """
        similar_errors = self.get_similar_errors(error_type, context)
        suggestions = []
        
        for error in similar_errors:
            # Add successful fixes
            for fix in error.get('fixes', []):
                suggestions.append(f"Fix from test {fix['test_name']} (successful)")
                
            # Add common patterns from examples
            examples = error.get('examples', [])
            if examples:
                suggestions.append(f"Based on {len(examples)} similar errors")
                
        return suggestions
        
    def record_new_error(self, error_type: str, context: str, test_name: str):
        """
        Record a new error pattern.
        
        Args:
            error_type: Type of error
            context: Error context
            test_name: Name of the test
        """
        error_key = self._get_error_key({
            'type': error_type,
            'context': context
        })
        
        if error_key not in self.error_patterns:
            self.error_patterns[error_key] = {
                'count': 0,
                'examples': [],
                'fixes': []
            }
            
        self.error_patterns[error_key]['count'] += 1
        self.error_patterns[error_key]['examples'].append({
            'test_name': test_name,
            'error': {
                'type': error_type,
                'context': context
            },
            'timestamp': datetime.now().isoformat()
        })
        
    def record_successful_fix(self, error_type: str, context: str, test_name: str):
        """
        Record a successful fix.
        
        Args:
            error_type: Type of error
            context: Error context
            test_name: Name of the test
        """
        error_key = self._get_error_key({
            'type': error_type,
            'context': context
        })
        
        if error_key in self.error_patterns:
            self.error_patterns[error_key]['fixes'].append({
                'test_name': test_name,
                'timestamp': datetime.now().isoformat()
            })
            
    def save_patterns(self):
        """Save error and fix patterns to a file."""
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        output_file = os.path.join(self.test_results_dir, f"error_patterns_{timestamp}.json")
        
        with open(output_file, 'w') as f:
            json.dump({
                'timestamp': timestamp,
                'error_patterns': self.error_patterns
            }, f, indent=2)
            
        logger.info(f"Saved error patterns to {output_file}")

def main():
    """Main function to demonstrate usage."""
    test_results_dir = "test_suite/results"
    manager = TestCaseManager(test_results_dir)
    
    # Example usage
    similar_errors = manager.get_similar_errors("syntax_error", "saw 'a constant' near 'true'")
    print(f"Found {len(similar_errors)} similar errors")
    
    suggestions = manager.get_fix_suggestions("syntax_error", "saw 'a constant' near 'true'")
    print("Fix suggestions:", suggestions)

if __name__ == "__main__":
    main() 