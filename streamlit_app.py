import os
import time
import streamlit as st
import tempfile
import difflib
import logging
from agent import CILToPromelaConverter, ErrorHandler
from error_database import ErrorDatabase
from io import StringIO
import base64
import re
from CtoCILConvertor import CToCILConverter

# Configure logging to capture output
log_stream = StringIO()
handler = logging.StreamHandler(log_stream)
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[handler]
)
logger = logging.getLogger('StreamlitApp')


# Add after your imports around line 20

def highlighted_message(message, message_type="info"):
    """Create a highlighted message with consistent styling
    
    Args:
        message (str): The message to display
        message_type (str): One of "info", "success", "warning", "error"
        
    Returns:
        str: HTML-formatted message
    """
    if message_type not in ["info", "success", "warning", "error"]:
        message_type = "info"
    
    highlight_class = f"highlight-{message_type}"
    return st.markdown(f'<span class="{highlight_class}">{message}</span>', unsafe_allow_html=True)

# Then use it like this:
# highlighted_message("Conversion successful!", "success")
# highlighted_message("Error in code", "error")
# highlighted_message("Processing file...", "info")
# highlighted_message("Potential issue detected", "warning")

# Function to load and apply custom CSS
# Update this function to provide better feedback

def load_css():
    css_file = os.path.join(os.path.dirname(__file__), "streamlit_app_styles.css")
    if os.path.exists(css_file):
        with open(css_file, "r") as f:
            css = f.read()
            # Add any missing styles for steps directly
            if "steps-container" not in css:
                css += """
                .steps-container {
                    display: flex;
                    margin: 20px 0;
                    position: relative;
                }
                
                .step {
                    flex: 1;
                    text-align: center;
                    padding: 10px 0;
                    position: relative;
                }
                
                .step-circle {
                    width: 30px;
                    height: 30px;
                    border-radius: 50%;
                    background-color: #ddd;
                    margin: 0 auto 5px;
                    display: flex;
                    align-items: center;
                    justify-content: center;
                    font-weight: bold;
                    position: relative;
                    z-index: 2;
                }
                
                .step.active .step-circle {
                    background-color: #2196F3;
                    color: white;
                }
                
                .step.completed .step-circle {
                    background-color: #4CAF50;
                    color: white;
                }
                
                .step-line {
                    position: absolute;
                    top: 15px;
                    left: 0;
                    right: 0;
                    height: 2px;
                    background-color: #ddd;
                    z-index: 1;
                }
                
                .step-label {
                    font-size: 12px;
                    color: #666;
                }
                
                .step.active .step-label {
                    color: #2196F3;
                    font-weight: bold;
                }
                
                .step.completed .step-label {
                    color: #4CAF50;
                }
                """
            st.markdown(f"<style>{css}</style>", unsafe_allow_html=True)
            logger.info("CSS loaded successfully")
        return True
    else:
        logger.warning(f"CSS file not found: {css_file}")
        # Insert critical styles directly as fallback
        st.markdown("""
        <style>
        /* Critical styles for steps */
        .steps-container {
            display: flex;
            margin: 20px 0;
            position: relative;
        }
        
        .step {
            flex: 1;
            text-align: center;
            padding: 10px 0;
            position: relative;
        }
        
        .step-circle {
            width: 30px;
            height: 30px;
            border-radius: 50%;
            background-color: #ddd;
            margin: 0 auto 5px;
            display: flex;
            align-items: center;
            justify-content: center;
            font-weight: bold;
            position: relative;
            z-index: 2;
        }
        
        .step.active .step-circle {
            background-color: #2196F3;
            color: white;
        }
        
        .step.completed .step-circle {
            background-color: #4CAF50;
            color: white;
        }
        
        .step-line {
            position: absolute;
            top: 15px;
            left: 0;
            right: 0;
            height: 2px;
            background-color: #ddd;
            z-index: 1;
        }
        
        .step-label {
            font-size: 12px;
            color: #666;
        }
        
        .step.active .step-label {
            color: #2196F3;
            font-weight: bold;
        }
        
        .step.completed .step-label {
            color: #4CAF50;
        }
        </style>
        """, unsafe_allow_html=True)
        return False

# Page config
st.set_page_config(
    page_title="CIL → Promela Converter",
    layout="wide",
    initial_sidebar_state="expanded"
)

# Apply custom styling
load_css()

# Add these to the session state initialization section
if 'c_code' not in st.session_state:
    st.session_state.c_code = ""
if 'cil_code' not in st.session_state:
    st.session_state.cil_code = ""
if 'conversion_step' not in st.session_state:
    st.session_state.conversion_step = "waiting"  # Possible values: waiting, c_to_cil, cil_to_promela, completed



# Initialize session state for storing logs
if 'status_log' not in st.session_state:
    st.session_state.status_log = []
if 'error_logs' not in st.session_state:
    st.session_state.error_logs = {
        'syntax': [],
        'verification': [],
        'type': [],
        'redeclaration': [],
        'undeclared_variable': [],
        'channel_error': [],
        'array_index_error': [],
        'deadlock': [],
        'assertion_violation': [],
        'other': []
    }
if 'original_code' not in st.session_state:
    st.session_state.original_code = ""
if 'promela_code' not in st.session_state:
    st.session_state.promela_code = ""
if 'fix_history' not in st.session_state:
    st.session_state.fix_history = []
if 'current_operation' not in st.session_state:
    st.session_state.current_operation = "Idle"
if 'error_counts' not in st.session_state:
    st.session_state.error_counts = {err_type: 0 for err_type in st.session_state.error_logs.keys()}

# Modify the on_status_update function around line 134

def on_status_update(message):
    """Callback for status updates from the converter"""
    # Add timestamp and regular message to the log
    st.session_state.status_log.append({
        'timestamp': time.strftime('%H:%M:%S'),
        'message': message
    })
    
    # Update current operation
    st.session_state.current_operation = message
    
    # Add highlighted messages based on content
    if "error" in message.lower() or "failed" in message.lower():
        st.markdown(f'<span class="highlight-error">{message}</span>', unsafe_allow_html=True)
    elif "success" in message.lower() or "complete" in message.lower():
        st.markdown(f'<span class="highlight-success">{message}</span>', unsafe_allow_html=True)
    elif "warning" in message.lower() or "issue" in message.lower():
        st.markdown(f'<span class="highlight-warning">{message}</span>', unsafe_allow_html=True)
    elif "starting" in message.lower() or "processing" in message.lower():
        st.markdown(f'<span class="highlight-info">{message}</span>', unsafe_allow_html=True)

def on_error_found(error_type, message, error_info=None):
    """Callback for error notifications from the converter"""
    # Map error types to known categories
    error_categories = {
        'syntax_error': 'syntax',
        'undeclared_variable': 'undeclared_variable',
        'redeclaration': 'redeclaration',
        'type_error': 'type',
        'channel_error': 'channel_error',
        'assertion_violation': 'assertion_violation',
        'array_index_error': 'array_index_error',
        'deadlock': 'deadlock',
        'verification': 'verification'
    }
    
    # Map the error type to a category
    category = error_categories.get(error_type, 'other')
    
    # Create the error entry
    error_entry = {
        'timestamp': time.strftime('%H:%M:%S'),
        'message': message,
        'details': error_info or {}
    }
    
    # Add to the appropriate log
    st.session_state.error_logs[category].append(error_entry)
    
    # Update error count
    if category in st.session_state.error_counts:
        st.session_state.error_counts[category] += 1

def on_fix_applied(original_snippet, fixed_snippet, error_type):
    """Track code fixes for highlighting changes"""
    st.session_state.fix_history.append({
        'timestamp': time.strftime('%H:%M:%S'),
        'error_type': error_type,
        'original': original_snippet,
        'fixed': fixed_snippet
    })

def create_download_link(code, filename="promela_code.pml"):
    """Create a download link for the Promela code"""
    b64 = base64.b64encode(code.encode()).decode()
    href = f'<a href="data:text/plain;base64,{b64}" download="{filename}" class="download-button">Download Promela Code</a>'
    return href

# Replace the existing highlight_differences function (around line 181)

def highlight_differences(original, modified):
    """Highlight differences between original and modified code for display with improved visibility"""
    original_lines = original.splitlines()
    modified_lines = modified.splitlines()
    
    # Get diff
    differ = difflib.Differ()
    diff = list(differ.compare(original_lines, modified_lines))
    
    # Prepare highlighted HTML with better colors and bold text
    highlighted_diff = []
    for line in diff:
        if line.startswith('- '):
            # Dark red for removed lines with white bold text
            highlighted_diff.append(f'<div style="background-color: #3B0000; color: white; padding: 3px; margin: 1px 0; font-weight: 700; border-left: 3px solid #FF5252;">{line[2:]}</div>')
        elif line.startswith('+ '):
            # Dark green for added lines with white bold text
            highlighted_diff.append(f'<div style="background-color: #004D40; color: white; padding: 3px; margin: 1px 0; font-weight: 700; border-left: 3px solid #00C853;">{line[2:]}</div>')
        elif line.startswith('  '):
            # Unchanged lines with slightly better contrast
            highlighted_diff.append(f'<div style="padding: 3px; margin: 1px 0;">{line[2:]}</div>')
    
    return '<div style="font-family: monospace; white-space: pre; overflow-x: auto; background-color: #0a0a0a; padding: 10px; border-radius: 5px; border: 1px solid #363558;">' + ''.join(highlighted_diff) + '</div>'

def format_error_message(error_type, error_message):
    """Format error messages to be more user-friendly"""
    
    # Basic cleanup
    message = error_message.strip()
    
    # Remove excessive technical details
    if "spin:" in message.lower():
        message = re.sub(r'spin:.*?:', '', message)
    
    # Create user-friendly messages based on error type
    friendly_messages = {
        'syntax': "Syntax Error: There's an issue with the code structure.",
        'undeclared_variable': "Undeclared Variable: Using a variable that hasn't been defined.",
        'redeclaration': "Redeclaration Error: A variable or type is declared more than once.",
        'type': "Type Error: Incompatible data types in an operation or assignment.",
        'channel_error': "Channel Error: Issue with message channels or communication.",
        'array_index_error': "Array Index Error: Array index out of bounds or invalid.",
        'deadlock': "Deadlock Detected: System reached a state where no progress is possible.",
        'assertion_violation': "Assertion Failed: A specified condition was violated.",
    }
    
    # Extract key information
    if error_type in friendly_messages:
        base_message = friendly_messages[error_type]
        
        # Extract line number if available
        line_match = re.search(r'line\s+(\d+)', message)
        line_info = f" (Line {line_match.group(1)})" if line_match else ""
        
        # Extract specific variable/identifier if available
        var_match = re.search(r"'(\w+)'", message)
        var_info = f": '{var_match.group(1)}'" if var_match else ""
        
        return f"{base_message}{line_info}{var_info}"
    
    return message


# Add this near other utility functions

def get_file_extension(file_type):
    """Get the appropriate file extension based on file type"""
    if file_type == "c":
        return ".c"
    elif file_type == "cil":
        return ".cil"
    elif file_type == "promela":
        return ".pml"
    else:
        return ".txt"

def create_download_links(c_code=None, cil_code=None, promela_code=None):
    """Create download links for all generated code files"""
    links = []
    
    if c_code:
        b64_c = base64.b64encode(c_code.encode()).decode()
        c_href = f'<a href="data:text/plain;base64,{b64_c}" download="code.c" class="download-button">Download C Code</a>'
        links.append(c_href)
        
    if cil_code:
        b64_cil = base64.b64encode(cil_code.encode()).decode()
        cil_href = f'<a href="data:text/plain;base64,{b64_cil}" download="code.cil" class="download-button">Download CIL Code</a>'
        links.append(cil_href)
        
    if promela_code:
        b64_pml = base64.b64encode(promela_code.encode()).decode()
        pml_href = f'<a href="data:text/plain;base64,{b64_pml}" download="code.pml" class="download-button">Download Promela Code</a>'
        links.append(pml_href)
        
    return '<div class="download-container">' + ''.join(links) + '</div>'


# Add this function to handle the Promela conversion step
def begin_promela_conversion(api_key=None):
    """Start the CIL to Promela conversion process"""
    with st.spinner("Converting CIL to Promela..."):
        # Clear previous logs and results
        st.session_state.status_log = []
        st.session_state.error_logs = {key: [] for key in st.session_state.error_logs}
        st.session_state.fix_history = []
        st.session_state.error_counts = {err_type: 0 for err_type in st.session_state.error_counts}
        
        try:
            # Create converter with callbacks
            converter = create_converter(api_key)
            
            # Perform conversion
            st.markdown('<span class="highlight-info">Starting CIL to Promela conversion process</span>', unsafe_allow_html=True)
            on_status_update("Starting CIL to Promela conversion process")
            
            # Save code for conversion
            cil_code = st.session_state.cil_code
            
            # Convert CIL to Promela
            promela_code = converter.convert(cil_code)
            
            # Verify the Promela code
            success, message = converter.verify_promela_code(promela_code)
            
            # If verification failed, try to fix
            if not success:
                st.markdown('<span class="highlight-warning">Initial verification failed, attempting to fix issues</span>', unsafe_allow_html=True)
                on_status_update("Initial verification failed, attempting to fix issues")
                max_iterations = 10
                iteration = 1
                current_code = promela_code
                current_error = message
                
                while iteration <= max_iterations and not success:
                    on_status_update(f"Fix attempt {iteration}/{max_iterations}")
                    
                    # Fix the code
                    fixed_code = converter.fix_promela_code(current_code, current_error)
                    
                    # Verify the fixed code
                    success, new_error = converter.verify_promela_code(fixed_code)
                    
                    # Update for next iteration
                    current_code = fixed_code
                    current_error = new_error
                    iteration += 1
                    
                    # Break if successful
                    if success:
                        on_status_update("Successfully fixed all issues!")
                        break
                
                promela_code = current_code
            
            # Update the session state
            st.session_state.promela_code = promela_code
            st.session_state.conversion_step = "completed"
            
            # Show final status
            if success:
                on_status_update("Conversion complete - No errors detected")
                st.success("Conversion successful!")
            else:
                on_status_update("Conversion complete - Some errors remain")
                st.warning("Conversion completed with some unresolved issues")
            
        except Exception as e:
            st.error(f"Error during conversion: {str(e)}")
            on_status_update(f"Error: {str(e)}")
            logger.exception("Conversion error")

def create_converter(api_key=None):
    """Create a CIL to Promela converter instance with callbacks"""
    # Use the API key if provided, otherwise use default
    api_key = api_key or "AIzaSyC88vGjUkqyu4Ux_9zVCdk7Z88cpQi7uEM"
    
    # Create the converter
    converter = CILToPromelaConverter(
        api_key=api_key,
        model="gemini-2.0-flash",
        spin_path="spin",
        verification_target="general",
        max_iterations=10
    )
    
    # Modify the converter to use our callbacks
    original_fix_promela_code = converter.fix_promela_code
    
    def fix_promela_code_with_callbacks(promela_code, error_message):
        """Wrapper for fix_promela_code that adds callbacks"""
        # Parse the error to categorize it properly
        error_info = converter.parse_spin_error(error_message)
        
        # Update the UI with the error
        for error_type in error_info.get('error_types', ['other']):
            on_error_found(
                error_type, 
                format_error_message(error_type, error_message),
                {"line_numbers": error_info.get('line_numbers', []), "details": error_message}
            )
        
        # Update status
        error_type_msg = " and ".join(error_info.get('error_types', ['unknown']))
        on_status_update(f"Fixing {error_type_msg} error{'s' if len(error_info.get('error_types', [])) > 1 else ''}")
        
        # Call original method
        fixed_code = original_fix_promela_code(promela_code, error_message)
        
        # Track the fix
        if error_info.get('error_types'):
            on_fix_applied(promela_code, fixed_code, error_info['error_types'][0])
        
        return fixed_code
    
    # Replace the method with our wrapped version
    converter.fix_promela_code = fix_promela_code_with_callbacks
    
    # Also capture verification attempts
    original_verify_promela_code = converter.verify_promela_code
    
    def verify_promela_code_with_callbacks(promela_code):
        """Wrapper for verify_promela_code that adds callbacks"""
        on_status_update("Verifying Promela code with SPIN")
        return original_verify_promela_code(promela_code)
    
    converter.verify_promela_code = verify_promela_code_with_callbacks
    
    # Capture conversion process
    original_convert = converter.convert
    
    def convert_with_callbacks(cil_code, context=None, fix_prompt=None):
        """Wrapper for convert that adds callbacks"""
        on_status_update("Converting CIL to Promela")
        result = original_convert(cil_code, context, fix_prompt)
        on_status_update("Initial conversion complete")
        return result
    
    converter.convert = convert_with_callbacks
    
    return converter

def main():
    """Main function for the Streamlit app"""
    
    # Header with logo and title
    st.markdown("""
    <div class="header">
        <h1>CIL to Promela Converter</h1>
        <h3>Formal Verification Tool</h3>
    </div>
    """, unsafe_allow_html=True)
    
    # REPLACE THE CURRENT STEPS CODE HERE (lines ~500-548)
    # WITH THE NEW STEPS HTML GENERATION CODE:
    
    # Show process steps indicator with cleaner HTML generation
    st.subheader("Conversion Progress")

    # Define the steps
    steps = [
        {"id": "c_code", "label": "C Code"},
        {"id": "c_to_cil", "label": "C → CIL"},
        {"id": "cil_code", "label": "CIL Code"},
        {"id": "cil_to_promela", "label": "CIL → Promela"},
        {"id": "promela_code", "label": "Promela Code"}
    ]

    # Determine current step
    current_step = "waiting"
    if st.session_state.conversion_step == "waiting":
        if st.session_state.c_code:
            current_step = "c_code"
        elif st.session_state.cil_code:
            current_step = "cil_code"
    elif st.session_state.conversion_step == "c_to_cil":
        current_step = "c_to_cil"
    elif st.session_state.conversion_step == "cil_to_promela":
        current_step = "cil_to_promela"
    elif st.session_state.conversion_step == "completed":
        current_step = "promela_code"

    # Generate HTML for steps - simpler, more robust approach
    steps_html = ['<div class="steps-container"><div class="step-line"></div>']

    for i, step in enumerate(steps):
        # Determine step status
        if step["id"] == current_step:
            status = "active"
        elif (current_step == "c_to_cil" and i < 1) or \
             (current_step == "cil_code" and i < 2) or \
             (current_step == "cil_to_promela" and i < 3) or \
             (current_step == "promela_code" and i < 4):
            status = "completed"
        else:
            status = ""
            
        # Add HTML for this step (as a single string with no line breaks)
        steps_html.append(f'<div class="step {status}"><div class="step-circle">{i+1}</div><div class="step-label">{step["label"]}</div></div>')

    steps_html.append('</div>')

    # Join all HTML parts and render
    final_html = ''.join(steps_html)

    # Add a debugging option to see the raw HTML (can be removed later)
    debug_mode = False  # Set to True to see the raw HTML
    if debug_mode:
        st.code(final_html)

    # Render the HTML
    st.markdown(final_html, unsafe_allow_html=True)
    


    # Sidebar for configuration
    with st.sidebar:
        st.subheader("Configuration")
        
        # API key input (optional)
        api_key = st.text_input("Gemini API Key (Optional)", 
                               value="", 
                               type="password",
                               help="Enter your Gemini API key if you have one")
        
        # File upload or text input option
        input_method = st.radio("Input Method", ["Upload File", "Enter Text"])
        
        # Show statistics
        # st.markdown("### Error Statistics")
        # for err_type, count in st.session_state.error_counts.items():
        #     if count > 0:
        #         st.markdown(f"- {err_type.title()}: {count}")

        # Add download section if code is available
        if st.session_state.c_code or st.session_state.cil_code or st.session_state.promela_code:
            st.markdown("### Download Options")
            st.markdown(
                create_download_links(
                    st.session_state.c_code, 
                    st.session_state.cil_code, 
                    st.session_state.promela_code
                ), 
                unsafe_allow_html=True
            )
    
    # Main content area with tabs
    tab1, tab2, tab3, tab4, tab5 = st.tabs(["Convert Code", "Errors & Fixes", "Error Summary", "Code Comparison", "Log Viewer"])
    
    # Modify the main tab1 content with the updated workflow
    with tab1:
        col1, col2 = st.columns(2)
        
        with col1:
            st.markdown("### Input Code")
            
            # Add a radio button to choose input type
            input_type = st.radio("Input Type", ["C Code", "CIL Code"], help="Choose whether to input C code or CIL code directly")
            
            if input_method == "Upload File":
                # Update file uploader to accept both C and CIL files
                uploaded_file = st.file_uploader("Upload file", type=["c", "i", "cil"])
                if uploaded_file is not None:
                    input_code = uploaded_file.getvalue().decode("utf-8")
                    
                    # Determine if the uploaded file is C or CIL based on extension
                    if uploaded_file.name.endswith('.c') and input_type == "C Code":
                        st.session_state.c_code = input_code
                        st.session_state.cil_code = ""  # Clear CIL code
                        st.session_state.original_code = ""  # Clear original code for the next step
                        st.code(input_code, language="c")
                    else:
                        st.session_state.cil_code = input_code
                        st.session_state.original_code = input_code  # Set as original code for conversion
                        st.code(input_code, language="c")
            else:
                # Text area input
                if input_type == "C Code":
                    input_code = st.text_area("Enter C code", height=400, value=st.session_state.c_code)
                    st.session_state.c_code = input_code
                    st.session_state.cil_code = ""  # Clear CIL code
                else:
                    input_code = st.text_area("Enter CIL code", height=400, value=st.session_state.cil_code)
                    st.session_state.cil_code = input_code
                    st.session_state.original_code = input_code  # Set as original code for conversion
        
        with col2:
            # Modified output section to show intermediate CIL code if needed
            if input_type == "C Code" and st.session_state.c_code:
                st.markdown("### CIL Code Intermediate Representation")
                
                # Show CIL code if available or a placeholder
                if st.session_state.cil_code:
                    st.code(st.session_state.cil_code, language="c")
                    
                    # Option to edit the generated CIL before proceeding
                    edit_cil = st.checkbox("Edit generated CIL code", value=False)
                    if edit_cil:
                        edited_cil = st.text_area("Edit CIL code", value=st.session_state.cil_code, height=300)
                        if st.button("Update CIL"):
                            st.session_state.cil_code = edited_cil
                            st.session_state.original_code = edited_cil  # Update original code for conversion
                            st.success("CIL code updated!")
                else:
                    st.info("CIL code will appear here after conversion from C")
            else:
                # Show Promela output section
                st.markdown("### Promela Code Output")
                
                # Display current status
                st.info(f"**Current Status**: {st.session_state.current_operation}")
                
                # Display Promela code if available
                if st.session_state.promela_code:
                    st.code(st.session_state.promela_code, language="promela")
                    
                    # Download button
                    st.markdown(create_download_link(st.session_state.promela_code), unsafe_allow_html=True)
                else:
                    st.info("Promela code will appear here after conversion")
        
        # Buttons for conversion - update to have different flows based on input type
        col1, col2, col3 = st.columns([1, 2, 1])
        
        with col2:
            if input_type == "C Code":
                # Show C to CIL conversion button first
# Add to the C to CIL conversion around line 741-755

                if st.button("Convert C to CIL", type="primary", use_container_width=True):
                    if not st.session_state.c_code:
                        st.markdown('<span class="highlight-error">Please provide C code to convert</span>', unsafe_allow_html=True)
                        st.error("Please provide C code to convert")
                    else:
                        with st.spinner("Converting C to CIL..."):
                            try:
                                # Run C to CIL conversion
                                st.markdown('<span class="highlight-info">Converting C code to CIL...</span>', unsafe_allow_html=True)
                                on_status_update("Converting C code to CIL")
                                converter = CToCILConverter()
                                cil_code = converter.convert(st.session_state.c_code)
                                
                                # Update session state
                                st.session_state.cil_code = cil_code
                                st.session_state.original_code = cil_code  # Set for next step
                                st.session_state.conversion_step = "c_to_cil"
                                
                                st.markdown('<span class="highlight-success">C to CIL conversion complete!</span>', unsafe_allow_html=True)
                                on_status_update("C to CIL conversion complete")
                                st.success("C code converted to CIL successfully!")
                            except Exception as e:
                                st.markdown(f'<span class="highlight-error">Error: {str(e)}</span>', unsafe_allow_html=True)
                                st.error(f"Error converting C to CIL: {str(e)}")
                                on_status_update(f"Error: {str(e)}")
                                logger.exception("C to CIL conversion error")
                
                # Only show next step button if CIL is available
                if st.session_state.cil_code:
                    # In the C Code flow:
                    if st.button("Convert CIL to Promela", use_container_width=True):
                        st.session_state.conversion_step = "cil_to_promela"
                        # Pass the api_key when calling the function
                        begin_promela_conversion(api_key)
            else:
                # Direct CIL to Promela conversion
                if st.button("Convert to Promela", type="primary", use_container_width=True):
                    if not st.session_state.cil_code:
                        st.error("Please provide CIL code to convert")
                    else:
                        begin_promela_conversion(api_key)

    
    # Tab 2: Errors & Fixes
# Alternative approach using buttons and session state

    # Tab 2: Errors & Fixes
    with tab2:
        # Initialize session state for detail visibility
        if 'visible_details' not in st.session_state:
            st.session_state.visible_details = {}
        
        # Create expandable sections for each error type
        error_types = {
            'syntax': "Syntax Errors",
            'redeclaration': "Redeclaration Errors",
            'undeclared_variable': "Undeclared Variable Errors",
            'type': "Type Errors",
            'channel_error': "Channel Errors",
            'array_index_error': "Array Index Errors",
            'deadlock': "Deadlock Issues",
            'assertion_violation': "Assertion Violations",
            'verification': "Verification Errors",
            'other': "Other Errors"
        }
        
        def toggle_detail_visibility(error_id):
            """Toggle visibility of error details"""
            if error_id in st.session_state.visible_details:
                st.session_state.visible_details[error_id] = not st.session_state.visible_details[error_id]
            else:
                st.session_state.visible_details[error_id] = True
        
        for error_key, error_title in error_types.items():
            errors = st.session_state.error_logs.get(error_key, [])
            
            if errors:
                with st.expander(f"{error_title} ({len(errors)})", expanded=True):
                    for idx, error in enumerate(errors):
                        error_id = f"{error_key}_{idx}"
                        st.markdown(f"**{error['timestamp']}**: {error['message']}")
                        
                        # Show details if available
                        if 'details' in error and isinstance(error['details'], dict):
                            if 'line_numbers' in error['details'] and error['details']['line_numbers']:
                                st.markdown(f"*Line numbers: {', '.join(map(str, error['details']['line_numbers']))}*")
                            
                            # Show detailed error message WITHOUT using nested expander
                            if 'details' in error['details']:
                                # Create a button to show/hide details
                                button_text = "Hide Details" if st.session_state.visible_details.get(error_id, False) else "Show Details"
                                if st.button(button_text, key=f"btn_{error_id}"):
                                    toggle_detail_visibility(error_id)
                                
                                # Show details if visible
                                if st.session_state.visible_details.get(error_id, False):
                                    st.code(error['details']['details'])
                        
                        st.divider()

# Add after the Tab 2 section (around line 447, after the existing tab2 code)

    # New Tab 3: Error Summary
    with tab3:
        st.markdown("### Error Classification Summary")
        
        # Check if we have any errors
        total_errors = sum(st.session_state.error_counts.values())
        
        if total_errors > 0:
            # Group errors into main categories
            error_categories = {
                "Syntax Errors": ["syntax", "redeclaration", "undeclared_variable"],
                "Type Errors": ["type", "array_index_error"],
                "Verification Errors": ["deadlock", "assertion_violation", "verification"],
                "Communication Errors": ["channel_error"],
                "Other Errors": ["other"]
            }
            
            # Create columns for charts and details
            chart_col, details_col = st.columns([3, 2])
            
            with chart_col:
                # Prepare data for pie chart
                categories = []
                counts = []
                colors = {
                    "Syntax Errors": "#FF9800",      # Orange
                    "Type Errors": "#2196F3",        # Blue
                    "Verification Errors": "#9C27B0", # Purple
                    "Communication Errors": "#4CAF50", # Green
                    "Other Errors": "#607D8B"        # Gray
                }
                category_colors = []
                
                for category, error_types in error_categories.items():
                    category_count = sum(st.session_state.error_counts.get(err_type, 0) for err_type in error_types)
                    if category_count > 0:
                        categories.append(category)
                        counts.append(category_count)
                        category_colors.append(colors.get(category, "#607D8B"))
                
                # Create chart using Streamlit
                st.subheader("Error Distribution")
                
                # If plotly is available, create an interactive pie chart
                try:
                    import plotly.graph_objects as go
                    fig = go.Figure(data=[go.Pie(
                        labels=categories,
                        values=counts,
                        marker=dict(colors=category_colors),
                        textinfo='label+percent',
                        hole=.3
                    )])
                    fig.update_layout(margin=dict(t=0, b=0, l=0, r=0))
                    st.plotly_chart(fig, use_container_width=True)
                except ImportError:
                    # Fallback to text representation
                    for i, (category, count) in enumerate(zip(categories, counts)):
                        st.markdown(
                            f"<div style='background-color: {category_colors[i]}; "
                            f"color: white; padding: 8px; border-radius: 5px; margin-bottom: 5px;'>"
                            f"{category}: {count} ({count/total_errors:.1%})</div>",
                            unsafe_allow_html=True
                        )
            
            # Replace with this code (using toggle buttons instead of nested expanders):
            with details_col:
                st.subheader("Error Breakdown")
                
                # Initialize state for examples if not exists
                if 'visible_examples' not in st.session_state:
                    st.session_state.visible_examples = {}
                
                def toggle_example_visibility(example_id):
                    """Toggle visibility of error examples"""
                    if example_id in st.session_state.visible_examples:
                        st.session_state.visible_examples[example_id] = not st.session_state.visible_examples[example_id]
                    else:
                        st.session_state.visible_examples[example_id] = True
                
                # Show detailed breakdown by specific error types
                for category, error_types in error_categories.items():
                    category_errors = [(err_type, st.session_state.error_counts.get(err_type, 0)) 
                                    for err_type in error_types if st.session_state.error_counts.get(err_type, 0) > 0]
                    
                    if category_errors:
                        with st.expander(f"{category} ({sum(count for _, count in category_errors)})", expanded=True):
                            for err_type, count in category_errors:
                                friendly_name = err_type.replace('_', ' ').title()
                                example_id = f"example_{category}_{err_type}"
                                
                                # Main error count display
                                st.markdown(f"- **{friendly_name}**: {count}")
                                
                                # Show representative example if available
                                errors = st.session_state.error_logs.get(err_type, [])
                                if errors:
                                    # Button to show/hide example
                                    button_text = "Hide Example" if st.session_state.visible_examples.get(example_id, False) else "Show Example"
                                    if st.button(button_text, key=f"btn_ex_{example_id}"):
                                        toggle_example_visibility(example_id)
                                    
# Modify the error breakdown section around line 855

                                    # Show example if visible
                                    if st.session_state.visible_examples.get(example_id, False):
                                        highlight_class = "highlight-error"
                                        if "syntax" in err_type or "redeclaration" in err_type or "undeclared" in err_type:
                                            highlight_class = "highlight-error"
                                        elif "verification" in err_type or "deadlock" in err_type or "assertion" in err_type:
                                            highlight_class = "highlight-warning"
                                        elif "type" in err_type:
                                            highlight_class = "highlight-info"
                                        
                                        st.markdown(f'<div class="{highlight_class}" style="padding: 10px; margin: 10px 0;">', unsafe_allow_html=True)
                                        st.markdown(f"*{errors[0].get('message', 'No details available')}*")
                                        if 'details' in errors[0] and 'line_numbers' in errors[0]['details']:
                                            st.markdown(f"Line numbers: {', '.join(map(str, errors[0]['details']['line_numbers']))}")
                                        st.markdown("</div>", unsafe_allow_html=True)


    # Change to:
    # Replace the Code Comparison tab content

    # Tab 4: Code Comparison
    with tab4:
        st.markdown("### Code Transformation Steps")
        
        if st.session_state.fix_history:
            # Show dropdown to select which fix to view
            fix_options = [f"{fix['timestamp']} - {fix['error_type']}" 
                        for fix in st.session_state.fix_history]
            selected_fix = st.selectbox("Select fix to view", fix_options)
            
            # Get the selected fix
            fix_idx = fix_options.index(selected_fix)
            fix = st.session_state.fix_history[fix_idx]
            
            # Display the original and fixed code side by side
            col1, col2 = st.columns(2)
            
            with col1:
                st.markdown("#### Before Fix")
                st.code(fix['original'], language="promela")
            
            with col2:
                st.markdown("#### After Fix")
                st.code(fix['fixed'], language="promela")
            
            # Show highlighted differences
            st.markdown("#### Changes Highlighted")
            st.markdown(highlight_differences(fix['original'], fix['fixed']), unsafe_allow_html=True)
            
        else:
            # Show the complete transformation pipeline
            if st.session_state.c_code and st.session_state.cil_code and st.session_state.promela_code:
                # Tabs for different comparison views
                comp_tab1, comp_tab2, comp_tab3 = st.tabs(["C → CIL", "CIL → Promela", "Full Pipeline"])
                
                with comp_tab1:
                    col1, col2 = st.columns(2)
                    with col1:
                        st.markdown("#### Original C Code")
                        st.code(st.session_state.c_code, language="c")
                    with col2:
                        st.markdown("#### Generated CIL Code")
                        st.code(st.session_state.cil_code, language="c")
                    
                    # Show differences
                    st.markdown("#### C to CIL Transformation")
                    st.markdown(highlight_differences(st.session_state.c_code, st.session_state.cil_code), unsafe_allow_html=True)
                
                with comp_tab2:
                    col1, col2 = st.columns(2)
                    with col1:
                        st.markdown("#### CIL Code")
                        st.code(st.session_state.cil_code, language="c")
                    with col2:
                        st.markdown("#### Generated Promela Code")
                        st.code(st.session_state.promela_code, language="promela")
                
                with comp_tab3:
                    st.markdown("#### Complete Transformation Pipeline")
                    st.markdown("##### Step 1: C Code")
                    st.code(st.session_state.c_code, language="c")
                    
                    st.markdown("##### Step 2: CIL Code")
                    st.code(st.session_state.cil_code, language="c")
                    
                    st.markdown("##### Step 3: Promela Code")
                    st.code(st.session_state.promela_code, language="promela")
                    
            elif st.session_state.cil_code and st.session_state.promela_code:
                # Just show CIL to Promela
                col1, col2 = st.columns(2)
                with col1:
                    st.markdown("#### CIL Code")
                    st.code(st.session_state.cil_code, language="c")
                with col2:
                    st.markdown("#### Generated Promela Code")
                    st.code(st.session_state.promela_code, language="promela")
            
            elif st.session_state.c_code and st.session_state.cil_code:
                # Just show C to CIL
                col1, col2 = st.columns(2)
                with col1:
                    st.markdown("#### C Code")
                    st.code(st.session_state.c_code, language="c")
                with col2:
                    st.markdown("#### Generated CIL Code")
                    st.code(st.session_state.cil_code, language="c")
                    
                # Show differences
                st.markdown("#### C to CIL Transformation")
                st.markdown(highlight_differences(st.session_state.c_code, st.session_state.cil_code), unsafe_allow_html=True)
            
            else:
                st.info("Convert some code first to see the transformations.")
    
    # Change to:
    with tab5:
        st.markdown("### Process Log")
    
        
# Modify the log viewer section around line 980

        # Display status log entries
        if st.session_state.status_log:
            for log_entry in st.session_state.status_log:
                message = log_entry['message']
                if "error" in message.lower() or "failed" in message.lower():
                    st.markdown(f'<span class="highlight-error">{log_entry["timestamp"]}: {message}</span>', unsafe_allow_html=True)
                elif "success" in message.lower() or "complete" in message.lower():
                    st.markdown(f'<span class="highlight-success">{log_entry["timestamp"]}: {message}</span>', unsafe_allow_html=True)
                elif "warning" in message.lower() or "issue" in message.lower():
                    st.markdown(f'<span class="highlight-warning">{log_entry["timestamp"]}: {message}</span>', unsafe_allow_html=True)
                else:
                    st.markdown(f'<span class="highlight-info">{log_entry["timestamp"]}: {message}</span>', unsafe_allow_html=True)
                st.divider()
        else:
            st.info("No logs to display yet. Convert some code to see the process log.")

if __name__ == "__main__":
    main()