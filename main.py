import google.generativeai as genai
from datasets import load_dataset
import os
from dotenv import load_dotenv
import subprocess
from datetime import datetime


load_dotenv()  # Load environment variables from .env file
GOOGLE_API_KEY = os.getenv("GOOGLE_API_KEY")

if not GOOGLE_API_KEY:
    raise ValueError("Google API key not found. Set it in the .env file.")

genai.configure(api_key=GOOGLE_API_KEY)


# Load the combined dataset
dataset2 = load_dataset('parquet', data_files='./combined_dataset.parquet')

# User input for theorem search
input_theorem = input("Enter a theorem to search: ").strip()

# Search for exact or partial match
matching_rows = [entry for entry in dataset2['train'] if input_theorem.lower() in entry['Theorem'].lower()]

if not matching_rows:
    print("Theorem not found in the dataset.")
    exit()

# Get proof details
proof_details = matching_rows[0]['Output']
print("\nProof and details:", proof_details)

# Set up Gemini API
GOOGLE_API_KEY = GOOGLE_API_KEY  # Replace with your API key
genai.configure(api_key=GOOGLE_API_KEY)

# Gemini prompt
prompt = f"""
I have the following theorem and proof in Coq:

Theorem:
{input_theorem}

Proof details:
{proof_details}

Generate the full Coq 8.20 code required to prove this theorem.
Ensure that:
1. **Use `From Cdcl Require Import Lib Syntax Lit.` correctly.**
3. The Coq script should be self-contained and verifiable in Coq without requiring additional manual fixes.
4. The output should contain **only valid Coq code**, with no explanations.
"""



# Generate response
model = genai.GenerativeModel("gemini-1.5-pro-002")  # Use this instead
response = model.generate_content(prompt)

# Display Coq Code
print("\nGenerated Coq Code:\n")
print(response.text)


# Save the generated Coq code to a file

import re

# Extract only valid Coq code
coq_code_lines = response.text.split("\n")

# Remove non-Coq parts
inside_coq_block = False
cleaned_code = []

for line in coq_code_lines:
    if line.strip().startswith("```coq"):
        inside_coq_block = True  # Start extracting Coq code
        continue
    if line.strip().startswith("```"):
        inside_coq_block = False  # Stop extracting Coq code
        continue
    if inside_coq_block:
        cleaned_code.append(line)

# Join cleaned Coq code
coq_code = "\n".join(cleaned_code)


print("\n✅ Cleaned Coq code saved to generated_proof.v")


# Create the 'verification' folder if it doesn't exist
os.makedirs("verification", exist_ok=True)

# Generate a unique filename using a timestamp
timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
file_name = f"generated_proof_{timestamp}.v"
file_path = os.path.join("verification", file_name)

# Save the cleaned Coq code to the file in the 'verification' folder
with open(file_path, "w") as f:
    f.write(coq_code)

print(f"\n✅ Cleaned Coq code saved to {file_path}")