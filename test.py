import google.generativeai as genai

# Set up Gemini API Key
GOOGLE_API_KEY = "AIzaSyAHIr9qaRwqz9iXk43ChHJ4zFIrlNrofQA" # Replace with your actual key
genai.configure(api_key=GOOGLE_API_KEY)

# List available models
models = genai.list_models()

# Print model names
print("Available Gemini models:")
for model in models:
    print(model.name)
