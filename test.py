import pandas as pd

# Load the dataset
dataset_path = './combined_dataset.parquet'
dataset = pd.read_parquet(dataset_path)

# Display the first few rows to check the structure
print("\nDataset Sample:\n", dataset.head())

# Check available columns
print("\nColumns in Dataset:", dataset.columns)

# Ensure necessary columns exist
if 'Theorem' not in dataset.columns or 'Output' not in dataset.columns:
    raise ValueError("Dataset does not contain required columns: 'Theorem' and 'Output'.")

# Extract all theorems and proofs
theorems_and_proofs = dataset[['Theorem', 'Output']]

# Display all the theorems and proofs
import ace_tools as tools
tools.display_dataframe_to_user(name="All Theorems and Proofs", dataframe=theorems_and_proofs)

# Save to CSV file (optional)
output_file = "all_theorems_and_proofs.csv"
theorems_and_proofs.to_csv(output_file, index=False)

print(f"\n✅ Theorems and proofs saved to {output_file}")
