from datasets import Dataset, load_dataset

# Load datasets
dataset = load_dataset('parquet', data_files='.\props-proofs.parquet')
dataset1 = load_dataset('parquet', data_files='.\facts.parquet')

print("Dataset columns:", dataset['train'].column_names)
print("Dataset1 columns:", dataset1['train'].column_names)

# Set max count
max_count = min(100000, len(dataset['train']['proposition']), len(dataset1['train']['fact']))

# Extract relevant columns
theorems = dataset['train']["proposition"][:max_count]
libraries_needed = dataset['train']["imports"][:max_count]
definitions = dataset1['train']["fact"][:max_count]
proofs = dataset['train']["proof"][:max_count]

# Create dataset
combined_data = Dataset.from_dict({
    "Theorem": theorems,
    "Output": [f"Libraries - {lib}, Definitions - {defn}, Endpoint - {proof}" for lib, defn, proof in zip(libraries_needed, definitions, proofs)]
})

# Save dataset properly
combined_data.to_parquet(".\combined_dataset.parquet")

print("Dataset successfully saved with", len(combined_data), "rows!")


# Test
dataset2 = load_dataset('parquet', data_files='.\combined_dataset.parquet')
print(dataset2["train"][0])
