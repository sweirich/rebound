#!/usr/bin/env python3
import importlib.util
import sys
import os

# Check if pandas is installed
if importlib.util.find_spec("pandas") is None:
    print("Error: pandas is not installed.")
    print("Please install pandas using pip.  It is recommended to use a virtual environment.  For virtualenv, run:")
    print("  python3 -m venv .venv")
    print("  source .venv/bin/activate  (Linux/macOS)")
    print("  .venv\\Scripts\\activate (Windows)")
    print("  pip install pandas")
    sys.exit(1)

import pandas as pd

def merge_csv_to_xlsx(all_eval_dir="results/all_eval", output_file="results/all_results.xlsx"):
    """
    Combines CSV files from subdirectories into an XLSX file, where each CSV
    becomes a separate sheet.

    Args:
        all_eval_dir (str): The root directory containing subdirectories with CSV files.
        output_file (str): The name of the output XLSX file.
    """
    writer = pd.ExcelWriter(output_file, engine="xlsxwriter")

    for variable in os.listdir(all_eval_dir):
        if not variable.startswith(".") and os.path.isdir(os.path.join(all_eval_dir, variable)):
            var_dir = os.path.join(all_eval_dir, variable)
            for filename in os.listdir(var_dir):
                if filename.endswith(".csv"):
                    filepath = os.path.join(var_dir, filename)
                    try:
                        df = pd.read_csv(filepath)
                        sheet_name = f"{variable}_{os.path.splitext(filename)[0]}"
                        # Sanitize sheet names for Excel compatibility
                        sheet_name = "".join(c if c.isalnum() else "_" for c in sheet_name)
                        sheet_name = sheet_name[:31]  # Excel sheet name limit
                        df.to_excel(writer, sheet_name=sheet_name, index=False)
                        print(f"Successfully added sheet {sheet_name} to XLSX")
                    except Exception as e:
                        print(f"Error reading CSV {filepath}: {e}")

    writer.close()
    print(f"Successfully created {output_file}")

if __name__ == "__main__":
    merge_csv_to_xlsx()
