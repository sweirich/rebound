#!/usr/bin/env bash

usage() {
  echo "Usage:"
  echo "  $0 [options]"
  echo ""
  echo "A script to run pi-forall benchmarks using different representations"
  echo "for Rebound's 'Env' type. Outputs will be located under './.results'."
  echo "The environment variable 'REBOUND' should contain a path to a local"
  echo "clone of Rebound's repository."
  echo ""
  echo "Options:"
  echo "  -h, --help      Display this help message."
  exit 1
}

# Parse command-line option.
while [[ $# -gt 0 ]]; do
  key="$1"
  case "$key" in
    -h|--help)
      usage
      ;;
    *)
      usage
      exit 1
      ;;
  esac
done

# Define the file to modify in Rebound.
repository="${REBOUND:-../Rebound}"
file="${repository}/src/Rebound/Env.hs"
dest_dir="./.results/"

# Check if the file exists.
if [ ! -f "$file" ]; then
  echo "Error: File '$file' not found."
  exit 1
fi

mkdir -p "$dest_dir"
if [ $? -ne 0 ]; then
  echo "Could not create $dest_dir directory"
  exit 1
fi

# Use perl to replace the import methods for Rebound.
perl -0777 -i.original -pe 's{- github:.*/Rebound\n.*}{- $ENV{repository}}' stack.yaml
restore_stack_yaml () {
  mv stack.yaml.original stack.yaml
}

# Define the list of variables.
valid_variables=("Internal" "InternalA" "Functional" "InternalB" "InternalLazy")

for variable in "${valid_variables[@]}"; do
  new_string="import Rebound.Env.$variable"
  sed -i -e "s/import Rebound.Env.Internal/$new_string/" "$file"

  if [ $? -ne 0 ]; then
    echo "Error: Failed to change line in '$file' for variable '$variable'."
    restore_stack_yaml
    exit 1
  else
    echo "Successfully changed line in '$file' to '$new_string'."
  fi

  # Run benchmark
  stack bench --benchmark-arguments="--output=$dest_dir/$variable.html --match=glob **/Rebound"
  if [ $? -ne 0 ]; then
    echo "Error: benchmark failed for variable '$variable'."
    restore_stack_yaml
    sed -i -e "s/import Rebound.Env.$variable/import Rebound.Env.Internal/" "$file"
    exit 1
  else
    echo "Benchmark executed successfully for variable '$variable'."
  fi

  # Revert file to its original state
  sed -i -e "s/import Rebound.Env.$variable/import Rebound.Env.Internal/" "$file"
  if [ $? -ne 0 ]; then
    echo "Error: Failed to revert the Haskell file '$file' after processing variable '$variable'."
    exit 1
  else
    echo "Successfully reverted '$file' to its original state after processing variable '$variable'."
  fi
done

restore_stack_yaml

exit 0
