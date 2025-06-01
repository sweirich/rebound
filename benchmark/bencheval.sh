#!/bin/bash

branch="wip/phantom-snat-fin-vec"

machine=`hostname`

echo "---------------- TESTING --------------------"
stack test
echo "---------------- BENCHMARKING ---------------"
make normalize 

source_dir="results/`hostname`/rebound_strict_envV"
dest_dir="results/ablate/rebound_strict_envV/$branch/Vector"


mkdir -p "$dest_dir"
# Move the files 

mv $source_dir/* $dest_dir/


