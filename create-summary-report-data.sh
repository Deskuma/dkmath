#!/bin/bash

LOG_DIR="logs/summary_report"  # Directory to store summary report data
mkdir -p "$LOG_DIR"  # Create logs directory if it doesn't exist

# clear old logs
rm -f "$LOG_DIR"/__*.txt

# Create summary report data by extracting relevant information from the codebase

# file tree
## project full tree (exclude .git and logs, others)
## .lake .git .github .vscode .pytest_cache, __pycache__, venv, *.pyc, *.pyo
find . | grep -vE '(\.git|logs|^./lean/dk_math/.lake|\.github|\.vscode|\.pytest_cache|__pycache__|venv|.*\.pyc$|.*\.pyo$|__fig\#|/__.*)' | sort | tee "$LOG_DIR/__project_find_files.txt"
tree lean/dk_math/DkMath | tee "$LOG_DIR/__file_tree_in_dkmath.txt"

# Extract theorems, lemmas, defs, sorries, and imports from the codebase
rg -n "^(theorem|lemma|def)\s+" lean/dk_math/DkMath -S -A5 -B2 | tee "$LOG_DIR/___theorems.txt"
rg -n "^(theorem|lemma|def)\s+" lean/dk_math/DkMath -S -A5 -B2 --heading | tee "$LOG_DIR/__theorems-heading.txt"
rg -n "^(theorem|lemma|def)\s+" lean/dk_math/DkMath -S -A5 -B5 --heading | rg -n "^[^:]+:" | tee "$LOG_DIR/___theorems-with-filename.txt"
rg -n --type-add 'lean:*.lean' --type lean "\bsorry\b" -S -A5 -B5 --heading | tee "$LOG_DIR/__sorries.txt"
rg -n "^import\s+" lean/dk_math/DkMath -S --heading | tee "$LOG_DIR/__imports.txt"

exit 0
