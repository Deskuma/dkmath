#!/usr/bin/env bash
set -euo pipefail

# Configuration
LOG_DIR="logs"  # Directory to store logs data
SUMMARY_REPORT_DIR="$LOG_DIR/summary_report"  # Directory to store final summary report
REPORT_DIR="$LOG_DIR/reports"  # Directory to store generated reports archives
ARCHIVE_NAME="$LOG_DIR/__summary_report_data.tar.gz"

# Ensure directories exist
mkdir -p "$LOG_DIR" "$SUMMARY_REPORT_DIR" "$REPORT_DIR"

# Ensure required external commands are available
require_cmd() {
  command -v "$1" >/dev/null 2>&1 || { echo "Required command not found: $1" >&2; exit 1; }
}
require_cmd find
require_cmd sort
require_cmd tee
require_cmd rg
require_cmd tar
require_cmd diff
# 'tree' is optional — provide fallback
if ! command -v tree >/dev/null 2>&1; then
  TREE_AVAILABLE=false
else
  TREE_AVAILABLE=true
fi

# cleanup handler — only remove generated __*.txt files (safe)
# trap 'find "${DIFF_WORK_DIR}" -maxdepth 2 -type f -name "__*.txt" -delete || true' EXIT

# clear old logs
rm -f "$SUMMARY_REPORT_DIR"/__*.txt

# rotate previous archive (if present) and keep archives in REPORT_DIR
BACKUP_ARCHIVE_NAME=$REPORT_DIR"/__summary_report_data_backup_$(date +%Y%m%d%H%M%S).tar.gz"
if [ -f "$ARCHIVE_NAME" ]; then
  mv "$ARCHIVE_NAME" "$BACKUP_ARCHIVE_NAME"
fi

# Create summary report data by extracting relevant information from the codebase

# file tree
## project full tree (exclude .git, logs, .lake, etc.)
find . | grep -vE '(\.git|logs|^./lean/dk_math/.lake|\.github|\.vscode|\.pytest_cache|__pycache__|venv|.*\.pyc$|.*\.pyo$|__fig\#|/__.*)' | sort | tee "$LOG_DIR/__project_find_files.txt"

if [ "$TREE_AVAILABLE" = true ]; then
  tree lean/dk_math/DkMath | tee "$SUMMARY_REPORT_DIR/__file_tree_in_dkmath.txt"
else
  find lean/dk_math/DkMath -print | sed 's|[^/]*/|  |g' | tee "$SUMMARY_REPORT_DIR/__file_tree_in_dkmath.txt"
fi

# Extract theorems, lemmas, defs, sorries, and imports from the codebase
rg -n "^(theorem|lemma|def)\s+" lean/dk_math/DkMath -S -A5 -B2 --heading | tee "$SUMMARY_REPORT_DIR/__theorems-heading.txt"
rg -n --type-add 'lean:*.lean' --type lean "\bsorry\b" -S -A5 -B5 --heading | tee "$SUMMARY_REPORT_DIR/__sorries.txt"
rg -n "^import\s+" lean/dk_math/DkMath -S --heading | tee "$SUMMARY_REPORT_DIR/__imports.txt"

# diff: compare the rotated BACKUP_ARCHIVE_NAME (if created) with the current summary_report
# exclude .vscode
git diff mark-summary-report | awk 'BEGIN {IGNORE_FLAG=0} /diff --git/{ if ($0 ~ /\.vscode/) {IGNORE_FLAG=1} else {IGNORE_FLAG=0} } !IGNORE_FLAG {print}' | tee "$SUMMARY_REPORT_DIR/__git_diff_summary_report.txt" || true
# update the tag to mark the current summary report state
git tag -d mark-summary-report && git tag mark-summary-report || true

# archive the logs (saved in $LOG_DIR to avoid self-inclusion)
tar -czf "$ARCHIVE_NAME" -C "$SUMMARY_REPORT_DIR" .

# large files for review
rg -n "^(theorem|lemma|def)\s+" lean/dk_math/DkMath -S -A5 -B2 | tee "$SUMMARY_REPORT_DIR/___theorems.txt"
rg -n "^(theorem|lemma|def)\s+" lean/dk_math/DkMath -S -A5 -B5 --heading | rg -n "^[^:]+:" | tee "$SUMMARY_REPORT_DIR/___theorems-with-filename.txt"

exit 0
