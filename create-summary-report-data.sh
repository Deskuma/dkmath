#!/usr/bin/env bash
set -euo pipefail

# Configuration
LOG_DIR="logs"  # Directory to store logs data
SUMMARY_REPORT_DIR="$LOG_DIR/summary_report"  # Directory to store final summary report
REPORT_DIR="$LOG_DIR/reports"  # Directory to store generated reports archives
DIFF_WORK_DIR="$LOG_DIR/diff_work"  # Directory to store diff work data
ARCHIVE_NAME="__summary_report_data.tar.gz"

# Ensure directories exist
mkdir -p "$LOG_DIR" "$SUMMARY_REPORT_DIR" "$DIFF_WORK_DIR" "$REPORT_DIR"

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

# cleanup handler
trap 'rm -rf "${DIFF_WORK_DIR}"/*' EXIT

# clear old logs
rm -f "$LOG_DIR"/__*.txt

# rotate previous archive (if present) and keep archives in REPORT_DIR
BACKUP_ARCHIVE_NAME="__summary_report_data_backup_$(date +%Y%m%d%H%M%S).tar.gz"
if [ -f "$REPORT_DIR/$ARCHIVE_NAME" ]; then
  mv "$REPORT_DIR/$ARCHIVE_NAME" "$REPORT_DIR/$BACKUP_ARCHIVE_NAME"
fi

# Create summary report data by extracting relevant information from the codebase

# file tree
## project full tree (exclude .git, logs, .lake, etc.)
find . \
  -path './.git' -prune -o \
  -path './logs' -prune -o \
  -path './lean/dk_math/.lake' -prune -o \
  -path './.github' -prune -o \
  -path './.vscode' -prune -o \
  -path './.pytest_cache' -prune -o \
  -path './__pycache__' -prune -o \
  -path './venv' -prune -o \
  -type f -print | grep -vE '(\.pyc$|\.pyo$|__fig#|/__.*)' | sort | tee "$LOG_DIR/__project_find_files.txt"

if [ "$TREE_AVAILABLE" = true ]; then
  tree lean/dk_math/DkMath | tee "$SUMMARY_REPORT_DIR/__file_tree_in_dkmath.txt"
else
  find lean/dk_math/DkMath -print | sed 's|[^/]*/|  |g' | tee "$SUMMARY_REPORT_DIR/__file_tree_in_dkmath.txt"
fi

# Extract theorems, lemmas, defs, sorries, and imports from the codebase
rg -n "^(theorem|lemma|def)\s+" lean/dk_math/DkMath -S -A5 -B2 --heading | tee "$SUMMARY_REPORT_DIR/__theorems-heading.txt"
rg -n --type-add 'lean:*.lean' --type lean "\bsorry\b" -S -A5 -B5 --heading | tee "$SUMMARY_REPORT_DIR/__sorries.txt"
rg -n "^import\s+" lean/dk_math/DkMath -S --heading | tee "$SUMMARY_REPORT_DIR/__imports.txt"

# diff latest backup archive (if present) with current logs
LATEST_BACKUP=$(ls -1t "$REPORT_DIR"/__summary_report_data_backup_*.tar.gz 2>/dev/null | head -n1 || true)
if [ -n "$LATEST_BACKUP" ]; then
  rm -rf "$DIFF_WORK_DIR"/*
  mkdir -p "$DIFF_WORK_DIR"
  tar -xzf "$LATEST_BACKUP" -C "$DIFF_WORK_DIR"
  diff -r "$DIFF_WORK_DIR" "$SUMMARY_REPORT_DIR" | tee "$SUMMARY_REPORT_DIR/__diff_summary_report_data.txt" || true
  rm -rf "$DIFF_WORK_DIR"/*
else
  echo "No previous summary report data tarball found. Skipping diff."
fi

# archive the logs (saved in $REPORT_DIR to avoid self-inclusion)
tar -czf "$REPORT_DIR/$ARCHIVE_NAME" -C "$LOG_DIR" .

# large files for review
rg -n "^(theorem|lemma|def)\s+" lean/dk_math/DkMath -S -A5 -B2 | tee "$SUMMARY_REPORT_DIR/___theorems.txt"
rg -n "^(theorem|lemma|def)\s+" lean/dk_math/DkMath -S -A5 -B5 --heading | rg -n "^[^:]+:" | tee "$SUMMARY_REPORT_DIR/___theorems-with-filename.txt"

exit 0
