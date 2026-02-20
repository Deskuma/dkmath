#!/bin/bash

# Create: Combine all dkmath lean files into one file and save it as './logs/__dkmath-all.lean.txt'
ROOT_LOGS_DIR="../../logs"
LOGS_DIR="./logs"
OUTPUT_FILE="$LOGS_DIR/__dkmath-all.lean.txt"

# Verify that the logs directory exists and lakefile.toml file, DkMath directory exists
if [ ! -d "$LOGS_DIR" ]; then
  echo "Error: Logs directory '$LOGS_DIR' does not exist."
  exit 1
fi
if [ ! -f "lakefile.toml" ]; then
  echo "Error: lakefile.toml not found in the current directory."
  exit 1
fi
if [ ! -d "DkMath" ]; then
  echo "Error: DkMath directory not found at './DkMath'."
  exit 1
fi

SEP1="============================================================" # 60 char. separator for log readability
SEP2="------------------------------------------------------------" # 60 char. separator for log readability

# Combine all .lean files in the DkMath directory and its subdirectories into one file
# exclude:
#   .lake, .github, .pytest_cache directory and its contents
find . -type f -name '*.lean' ! -path './.lake/*' ! -path './.github/*' ! -path './.pytest_cache/*' \
    | sort \
    | while IFS= read -r f; do echo "$SEP1"; echo "$f"; echo "$SEP2";cat "$f"; echo; done > "$OUTPUT_FILE" \
&& echo "Created: $OUTPUT_FILE" \
&& ls -l "$OUTPUT_FILE" \
&& wc -l "$OUTPUT_FILE"

# gzip the output file to save space
gzip -f "$OUTPUT_FILE" \
&& echo "Compressed: $OUTPUT_FILE.gz" \
&& ls -l "$OUTPUT_FILE.gz" \
&& zcat "$OUTPUT_FILE.gz" | wc -l

# copy the gzipped file to the logs directory (if not already there)
cp "$OUTPUT_FILE.gz" "$ROOT_LOGS_DIR/"
echo "Copy: $OUTPUT_FILE.gz to $ROOT_LOGS_DIR/"
