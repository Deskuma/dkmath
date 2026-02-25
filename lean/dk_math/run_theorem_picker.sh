#!/usr/bin/env bash
# Wrapper to run theorem_picker.py from lean/dk_math
set -euo pipefail
cd "$(dirname "$0")"
# Allow passing any args through
python3 theorem_picker.py "$@"
