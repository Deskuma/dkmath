#!/usr/bin/env bash
# Wrapper to run assistant_driver.py from lean/dk_math
set -euo pipefail
cd "$(dirname "$0")"
python3 assistant_driver.py "$@"
