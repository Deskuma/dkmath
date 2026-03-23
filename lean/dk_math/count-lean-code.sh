#!/bin/bash

# Count the number of lines of Lean code in the current directory and its subdirectories.
echo "Counting lines of Lean code in DkMath..."
find DkMath/ -name "*.lean" | LANG=C xargs wc -l | tail -n 1
# 埋め込みに適しているカウント方式はこっち
# find DkMath/ -name "*.lean" -print0 | LANG=C xargs -0 -n1 wc -l | awk '{sum += $1} END {print sum}'