#!/bin/bash

# Count the number of lines of Lean code in the current directory and its subdirectories.
echo "Counting lines of Lean code in DkMath..."
find DkMath/ -name "*.lean" | LANG=C xargs wc -l | tail -n 1
