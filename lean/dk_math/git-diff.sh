#!/bin/bash

# This script generates a diff of the current Git repository and opens it in VS Code.
# This is the diff from the current tracked state. New files and untracked changes are not included.
# You can specify a commit hash to get a diff that includes the current changes.
# Use four backslashes to avoid nested code blocks in Markdown.

echo '````diff' > __git.diff
git diff $@ >> __git.diff
echo '````' >> __git.diff
code __git.diff
