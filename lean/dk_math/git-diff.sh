#!/bin/bash

# This script generates a diff of the current Git repository and opens it in VS Code.
# This is the diff from the current tracked state. New files and untracked changes are not included.
# You can specify a commit hash to get a diff that includes the current changes.
# Use four backslashes `diff` and five backslashes `md` to avoid nested code blocks in Markdown.

# オプションに `-H` が指定されたら `HEAD~1` を使用して、前のコミットとの差分を生成します。
if [[ "$1" == "-H" ]]; then
  shift
  COMMIT="HEAD~1"
else
  COMMIT=""
fi

echo '`````md' > __git.diff
echo '````diff' >> __git.diff
git diff $COMMIT $@ >> __git.diff
echo '````' >> __git.diff
echo '`````' >> __git.diff
code __git.diff
