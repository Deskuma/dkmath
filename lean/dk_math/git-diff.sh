#!/bin/bash

echo '```diff' > __git.diff
git diff $@ >> __git.diff
echo '```' >> __git.diff
code __git.diff
