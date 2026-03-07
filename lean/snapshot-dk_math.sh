#!/bin/bash

DTM=$(date +%y%m%d-%H%M)

# dk_math ディレクトリを tar.gz 形式で圧縮する
# .lake と .github .git ディレクトリを除外する
# 各ディレクトリ内のドットファイルも除外する
tar cvzf __snapshot-dk_math-lean-code-$DTM.tar.gz \
    --exclude='./dk_math/.lake' \
    --exclude='./dk_math/.vscode' \
    --exclude='./dk_math/.github' \
    --exclude='./dk_math/.git' \
    --exclude='./dk_math/notes' \
    --exclude='./**/.pytest_cache' \
    --exclude='./**/__pycache__/' \
    --exclude='./**/__*' \
    --exclude='./**/*.png' \
    --exclude='./**/*.jpg' \
    --exclude='./**/*.zip' \
    ./dk_math
sha256sum __snapshot-dk_math-lean-code-$DTM.tar.gz > __snapshot-dk_math-lean-code-$DTM.tar.gz.sha256

ls -l __snapshot-dk_math-lean-code-$DTM.tar.gz
ls -l __snapshot-dk_math-lean-code-$DTM.tar.gz.sha256
