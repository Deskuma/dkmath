#!/bin/bash
# `sed 's/^trace: .> LEAN_PATH=.*$/trace: .> LEAN_PATH=.../'` は、
# ビルドログの中で `LEAN_PATH` を含む行を見つけて、その部分を `LEAN_PATH=...` に置き換えます。
# これにより、ビルドログが読みやすくなります。
# `tee __build.log` は、ビルドの出力を `__build.log` ファイルに保存しつつ、同時にターミナルにも表示します。
# escape sequence を削除して、ビルドの進行状況をわかりやすくする
# 空行を削除する
echo "🚀 Starting build Lean..."
lake --quiet --no-ansi test $@ \
    | sed 's/^trace: .> LEAN_PATH=.*$//' \
    | sed 's/^✔ \[[0-9]\+\/[0-9]\+\] Replayed \(.*\)$/✔ [\1]/' \
    | sed 's/\x1b\[[0-9;]*m//g' \
    | grep -v 'Mathlib' \
    | grep -v 'Batteries' \
    | grep -v 'Aesop' \
    | grep -v '^$' \
    | tee __build.log
build_exit_code=${PIPESTATUS[0]}
result_msg=""
if [ "$build_exit_code" -eq 0 ]; then
  result_msg="✅️ build succeeded"
else
  result_msg="❌️ build failed"
fi
echo "🔍 Checking build results..."
echo "  see: __build.log:1"
echo ${result_msg}

# Exit with lake's exit code so callers (scripts) can detect failure
exit ${build_exit_code}
