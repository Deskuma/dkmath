#!/bin/bash
# `sed 's/^trace: .> LEAN_PATH=.*$/trace: .> LEAN_PATH=.../'` は、
# ビルドログの中で `LEAN_PATH` を含む行を見つけて、その部分を `LEAN_PATH=...` に置き換えます。
# これにより、ビルドログが読みやすくなります。
# `tee __build.log` は、ビルドの出力を `__build.log` ファイルに保存しつつ、同時にターミナルにも表示します。
# escape sequence を削除して、ビルドの進行状況をわかりやすくする
# 空行を削除する

# オプションのチェック

# `-C`, `--check` オプションが指定された場合、`lake build -v --no-ansi --log-level=info | grep -B1 "file: "` を実行して、ビルドの詳細なログを表示し、エラーが発生したファイルを特定します。
if [[ "$1" == "-C" || "$1" == "--check" ]]; then
    echo "🔍 Checking build with detailed logs..."
    lake build -v --no-ansi --log-level=info | grep -B1 "file: " | tee __check.log
    build_exit_code=${PIPESTATUS[0]}
    result_msg=""
    if [ "$build_exit_code" -eq 0 ]; then
      result_msg="✅️ build succeeded"
    else
      result_msg="❌️ build failed"
    fi
    echo "🔍 Checking build results..."
    echo "  see: __check.log:1"
    echo ${result_msg}
    exit ${build_exit_code}
fi

# `-T`, `--test` オプションが指定された場合、DkMathTest のテストビルドを実行します。
if [[ "$1" == "-T" || "$1" == "--test" ]]; then
    echo "🔍 Running test build..."
    ./lean-test.sh
    build_exit_code=${PIPESTATUS[0]}
    exit ${build_exit_code}
fi

# デフォルトのビルド
echo "🔍 Running default build..."
echo "🚀 Starting build Lean..."
lake --quiet --no-ansi build $@ \
    | sed 's/^trace: .> LEAN_PATH=.*$//' \
    | sed 's/^✔ \[[0-9]\+\/[0-9]\+\] Replayed \(.*\)$/✔ [\1]/' \
    | sed 's/\x1b\[[0-9;]*m//g' \
    | grep -v 'Mathlib' \
    | grep -v 'Batteries' \
    | grep -v 'Aesop' \
    | grep -v '^$' \
    | tee __build.log
build_exit_code=${PIPESTATUS[0]}

# ビルドの結果をチェックして、成功か失敗かを表示します。
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
