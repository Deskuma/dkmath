#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# Delete development graph images for experiment #4

# グラフ画像の削除
import os
import argparse
from fig_config import fig4_config

# コマンドライン引数の解析
parser = argparse.ArgumentParser(description="Remove generated graph image files.")
# -D オプションを追加
parser.add_argument(
    "-D",
    "--delete",
    action="store_true",
    help="Actually delete the files instead of just printing their names.",
)
args = parser.parse_args()

prefix = "__" + fig4_config.prefix_fig + "#4-"
suffix = ".png"

for filename in os.listdir("."):
    if filename.startswith(prefix) and filename.endswith(suffix):
        print(f"Removing file: {filename}")
        if args.delete:
            os.remove(filename)
if not args.delete:
    print("No files were deleted. Use the -D option to actually delete the files.")
