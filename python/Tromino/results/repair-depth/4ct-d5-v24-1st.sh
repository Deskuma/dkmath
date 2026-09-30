#!/bin/bash

PROJECT_ROOT=`git rev-parse --show-toplevel`
cd $PROJECT_ROOT

mkdir -p python/Tromino/results/repair-depth/d5-v24

python3 python/Tromino/search/repair_depth_search.py search \
  --vertices 24 \
  --jobs 2000 \
  --steps 2000 \
  --warmup-flips 48 \
  --workers "$(nproc)" \
  --max-depth 6 \
  --target-depth 5 \
  --node-limit 500000 \
  --base-seed 6000000 \
  --intermediate-policy strict \
  --output python/Tromino/results/repair-depth/d5-v24

cd -
