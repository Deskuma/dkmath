#!/bin/bash

PROJECT_ROOT=`git rev-parse --show-toplevel`
cd $PROJECT_ROOT

mkdir -p python/Tromino/results/repair-depth/w10-state-component-v24

python3 python/Tromino/search/repair_depth_search.py state-component-scan \
  python/Tromino/results/repair-depth/seeded-w9-frontier2-d10-v24/best_frontier_witness.json \
  --step 16 \
  --prefix-depth 10 \
  --max-depth 11 \
  --node-limit 6000000 \
  --state-limit 512 \
  --workers "$(nproc)" \
  --intermediate-policy endpoint \
  --output python/Tromino/results/repair-depth/w10-state-component-v24

cd -
