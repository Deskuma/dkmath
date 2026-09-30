#!/bin/bash

PROJECT_ROOT=`git rev-parse --show-toplevel`
cd $PROJECT_ROOT

mkdir -p python/Tromino/results/repair-depth/w9-oneflip-neighborhood-v24

python3 python/Tromino/search/repair_depth_search.py neighbors \
  python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json \
  --max-depth 10 \
  --node-limit 6000000 \
  --intermediate-policy endpoint \
  --workers "$(nproc)" \
  --output python/Tromino/results/repair-depth/w9-oneflip-neighborhood-v24

cd -
