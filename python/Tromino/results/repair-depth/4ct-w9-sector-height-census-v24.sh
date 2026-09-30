#!/bin/bash

PROJECT_ROOT=`git rev-parse --show-toplevel`
cd $PROJECT_ROOT

mkdir -p python/Tromino/results/repair-depth/w9-sector-height-census-v24

python3 python/Tromino/search/sector_height_census.py \
  python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json \
  --source-component-summary python/Tromino/results/repair-depth/w9-state-component-v24/summary.json \
  --flip-census-summary python/Tromino/results/repair-depth/w9-flip-chamber-census-v24/summary.json \
  --step 16 \
  --prefix-depth 10 \
  --max-depth 11 \
  --node-limit 6000000 \
  --state-limit 512 \
  --workers "$(nproc)" \
  --intermediate-policy endpoint \
  --output python/Tromino/results/repair-depth/w9-sector-height-census-v24

cd -
