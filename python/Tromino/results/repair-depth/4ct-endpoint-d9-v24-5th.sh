#!/bin/bash

PROJECT_ROOT=`git rev-parse --show-toplevel`
cd $PROJECT_ROOT

mkdir -p python/Tromino/results/repair-depth/endpoint-d9-v24

python3 python/Tromino/search/repair_depth_search.py search \
  --vertices 24 \
  --jobs 2000 \
  --steps 3000 \
  --warmup-flips 64 \
  --workers "$(nproc)" \
  --max-depth 10 \
  --target-depth 9 \
  --node-limit 1500000 \
  --base-seed 9000000 \
  --intermediate-policy endpoint \
  --search-objective resolved \
  --stop-on-target \
  --output python/Tromino/results/repair-depth/endpoint-d9-v24

python3 python/Tromino/search/repair_depth_search.py replay \
  python/Tromino/results/repair-depth/endpoint-d9-v24/best_resolved_witness.json \
  --min-depth 0 \
  --max-depth 11 \
  --node-limit 5000000 \
  --intermediate-policy endpoint \
  --trace \
  --stop-on-success \
  --output python/Tromino/results/repair-depth/endpoint-d9-v24/replay-best-resolved.json

cd -
