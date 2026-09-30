#!/bin/bash

PROJECT_ROOT=`git rev-parse --show-toplevel`
cd $PROJECT_ROOT

mkdir -p python/Tromino/results/repair-depth/seeded-w9-d10-v24

python3 python/Tromino/search/repair_depth_search.py search \
  --vertices 24 \
  --jobs 64 \
  --steps 512 \
  --warmup-flips 0 \
  --workers "$(nproc)" \
  --max-depth 11 \
  --target-depth 10 \
  --node-limit 3000000 \
  --base-seed 10000000 \
  --intermediate-policy endpoint \
  --search-objective resolved \
  --stop-on-target \
  --initial-witness \
    python/Tromino/results/repair-depth/endpoint-d9-v24/best_resolved_witness.json \
  --output python/Tromino/results/repair-depth/seeded-w9-d10-v24

python3 python/Tromino/search/repair_depth_search.py replay \
  python/Tromino/results/repair-depth/seeded-w9-d10-v24/best_resolved_witness.json \
  --min-depth 8 \
  --max-depth 11 \
  --node-limit 6000000 \
  --intermediate-policy endpoint \
  --trace \
  --stop-on-success \
  --output python/Tromino/results/repair-depth/seeded-w9-d10-v24/replay-best-resolved.json

cd -
