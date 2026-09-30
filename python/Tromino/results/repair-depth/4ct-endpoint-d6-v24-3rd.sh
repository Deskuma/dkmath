#!/bin/bash

PROJECT_ROOT=`git rev-parse --show-toplevel`
cd $PROJECT_ROOT

# mkdir -p python/Tromino/results/repair-depth/endpoint-d6-v24

# python3 python/Tromino/search/repair_depth_search.py search \
#   --vertices 24 \
#   --jobs 2000 \
#   --steps 2000 \
#   --warmup-flips 48 \
#   --workers "$(nproc)" \
#   --max-depth 8 \
#   --target-depth 6 \
#   --node-limit 750000 \
#   --base-seed 7000000 \
#   --intermediate-policy endpoint \
#   --search-objective resolved \
#   --output python/Tromino/results/repair-depth/endpoint-d6-v24

python3 python/Tromino/search/repair_depth_search.py replay \
  python/Tromino/results/repair-depth/endpoint-d6-v24/best_resolved_witness.json \
  --min-depth 0 \
  --max-depth 10 \
  --node-limit 3000000 \
  --intermediate-policy endpoint \
  --trace \
  --stop-on-success \
  --output python/Tromino/results/repair-depth/endpoint-d6-v24/replay-best-resolved.json

cd -
