#!/bin/bash

PROJECT_ROOT=`git rev-parse --show-toplevel`
cd $PROJECT_ROOT

# mkdir -p python/Tromino/results/repair-depth/endpoint-d8-v24

# python3 python/Tromino/search/repair_depth_search.py search \
#   --vertices 24 \
#   --jobs 3000 \
#   --steps 3000 \
#   --warmup-flips 64 \
#   --workers "$(nproc)" \
#   --max-depth 10 \
#   --target-depth 8 \
#   --node-limit 1500000 \
#   --base-seed 8000000 \
#   --intermediate-policy endpoint \
#   --search-objective resolved \
#   --output python/Tromino/results/repair-depth/endpoint-d8-v24

# python3 python/Tromino/search/repair_depth_search.py replay \
#   python/Tromino/results/repair-depth/endpoint-d8-v24/best_resolved_witness.json \
#   --min-depth 0 \
#   --max-depth 12 \
#   --node-limit 5000000 \
#   --intermediate-policy endpoint \
#   --trace \
#   --stop-on-success \
#   --output python/Tromino/results/repair-depth/endpoint-d8-v24/replay-best-resolved.json

RESULT=python/Tromino/results/repair-depth/endpoint-d8-v24

python3 - <<'PY'
import json
from pathlib import Path

d = Path("python/Tromino/results/repair-depth/endpoint-d8-v24")
for line in (d / "runs.jsonl").read_text().splitlines():
    r = json.loads(line)
    if r["job_seed"] == 8000005:
        (d / "witness-8000005.json").write_text(
            json.dumps(r["witness"], indent=2, sort_keys=True) + "\n"
        )
        print("saved seed 8000005")
        break
else:
    raise SystemExit("seed 8000005 not found")
PY

python3 python/Tromino/search/repair_depth_search.py replay \
  "$RESULT/witness-8000005.json" \
  --min-depth 0 \
  --max-depth 10 \
  --node-limit 5000000 \
  --intermediate-policy endpoint \
  --trace \
  --stop-on-success \
  --output "$RESULT/replay-8000005.json"

cd -
