#!/bin/bash

PROJECT_ROOT=`git rev-parse --show-toplevel`
cd $PROJECT_ROOT

RESULT=python/Tromino/results/repair-depth/d5-v24

python3 - <<'PY'
import json
from pathlib import Path

d = Path("python/Tromino/results/repair-depth/d5-v24")
rows = [json.loads(x) for x in (d / "runs.jsonl").read_text().splitlines() if x.strip()]

solved = [r for r in rows if r.get("success")]
best = max(
    solved,
    key=lambda r: (
        r.get("required_depth", -1),
        tuple(r.get("objective", [])),
    ),
)

(d / "best_resolved_witness.json").write_text(
    json.dumps(best["witness"], indent=2, sort_keys=True) + "\n"
)

print("best resolved:",
      "seed =", best["job_seed"],
      "depth =", best["required_depth"],
      "objective =", best["objective"])
PY

# unresolved best: strict を緩めて「本当に深い壁」か
# 「strict invariant が強すぎるだけ」かを判別
python3 python/Tromino/search/repair_depth_search.py replay \
  "$RESULT/best_witness.json" \
  --min-depth 0 \
  --max-depth 10 \
  --node-limit 2000000 \
  --intermediate-policy endpoint \
  --trace \
  --stop-on-success \
  --output "$RESULT/replay-endpoint.json"

# depth-6 solved witness も独立保存して再確認
python3 python/Tromino/search/repair_depth_search.py replay \
  "$RESULT/best_resolved_witness.json" \
  --min-depth 0 \
  --max-depth 8 \
  --node-limit 2000000 \
  --intermediate-policy strict \
  --trace \
  --stop-on-success \
  --output "$RESULT/replay-best-resolved.json"

cd -
