
#!/usr/bin/env python3
"""
Collatz Cartography: Petal (2^k) shift experiment.

We compare base odd n in [1, 2^k) against shifted n' = n + j*2^k for j>=1,
using the accelerated Collatz map on odd numbers:
    T(n) = (3n+1) / 2^{v2(3n+1)}   (always odd)

We record:
- s(n) = v2(3n+1)
- D_t = t*log2(3) - sum_{i<=t} s_i  (prefix drift)
- max_prefix_D = max_{t<=m} D_t
- Difference segments per step: delta_s, delta_n, v2(|delta_n|)
- first_delta_index = first t where s differs
- tau_r = min { t : v2(|delta_n_t|) < r } for r=1..min(k,12)

This script is intentionally self-contained (no external dependencies beyond numpy/matplotlib).
"""

import argparse
import json
import math
from dataclasses import dataclass
from typing import List, Optional, Dict, Tuple

import numpy as np

LOG2_3 = math.log2(3.0)

def v2_pos(x: int) -> int:
    """2-adic valuation for positive integer x."""
    # x & -x isolates lowest set bit
    return (x & -x).bit_length() - 1

def accel_step_odd(n: int) -> Tuple[int, int]:
    """One accelerated Collatz step on odd n. Returns (next_odd, s=v2(3n+1))."""
    a = 3*n + 1
    s = v2_pos(a)
    nxt = a >> s
    # nxt is odd by construction
    return nxt, s

def trajectory(n0: int, m: int) -> Dict:
    """Compute trajectory log for odd n0 for m steps."""
    n = n0
    s_list = []
    n_list = [n0]
    prefix_D = []
    S = 0
    max_prefix_D = -1e100
    for t in range(1, m+1):
        n, s = accel_step_odd(n)
        s_list.append(s)
        n_list.append(n)
        S += s
        D_t = t*LOG2_3 - S
        prefix_D.append(D_t)
        if D_t > max_prefix_D:
            max_prefix_D = D_t
    return {
        "n0": n0,
        "m": m,
        "n_seq": n_list,       # length m+1 (includes n0)
        "s_seq": s_list,       # length m
        "D_m": prefix_D[-1] if prefix_D else 0.0,
        "max_prefix_D": float(max_prefix_D),
    }

@dataclass
class DiffSeg:
    step: int
    n_base: int
    n_shift: int
    s_base: int
    s_shift: int
    delta_s: int
    delta_n: int
    v2_delta_n: Optional[int]

    def to_dict(self):
        return {
            "step": self.step,
            "n_base": self.n_base,
            "n_shift": self.n_shift,
            "s_base": self.s_base,
            "s_shift": self.s_shift,
            "delta_s": self.delta_s,
            "delta_n": self.delta_n,
            "v2_delta_n": self.v2_delta_n,
        }

def diff_log(n0: int, j: int, k: int, m: int) -> Dict:
    """Compare n0 vs n0 + j*2^k for m steps."""
    shift = j*(1<<k)
    n1 = n0
    n2 = n0 + shift
    segs: List[DiffSeg] = []
    first_delta = None

    # Step-by-step
    for t in range(1, m+1):
        n1_next, s1 = accel_step_odd(n1)
        n2_next, s2 = accel_step_odd(n2)
        dn = n2_next - n1_next
        v2dn = None if dn == 0 else v2_pos(abs(dn))
        ds = s2 - s1
        if first_delta is None and ds != 0:
            first_delta = t
        segs.append(DiffSeg(
            step=t,
            n_base=n1_next, n_shift=n2_next,
            s_base=s1, s_shift=s2,
            delta_s=ds,
            delta_n=dn,
            v2_delta_n=v2dn,
        ))
        n1, n2 = n1_next, n2_next

    # tau_r
    tau_r: Dict[str, Optional[int]] = {}
    for r in range(1, min(k, 12)+1):
        hit = None
        for seg in segs:
            v = seg.v2_delta_n
            if v is None:
                continue
            if v < r:
                hit = seg.step
                break
        tau_r[str(r)] = hit

    # per-log summaries
    delta_s_list = [s.delta_s for s in segs]
    v2_list = [s.v2_delta_n for s in segs if s.v2_delta_n is not None]
    return {
        "n0": n0,
        "k": k,
        "j": j,
        "m": m,
        "shift": shift,
        "first_delta_index": first_delta,
        "tau_r": tau_r,
        "max_abs_delta_s": int(max(abs(x) for x in delta_s_list)) if delta_s_list else 0,
        "min_delta_s": int(min(delta_s_list)) if delta_s_list else 0,
        "sum_delta_s": int(sum(delta_s_list)) if delta_s_list else 0,
        "max_v2_delta_n": int(max(v2_list)) if v2_list else None,
        "segments": [s.to_dict() for s in segs],
    }

def summarize(k: int, m: int, trajs: List[Dict], diffs: List[Dict]) -> Dict:
    stats: Dict[str, float] = {"k": k, "m": m, "num_traj": len(trajs), "num_diffs": len(diffs)}
    Dm = np.array([t["D_m"] for t in trajs], dtype=float)
    maxP = np.array([t["max_prefix_D"] for t in trajs], dtype=float)
    stats["drift_mean"] = float(Dm.mean())
    stats["drift_min"] = float(Dm.min())
    stats["drift_max"] = float(Dm.max())
    stats["max_prefix_D_mean"] = float(maxP.mean())
    stats["max_prefix_D_max"] = float(maxP.max())

    # first_delta distribution
    fd = [d["first_delta_index"] for d in diffs if d["first_delta_index"] is not None]
    stats["first_delta_rate"] = float(len(fd)/len(diffs)) if diffs else 0.0
    if fd:
        fd_arr = np.array(fd, dtype=float)
        stats["first_delta_mean"] = float(fd_arr.mean())
        stats["first_delta_median"] = float(np.median(fd_arr))
        stats["first_delta_min"] = float(fd_arr.min())
        stats["first_delta_max"] = float(fd_arr.max())

    # tau_r means for r=2..6
    for r in [2,3,4,5,6]:
        vals = []
        for d in diffs:
            t = d["tau_r"].get(str(r))
            if t is not None:
                vals.append(t)
        if vals:
            arr = np.array(vals, dtype=float)
            stats[f"tau_{r}_mean"] = float(arr.mean())
            stats[f"tau_{r}_median"] = float(np.median(arr))
            stats[f"tau_{r}_min"] = float(arr.min())
            stats[f"tau_{r}_max"] = float(arr.max())

    # correlation max_prefix_D(base n0) vs tau_4 (per diff)
    mp_by_n0 = {t["n0"]: t["max_prefix_D"] for t in trajs}
    pairs = []
    for d in diffs:
        t4 = d["tau_r"].get("4")
        if t4 is None:
            continue
        pairs.append((mp_by_n0.get(d["n0"]), t4))
    pairs = [(x,y) for (x,y) in pairs if x is not None]
    if len(pairs) >= 3:
        xs = np.array([p[0] for p in pairs], dtype=float)
        ys = np.array([p[1] for p in pairs], dtype=float)
        if xs.std() > 0 and ys.std() > 0:
            stats["corr_maxPrefix_tau4"] = float(np.corrcoef(xs, ys)[0,1])

    return stats

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--m", type=int, default=256)
    ap.add_argument("--num-bases", type=int, default=64, help="how many odd bases to sample from [1,2^k)")
    ap.add_argument("--max-j", type=int, default=16, help="how many petals: compare to n + j*2^k for j=1..max-j")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--output", type=str, required=True)
    args = ap.parse_args()

    k = args.k
    m = args.m
    max_j = args.max_j

    rng = np.random.default_rng(args.seed)
    # sample odd bases from [1,2^k)
    N = 1<<k
    odds = np.arange(1, N, 2, dtype=np.int64)
    if args.num_bases >= len(odds):
        bases = odds.tolist()
    else:
        idx = rng.choice(len(odds), size=args.num_bases, replace=False)
        bases = [int(odds[i]) for i in idx]
    bases.sort()

    trajs = [trajectory(n0, m) for n0 in bases]
    diffs = []
    for n0 in bases:
        for j in range(1, max_j+1):
            diffs.append(diff_log(n0, j, k, m))

    stats = summarize(k, m, trajs, diffs)

    out = args.output
    import os
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, f"trajectories_k{k}.json"), "w") as f:
        json.dump(trajs, f, indent=2)
    with open(os.path.join(out, f"differences_k{k}.json"), "w") as f:
        json.dump(diffs, f, indent=2)
    with open(os.path.join(out, f"statistics_k{k}.json"), "w") as f:
        json.dump(stats, f, indent=2)
    print("Wrote:", out)

if __name__ == "__main__":
    main()
