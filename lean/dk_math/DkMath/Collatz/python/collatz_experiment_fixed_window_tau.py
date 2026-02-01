#!/usr/bin/env python3
"""
CollatzCartography: Experimental Python framework for observing petal structure.

This module generates logarithmic data from the accelerated Collatz map:
  - Acceleration log: (n, s, S_m, D_m) sequences
  - Difference log: (Δs_i, first singularity index, etc.) for block comparisons
  - Heatmaps and statistics to extract boundary conditions

Usage:
    python collatz_experiment.py --k 8 --max_m 256 --output results/

Author: D. and Wise Wolf (2026)
License: MIT
"""

import numpy as np
import math
import json
from typing import List, Dict, Optional
from dataclasses import dataclass, asdict
import argparse
from pathlib import Path


# ============================================================================
# Core Arithmetic: Collatz Dynamics
# ============================================================================


def v2(a: int) -> int:
    """Compute v₂(a): the 2-adic valuation (highest power of 2 dividing a)."""
    if a == 0:
        return 0
    count = 0
    while a % 2 == 0:
        count += 1
        a //= 2
    return count


def C(n: int) -> int:
    """Standard Collatz map: C(n) = n/2 if even, else 3n+1."""
    return n // 2 if n % 2 == 0 else 3 * n + 1


def T(n: int) -> int:
    """Accelerated Collatz map (on odd n): T(n) = (3n+1) / 2^v₂(3n+1)."""
    if n % 2 == 0:
        raise ValueError(f"T requires odd input, got {n}")
    a = 3 * n + 1
    s = v2(a)
    return a >> s  # a / 2^s


def s_func(n: int) -> int:
    """Observation function: s(n) = v₂(3n+1) for odd n."""
    if n % 2 == 0:
        raise ValueError(f"s(n) requires odd input, got {n}")
    return v2(3 * n + 1)


def log2_3() -> float:
    """Precomputed log₂(3)."""
    return math.log(3) / math.log(2)


# ============================================================================
# Trajectory Computation
# ============================================================================


@dataclass
class TrajectorySegment:
    """Record for one step of the accelerated Collatz trajectory."""

    step: int
    n: int
    a: int  # = 3n+1
    s: int  # = v₂(a)
    n_next: int  # = a / 2^s


@dataclass
class TrajectoryLog:
    """Complete trajectory log over m steps from initial n₀."""

    n0: int
    k: int  # block size exponent (2^k)
    m: int  # number of steps
    log2_3: float
    segments: List[TrajectorySegment]

    @property
    def S_m(self) -> int:
        """Partial sum ∑ₛ s_i over all segments."""
        return sum(seg.s for seg in self.segments)

    @property
    def D_m(self) -> float:
        """Drift: D_m = m·log₂(3) - S_m."""
        return self.m * self.log2_3 - self.S_m

    @property
    def max_prefix_D(self) -> float:
        """Maximum prefix drift: max_{1<=t<=m} (t·log₂(3) - ∑_{i<=t} s_i)."""
        ssum = 0
        best = float('-inf')
        for t, seg in enumerate(self.segments, start=1):
            ssum += seg.s
            D_t = t * self.log2_3 - ssum
            if D_t > best:
                best = D_t
        return best if self.segments else float('-inf')

    @property
    def s_sequence(self) -> List[int]:
        """Extract the sequence of s values."""
        return [seg.s for seg in self.segments]

    def to_dict(self):
        """Serialize to dict for JSON export."""
        return {
            "n0": self.n0,
            "k": self.k,
            "m": self.m,
            "log2_3": self.log2_3,
            "S_m": self.S_m,
            "D_m": self.D_m,
            "max_prefix_D": self.max_prefix_D,
            "s_sequence": self.s_sequence,
            "segments": [asdict(seg) for seg in self.segments],
        }


def compute_trajectory(
    n0: int, m: int, k: int
) -> TrajectoryLog:
    """
    Compute the accelerated Collatz trajectory starting from odd n₀ over m steps.

    Args:
        n0: Starting odd natural number
        m: Number of steps
        k: Block size exponent (for metadata)

    Returns:
        TrajectoryLog with all segments recorded
    """
    if n0 % 2 == 0:
        raise ValueError(f"n0 must be odd, got {n0}")

    segments = []
    n = n0
    for step in range(m):
        a = 3 * n + 1
        s = v2(a)
        n_next = a >> s

        segments.append(TrajectorySegment(step, n, a, s, n_next))
        n = n_next

    return TrajectoryLog(
        n0=n0, k=k, m=len(segments), log2_3=log2_3(), segments=segments
    )


# ============================================================================
# Block Comparison and Difference Logging
# ============================================================================


@dataclass
class DifferenceSegment:
    """Record for comparing one step of two related trajectories."""

    step: int
    delta_s: int  # = s(n') - s(n)
    s_base: int
    s_shifted: int
    delta_n: int  # = n'(t) - n(t)
    v2_delta_n: Optional[int]  # = v2(|delta_n|), None if delta_n=0
    singular_at_base: bool  # = s(n) >= k


@dataclass
class DifferenceLog:
    """Comparison log between base trajectory and shifted trajectory."""

    n0: int
    k: int  # block size exponent
    m_shift: int  # m in n' = n + 2^k·m
    j: int  # j in the block index
    m: int  # comparison length
    segments: List[DifferenceSegment]

    @property
    def first_delta_index(self) -> Optional[int]:
        """Return the first step i where delta_s != 0, or None if none."""
        for i, seg in enumerate(self.segments):
            if seg.delta_s != 0:
                return i
        return None

    @property
    def singular_indices(self) -> List[int]:
        """Return all step indices where v₂(3n+1) >= k."""
        return [seg.step for seg in self.segments if seg.singular_at_base]

    @property
    def tau_r(self) -> dict:
        """Terrain collapse times: tau_r[r] = min{t : v2(|Δn_t|) < r}. Keys are strings."""
        out = {}
        r_max = min(self.k, 12)
        for r in range(1, r_max + 1):
            hit = None
            for seg in self.segments:
                v = seg.v2_delta_n
                if v is None:
                    continue
                if v < r:
                    hit = seg.step
                    break
            out[str(r)] = hit
        return out

    def to_dict(self):
        """Serialize to dict."""
        deltas = [seg.delta_s for seg in self.segments]
        v2s = [seg.v2_delta_n for seg in self.segments if seg.v2_delta_n is not None]
        return {
            "n0": self.n0,
            "k": self.k,
            "m_shift": self.m_shift,
            "j": self.j,
            "m": self.m,
            "first_delta_index": self.first_delta_index,
            "first_delta_value": (deltas[self.first_delta_index] if self.first_delta_index is not None else None),
            "singular_indices": self.singular_indices,
            "tau_r": self.tau_r,
            "max_delta_s": max(deltas) if deltas else 0,
            "min_delta_s": min(deltas) if deltas else 0,
            "max_abs_delta_s": max((abs(x) for x in deltas), default=0),
            "sum_delta_s": int(sum(deltas)) if deltas else 0,
            "max_v2_delta_n": (max(v2s) if v2s else None),
            "segments": [asdict(seg) for seg in self.segments],
        }


def compute_difference_log(
    log_base: TrajectoryLog, m_shift: int, j: int
) -> DifferenceLog:
    """
    Compare trajectory from n with shifted trajectory from n' = n + 2^k·j·m_shift.

    Args:
        log_base: Base trajectory (from n₀)
        m_shift: Multiplier m in n' = n + 2^k·m
        j: Block index (conceptually, but here we use m_shift directly)

    Returns:
        DifferenceLog recording differences at each step
    """
    n0 = log_base.n0
    k = log_base.k
    block_size = 1 << k  # 2^k

    n_shifted = n0 + (block_size * m_shift)

    # Compute shifted trajectory
    log_shifted = compute_trajectory(n_shifted, log_base.m, k)

    segments = []
    for i in range(min(len(log_base.segments), len(log_shifted.segments))):
        seg_base = log_base.segments[i]
        seg_shifted = log_shifted.segments[i]

        delta_s = seg_shifted.s - seg_base.s
        singular = seg_base.s >= k

        segments.append(
            DifferenceSegment(
                step=i,
                delta_s=delta_s,
                s_base=seg_base.s,
                s_shifted=seg_shifted.s,
                delta_n=(seg_shifted.n - seg_base.n),
                v2_delta_n=(v2(abs(seg_shifted.n - seg_base.n)) if (seg_shifted.n - seg_base.n) != 0 else None),
                singular_at_base=singular,
            )
        )

    return DifferenceLog(
        n0=n0, k=k, m_shift=m_shift, j=j, m=len(segments), segments=segments
    )


# ============================================================================
# Experimental Framework
# ============================================================================


class ExperimentConfig:
    """Configuration for a cartography experiment."""

    def __init__(self, k: int, max_m: int = 256, num_bases: int = 32):
        self.k = k
        self.block_size = 1 << k
        self.max_m = max_m
        self.num_bases = num_bases
        self.log2_3 = log2_3()

    def base_numbers(self) -> List[int]:
        """Generate base odd numbers to study (up to block size)."""
        bases = []
        for n in range(1, self.block_size, 2):  # Odd numbers only
            bases.append(n)
        return bases[: self.num_bases]

    def shift_offsets(self) -> List[int]:
        """Shift multipliers m to compare: small subset."""
        return list(range(1, min(self.block_size, 16)))


class CartographyExperiment:
    """Main experiment: generate logs and extract statistics."""

    def __init__(self, config: ExperimentConfig):
        self.config = config
        self.trajectory_logs: List[TrajectoryLog] = []
        self.difference_logs: List[DifferenceLog] = []

    def run(self):
        """Execute the cartography experiment."""
        print(
            f"[CartographyExperiment] k={self.config.k}, block_size={self.config.block_size}"
        )

        bases = self.config.base_numbers()
        print(f"  Computing {len(bases)} base trajectories (m={self.config.max_m})...")

        for n0 in bases:
            log = compute_trajectory(n0, self.config.max_m, self.config.k)
            self.trajectory_logs.append(log)

        print(f"  Computing difference logs for selected pairs...")
        shifts = self.config.shift_offsets()

        count = 0
        for log_base in self.trajectory_logs[:4]:  # Sample a few for difference logs
            for m_shift in shifts:
                diff_log = compute_difference_log(log_base, m_shift, 0)
                self.difference_logs.append(diff_log)
                count += 1

        print(f"  Generated {count} difference logs")

    def compute_statistics(self) -> Dict:
        """Extract summary statistics from logs."""
        if not self.trajectory_logs:
            return {}

        stats = {
            "k": self.config.k,
            "block_size": self.config.block_size,
            "num_trajectories": len(self.trajectory_logs),
            "num_difference_logs": len(self.difference_logs),
            "log2_3": self.config.log2_3,
        }

        # Drift statistics
        drifts = [log.D_m for log in self.trajectory_logs]
        stats["drift_mean"] = float(np.mean(drifts))
        stats["drift_std"] = float(np.std(drifts))
        stats["drift_min"] = float(np.min(drifts))
        stats["drift_max"] = float(np.max(drifts))

        # Spike statistics (maximum prefix drift)
        max_prefix = [log.max_prefix_D for log in self.trajectory_logs]
        stats["max_prefix_D_mean"] = float(np.mean(max_prefix))
        stats["max_prefix_D_std"] = float(np.std(max_prefix))
        stats["max_prefix_D_min"] = float(np.min(max_prefix))
        stats["max_prefix_D_max"] = float(np.max(max_prefix))

        # First singularity index statistics
        first_singular_indices = []
        for log in self.trajectory_logs:
            for i, seg in enumerate(log.segments):
                if seg.s >= self.config.k:
                    first_singular_indices.append(i)
                    break

        if first_singular_indices:
            stats["first_singular_mean"] = float(np.mean(first_singular_indices))
            stats["first_singular_median"] = float(np.median(first_singular_indices))

        # Difference log: first delta index distribution
        first_deltas = []
        for diff_log in self.difference_logs:
            idx = diff_log.first_delta_index
            if idx is not None:
                first_deltas.append(idx)

        if first_deltas:
            stats["diff_first_delta_mean"] = float(np.mean(first_deltas))
            stats["diff_first_delta_median"] = float(np.median(first_deltas))
            stats["diff_first_delta_max"] = float(np.max(first_deltas))

        # Terrain statistics: v2(|Δn|) across all difference segments
        v2_values = []
        for diff_log in self.difference_logs:
            for seg in diff_log.segments:
                if seg.v2_delta_n is not None:
                    v2_values.append(seg.v2_delta_n)
        if v2_values:
            stats["v2_delta_n_mean"] = float(np.mean(v2_values))
            stats["v2_delta_n_std"] = float(np.std(v2_values))
            stats["v2_delta_n_min"] = float(np.min(v2_values))
            stats["v2_delta_n_max"] = float(np.max(v2_values))

        # Tau_r statistics (terrain collapse times)
        # Collect tau_r per difference log for r in {1,2,3,4,5,6}
        for r in [1, 2, 3, 4, 5, 6]:
            vals = []
            for diff_log in self.difference_logs:
                t = diff_log.tau_r.get(str(r)) if hasattr(diff_log, 'tau_r') else None
                if t is not None:
                    vals.append(t)
            if vals:
                stats[f"tau_{r}_mean"] = float(np.mean(vals))
                stats[f"tau_{r}_median"] = float(np.median(vals))
                stats[f"tau_{r}_min"] = float(np.min(vals))
                stats[f"tau_{r}_max"] = float(np.max(vals))

        # Correlation: max_prefix_D vs tau_4 (if available)
        # Join by n0: use the base trajectory's max_prefix_D
        base_by_n0 = {log.n0: log for log in self.trajectory_logs}
        pairs = []
        for diff_log in self.difference_logs:
            base = base_by_n0.get(diff_log.n0)
            if base is None:
                continue
            t4 = diff_log.tau_r.get('4') if hasattr(diff_log, 'tau_r') else None
            if t4 is None:
                continue
            pairs.append((base.max_prefix_D, t4))
        if len(pairs) >= 3:
            xs = np.array([p[0] for p in pairs], dtype=float)
            ys = np.array([p[1] for p in pairs], dtype=float)
            if np.std(xs) > 0 and np.std(ys) > 0:
                stats["corr_maxPrefix_tau4"] = float(np.corrcoef(xs, ys)[0, 1])

        return stats

    def save_results(self, output_dir: Path):
        """Save all logs and statistics to JSON files."""
        output_dir = Path(output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)

        # Save trajectory logs
        traj_file = output_dir / f"trajectories_k{self.config.k}.json"
        with open(traj_file, "w") as f:
            json.dump([log.to_dict() for log in self.trajectory_logs], f, indent=2)
        print(f"  Saved trajectory logs to {traj_file}")

        # Save difference logs
        diff_file = output_dir / f"differences_k{self.config.k}.json"
        with open(diff_file, "w") as f:
            json.dump(
                [diff_log.to_dict() for diff_log in self.difference_logs], f, indent=2
            )
        print(f"  Saved difference logs to {diff_file}")

        # Save statistics
        stats = self.compute_statistics()
        stats_file = output_dir / f"statistics_k{self.config.k}.json"
        with open(stats_file, "w") as f:
            json.dump(stats, f, indent=2)
        print(f"  Saved statistics to {stats_file}")


# ============================================================================
# CLI
# ============================================================================


def main():
    parser = argparse.ArgumentParser(
        description="CollatzCartography: Experimental observation framework"
    )
    parser.add_argument("--k", type=int, default=8, help="Block size exponent (2^k)")
    parser.add_argument(
        "--max-m", type=int, default=256, help="Maximum trajectory length"
    )
    parser.add_argument(
        "--num-bases", type=int, default=32, help="Number of base odd numbers to study"
    )
    parser.add_argument(
        "--output", type=str, default="results", help="Output directory for results"
    )

    args = parser.parse_args()

    config = ExperimentConfig(k=args.k, max_m=args.max_m, num_bases=args.num_bases)
    exp = CartographyExperiment(config)

    print("[CollatzCartography] Starting experiment...")
    exp.run()

    print("\n[Statistics]")
    stats = exp.compute_statistics()
    for key, val in stats.items():
        if isinstance(val, float):
            print(f"  {key}: {val:.6f}")
        else:
            print(f"  {key}: {val}")

    print(f"\n[Results] Saving to {args.output}...")
    exp.save_results(Path(args.output))
    print("[CollatzCartography] Done!")


if __name__ == "__main__":
    main()
