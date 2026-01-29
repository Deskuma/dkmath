# Collatz Cartography: 2026 Research Framework

**Date**: 2026年1月30日  
**Authors**: D. and Wise Wolf  
**License**: MIT  

---

## Overview

This document describes the integrated research framework for the accelerated Collatz conjecture, combining formal Lean verification with experimental Python observation. The goal is to understand the "petal structure" at scale $2^k$ and extract boundary conditions that distinguish between convergent and divergent behaviors.

### Core Insight: Petal Conservation

The central mathematical insight is:

> **If $v_2(3n+1) < k$, then shifting $n$ by a block of size $2^k$ does not change $v_2(3n'+1)$.**

This "petal conservation" law means that anomalies (points where $v_2(3n+1) \geq k$) form localized filaments — the singular structure we're mapping.

---

## 1. Lean Formalization Layer

### 1.1 Module Structure

```
DkMath/Collatz/
├── Basic.lean        # Core definitions: C(n), T(n), OddNat, s(n)
├── V2.lean           # 2-adic valuation: v₂(a), v₂Spec
├── Shift.lean        # Block shift and petal conservation theorem
└── Collatz2K26.lean  # Main integration module
```

### 1.2 Basic Definitions (Basic.lean)

**Collatz Map:**
$$C(n) = \begin{cases} n/2 & \text{if } 2 | n \\ 3n+1 & \text{otherwise} \end{cases}$$

**Accelerated Collatz Map** (on odd naturals):
$$T(n) = \frac{3n+1}{2^{v_2(3n+1)}}$$

**Observation Function:**
$$s(n) := v_2(3n+1)$$

where $v_2(a)$ is the highest power of 2 dividing $a$.

**Partial Sums and Drift:**
$$S_m(n) = \sum_{i=0}^{m-1} s(T^i(n))$$
$$D_m(n) = m \log_2(3) - S_m(n)$$

### 1.3 2-adic Valuation (V2.lean)

**Specification:**
$$v_2\text{Spec}(a, s) :\Leftrightarrow 2^s | a \land 2^{s+1} \nmid a$$

**Definition:**
The function `v2` returns the unique $s$ satisfying $v_2\text{Spec}(a, s)$.

**Key Lemmas:**

- `v2_odd`: For odd $a$, $v_2(a) = 0$
- `v2_even`: For even $a$, $v_2(a) > 0$
- `v2_mul`: $v_2(ab) = v_2(a) + v_2(b)$ (multiplicative)
- `v2_3n_plus_1_ge_1`: For odd $n$, $v_2(3n+1) \geq 1$

### 1.4 Block Shift and Petal Conservation (Shift.lean)

**Definition:**
$$\text{shift}(k, m, n) = n + 2^k \cdot m$$

**Central Theorem (Petal Conservation):**

```lean
theorem v2_shift_invariant
  (k m n : ℕ)
  (hn : n % 2 = 1)
  (hk : v2 (3*n + 1) < k) :
  v2 (3 * (shift k m n) + 1) = v2 (3*n + 1)
```

**Interpretation:**

- When $v_2(3n+1) < k$, the "petal" is small enough that it doesn't interact with the block boundary.
- Shifting by a full block size $2^k$ preserves the observation value.
- Differences between shifted and unshifted trajectories can only arise at "singular" positions where $v_2 \geq k$.

---

## 2. Python Experimental Framework

### 2.1 Core Module: `collatz_experiment.py`

A comprehensive Python framework for:

1. Computing trajectories with full logging
2. Generating difference logs for block comparisons
3. Computing statistics and extracting boundary conditions

### 2.2 Log Types

#### Trajectory Log (TrajactoryLog)

For a starting odd $n_0$, record $m$ steps of the accelerated Collatz map:

```python
@dataclass
class TrajectorySegment:
    step: int       # Step number
    n: int          # Current odd natural
    a: int          # 3n + 1
    s: int          # v₂(a)
    n_next: int     # T(n) = a / 2^s
```

**Computed quantities:**

- $S_m = \sum_i s_i$ (total observation)
- $D_m = m \log_2(3) - S_m$ (drift)

#### Difference Log (DifferenceLog)

Compare trajectory from $n$ with trajectory from $n' = n + 2^k \cdot m_{\text{shift}}$:

```python
@dataclass
class DifferenceSegment:
    step: int
    delta_s: int             # s(n'_i) - s(n_i)
    singular_at_base: bool   # s(n) >= k
```

**Key metrics:**

- `first_delta_index`: First step where $\Delta s_i \neq 0$ (first divergence point)
- `singular_indices`: Steps where base trajectory is at/above singularity threshold

### 2.3 Experiment Configuration

```python
class ExperimentConfig:
    k: int           # Block size exponent (2^k)
    max_m: int       # Trajectory length
    num_bases: int   # How many base odd numbers to test
```

### 2.4 Running Experiments

**Example: k = 8 (block size 256)**

```bash
python3 collatz_experiment.py --k 8 --max-m 256 --num-bases 32 --output results/
```

**Output:**

- `trajectories_k8.json`: All trajectory logs
- `differences_k8.json`: Difference logs for selected pairs
- `statistics_k8.json`: Summary statistics

---

## 3. Experimental Results (k = 8)

### 3.1 Summary Statistics

| Metric | Value |
|--------|-------|
| Block size | 256 |
| Number of trajectories | 32 |
| Number of difference logs | 60 |
| $\log_2(3)$ | 1.584963 |
| **Drift mean** | -5.196 |
| **Drift std** | 1.400 |
| **Drift range** | [-6.602, -0.415] |

### 3.2 Singularity Observations

- **First difference index (mean)**: 4.0 steps
- **First difference index (median)**: 4.0 steps
- **First difference index (max)**: 4.0 steps

**Interpretation:**
In the tested block comparisons, shifts begin to show observable differences around step 4, suggesting a characteristic "induction length" for the block size $2^8$.

### 3.3 Drift Characteristics

The drift $D_m$ is consistently negative over the observed range:

- **Mean drift**: $\approx -5.2$ (slight systematic decrease)
- **Variability**: $\sigma \approx 1.4$ (moderate spread across initial conditions)
- **Range**: Spans about 6.2 units across all tested trajectories

This negative drift indicates that, on average, the sum $S_m$ grows faster than expected from pure geometric scaling at rate $\log_2(3)$, suggesting that the Collatz dynamics includes mechanisms that amplify $v_2$ beyond the geometric baseline.

---

## 4. Next Steps in the Investigation

### 4.1 Phase I: Refine the Cartography

1. **Extend $k$ range:** Repeat experiments for $k \in \{6, 7, 8, 9, 10\}$
2. **Analyze singularity distributions:**
   - Heatmaps: horizontal = $n \bmod 2^k$, vertical = $j$ (block index), color = first singularity position
   - Expected pattern: Vertical lines (filaments) where $v_2 \geq k$ starting point
3. **Study boundary effects:**
   - Scan $\max_{t \leq m} D_t(n)$ as a function of initial conditions
   - Identify thresholds that separate "stable" from "divergent" phases

### 4.2 Phase II: Extract Boundary Inequalities

From Python experiments, infer candidates for:
$$\Phi(n, k) := \text{(condition distinguishing stable from unstable)}$$

Examples:

- $v_2(3n+1) \geq k$ (already formalized in Lean)
- Maximum drift before iteration $i_0$: $\max_{t \leq i_0} D_t > B_0(k)$
- Cumulative singularity burden: $\#\{i < m : v_2(T^i(n)) \geq k\}$

### 4.3 Phase III: Formalize in Lean

Once candidates are identified from Python:

1. Define the boundary proposition formally in Lean
2. State it as a theorem with assumptions on $n$, $k$, etc.
3. Prove or assume the necessary supporting lemmas
4. Use it to reason about convergence guarantees

---

## 5. Code Organization and Workflow

### 5.1 Lean Files

| File | Purpose | Status |
|------|---------|--------|
| `Basic.lean` | Core definitions (C, T, OddNat) | ✓ Complete (skeleton) |
| `V2.lean` | 2-adic valuation and lemmas | ✓ Complete (spec + stubs) |
| `Shift.lean` | Petal conservation theorem | ✓ Complete (main theorem + stubs) |
| `Collatz2K26.lean` | Integration and higher-level results | ✓ In progress |

### 5.2 Python Files

| File | Purpose | Status |
|------|---------|--------|
| `collatz_experiment.py` | Main experimental framework | ✓ Complete |
| (Future) `analyze_heatmaps.py` | Visualization and filament analysis | ⧗ Planned |
| (Future) `extract_boundaries.py` | Automated boundary candidate extraction | ⧗ Planned |

### 5.3 Documentation

| File | Purpose | Status |
|------|---------|--------|
| `docs/CollatzCartography.md` | This file | ✓ In progress |
| `theorem_picker.md` | Theorem candidates from earlier phases | ✓ Existing |
| `__Theorems.md` | Formalized theorem statements | ⧗ To be updated |

---

## 6. Mathematical Notation Reference

| Symbol | Meaning |
|--------|---------|
| $v_2(a)$ | 2-adic valuation of $a$ (highest power of 2 dividing $a$) |
| $C(n)$ | Standard Collatz map |
| $T(n)$ | Accelerated Collatz map (odd $n$ → odd $(3n+1)/2^{v_2(3n+1)}$) |
| $s(n)$ | Observation function $= v_2(3n+1)$ |
| $S_m(n)$ | Partial sum $= \sum_{i=0}^{m-1} s(T^i(n))$ |
| $D_m(n)$ | Drift $= m \log_2(3) - S_m(n)$ |
| $\text{shift}(k, m, n)$ | Block shift $= n + 2^k m$ |
| $\text{OddNat}$ | Type of odd natural numbers |

---

## 7. References and Related Work

- **Collatz Conjecture**: Lagarias, J. C. (1985). "The 3x+1 problem and its generalizations."
- **p-adic methods**: Motivated by classical work in arithmetic dynamics.
- **Lean/Mathlib**: Formal verification framework (<https://lean-lang.org/>).
- **This project**: Building a bridge between formal verification (Lean) and experimental observation (Python).

---

## Appendix: Running the Full Workflow

### Quick Start

```bash
cd /home/deskuma/develop/lean/dkmath/lean/dk_math

# 1. Run Python experiments
python3 collatz_experiment.py --k 8 --max-m 256 --num-bases 32 --output results/

# 2. Build Lean project (skeleton definitions are complete)
lake build

# 3. (Future) Analyze results
python3 analyze_heatmaps.py --input results/trajectories_k8.json --output results/heatmaps.png
```

### Expected Outputs

```
results/
├── trajectories_k8.json      # Full trajectory logs
├── differences_k8.json       # Block comparison logs
├── statistics_k8.json        # Summary statistics
└── (future) heatmaps.png     # Visualization of singularity filaments
```

---

**End of Document**

Last updated: 2026年1月30日
