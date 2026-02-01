# Collatz Cartography  

— Block Self-Similarity (“Petals”) and Singular Ridges in the Accelerated Collatz Map —

> This document is a design note for a numerical-verification program that views the Collatz dynamics through **geometric–self-similar blocks** of size \(2^k\) (“petals”).  
> The goal is to **map where differences actually arise** under block offsets, identify **singular ridges**, and extract **inequality-style boundary conditions** that separate “contained / convergent-looking” behavior from “spiky / jumpy” behavior.

---

## 0. Goal (What are we trying to achieve?)

Before chasing a full proof, this project aims to fix and observe the *structural* claims that make the “petal” picture meaningful:

1. **Block (petal) invariance**  
   Under an offset \(+2^k m\), how long does the dynamics remain effectively “the same” inside a block?

2. **Where do differences actually originate?**  
   When two offset trajectories diverge, *where* does the divergence first appear?

3. **Quantify “spikes” (bad cases) as measurable terrain**  
   Capture “bad cases” as *density / ridges inside blocks*, not just isolated outliers.

---

## 1. Worldview: the Petal Model (Block Self-Similarity)

Fix a block exponent \(k\) and define the block size

\[
B := 2^k.
\]

Think of the natural numbers as tiled by blocks (petals):

- \([0,B), [B,2B), [2B,3B), \dots\)

The guiding intuition:

- Many features repeat across scales (self-similarity),
- Differences under offsets tend to **activate near boundaries / singular events**.

---

## 2. Accelerated Collatz on Odd Integers (Observation System)

Work on odd integers only. Define the accelerated Collatz map

\[
T(n) := \frac{3n+1}{2^{v_2(3n+1)}} \quad (\text{always odd}),
\]

and the observation function

\[
s(n) := v_2(3n+1),
\]

where \(v_2(x)\) is the 2-adic valuation (the exponent of 2 dividing \(x\)).

---

## 3. Drift (A Proxy for “How High It Spikes”)

Define the partial sum

\[
S_m := \sum_{i=0}^{m-1} s(T^i(n)),
\]

and the drift

\[
D_m := m\log_2 3 - S_m.
\]

The key quantity is not the final \(D_m\), but the **maximum prefix drift**

\[
\max_{t\le m} D_t,
\]

which we interpret as “the maximum spike inside the observation window.”

---

## 4. Block Offset Comparison (Petal-to-Petal Comparison)

Fix \(k\). For a base odd integer \(n_0\), compare it against

\[
n_0' := n_0 + 2^k\cdot m
\]

for various shift multipliers \(m\).

### 4.1 Difference in the valuation signal

Define

\[
\Delta s_t := s(n_t') - s(n_t).
\]

The **first time the signal differs** is

\[
\mathrm{first\_delta} := \min\{t \mid \Delta s_t \ne 0\}.
\]

### 4.2 Terrain signal: the 2-power structure of the offset

Define

\[
\Delta n_t := n_t' - n_t,\qquad v_2(|\Delta n_t|).
\]

This is the “petal terrain”: how strongly the offset remains aligned in 2-power terms as time evolves.

At \(t=0\),

\[
\Delta n_0 = 2^k m \Rightarrow v_2(\Delta n_0)=k+v_2(m),
\]

but as dynamics proceed, the nonlinear map tends to erode this alignment—possibly in a structured way.

---

## 5. Core Hypotheses (Working Theory)

> These are **working hypotheses**, not truths. The point is to test them.

### H1. Invariance in the non-singular region

For many points, \(\Delta s_t=0\) persists for a while; offsets do not immediately matter.

### H2. Singular ridges trigger divergence

Differences activate preferentially near indices where

\[
s(n)=v_2(3n+1)\ge k.
\]

These are the “singular ridges” (or “singular spine”) relative to block size \(2^k\).

### H3. Spikes are governed by max-prefix behavior

The key spike diagnostic is \(\max_{t\le m} D_t\), not the terminal drift.

### H4. Boundaries appear as ridges, not single points

Bad behavior likely forms *bands / ridges* (dense regions) rather than rare isolated outliers.

---

## 6. Implementation (Python Experiment)

The experimental instrument is `collatz_experiment.py`.

### 6.1 Outputs

- `trajectories_k{k}.json`  
  Per-base trajectory logs: \((n,a=3n+1,s,n_{\text{next}})\), plus \(S_m\), \(D_m\), and `max_prefix_D`.

- `differences_k{k}.json`  
  Pairwise comparison logs for base vs offset: \(\Delta s_t\), `first_delta_index`, \(\Delta n_t\), and \(v_2(|\Delta n_t|)\).

- `statistics_k{k}.json`  
  Aggregate statistics: means / maxima / minima / standard deviations for drift, spikes, and terrain.

### 6.2 Observation window note

`first_delta_index = null` does **not** mean “no difference forever.”  
It means **no difference within the finite observation window** (finite steps).

---

## 7. Lean Formalization (Fixing the Skeleton)

The Python experiment is observation; the Lean side fixes the structural skeleton so that the observation is meaningful.

Example fixed facts (informal summary):

- Basic “peel off a factor of 2” behavior for \(v_2\),
- \(v_2(2x)=1+v_2(x)\),
- A key block-shift invariance statement:
  under suitable non-singularity conditions, shifting by \(+2^k m\) preserves the relevant \(v_2\) behavior.
  (In other words: **differences are forced to concentrate around the singular ridges**.)

---

## 8. Experiment Plan (What to run next)

### 8.1 Scale sweep (self-similarity check)

Run for

\[
k\in\{6,8,10,12\}
\]

and compare distributions across scales.

### 8.2 Increase samples

- Increase base points \(n_0\) (thousands to tens of thousands),
- Increase shift multipliers \(m\) (wider range).

### 8.3 Ridge extraction metrics (make boundaries visible)

Add and analyze:

- Terrain break time  
  \[
  \tau_r := \min\{t : v_2(\Delta n_t) < r\}
  \]
  for thresholds \(r\) such as \(k, k-1, k-2\).

- Correlations:
  - `max_prefix_D` vs \(\tau_r\),
  - `min_delta_s` (negative direction) vs spike magnitude,
  - density of singular indices \(\#\{t\le m: s(n_t)\ge k\}\).

---

## 9. Toward Inequality-Style Boundary Conditions

A long-term goal is to turn “ridges” into inequality candidates, e.g.:

- A sufficient condition for “contained / not-too-spiky” behavior (empirical → conjectural):
  \[
  \max_{t\le m} D_t \le C \Rightarrow \text{(no large spike up to time \(m\))}
  \]

- A necessary condition for divergence activation:
  \[
  \exists t\le m,\ s(n_t)\ge k \Rightarrow \text{(offset differences become likely)}
  \]

At this stage we prioritize finding **statistically strong conditions** before attempting proof.

---

## 10. Current Status

- ✅ Lean skeleton: key invariance and valuation lemmas fixed (no project-specific axioms).
- ✅ Python instrument: trajectories, differences, and statistics exported as JSON.
- ✅ Expanded stats:
  - `max_prefix_D` (spike measure),
  - `v2_delta_n` (petal terrain),
  - signed difference metrics (`min_delta_s`, `max_abs_delta_s`, `sum_delta_s`).

- ⏳ Next: scale sweep and sample growth to determine whether the boundary is a sharp “line” or a broad “ridge.”

---

## Appendix A. Terminology

- **Petal / block**: an interval of size \(2^k\).
- **Singular ridge**: indices where \(s(n)=v_2(3n+1)\ge k\) relative to block size \(2^k\).
- **Terrain**: the evolution of \(v_2(|\Delta n_t|)\), describing how offset alignment erodes.
- **Spike (max-prefix)**: \(\max_{t\le m} D_t\), a proxy for maximum upward excursion.
