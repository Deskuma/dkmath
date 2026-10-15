# FLT7 — Kummer × GN bridge

Branch: `research/FLT7-Kummer-Anthropic-Bridge-261015-v0`  
Lean project: `lean/dk_math`  
Documentation: `lean/dk_math/docs/dev/FLT7-Kummer-Anthropic-Bridge-261015-v0`  
Status: **Gate 001 B accepted; Gate 002 A accepted; Gate 003 authorized; FLT7 OPEN**.

## Goal

Compare the native GN/GTail arithmetic with the cyclotomic Kummer mechanism
without invoking a completed external FLT theorem. The source of truth is
the checked-out GitHub repository. Anthropic comparison source:
[`P2M/Sol/S_flt_regular.lean`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_flt_regular.lean);
verify provenance/license before borrowing text.

## Established

- Gate 001 [review](review-001.md) / [matrix](bridge-matrix-001.md):
  cyclotomic PID and concrete degree-six ring equivalence already proved;
  chosen-factor extraction `Q = gamma^7` and `L = pi * gamma^7`
  already proved; old natural `q`-peel is not the same as an enlarged
  cyclotomic-integer descent state.
- Gate 002 [review](review-002.md) / [report](report-002.md):
  generic **scalar-congruent** units are seventh powers in the concrete
  degree-six ring. Proofs G1/G2/G3 in
  `DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicKummerUnit.lean`;
  their published axioms are `propext`, `Classical.choice`, `Quot.sound`.
- **Missing:** an actual next cyclotomic state with strictly smaller
  ramifier exponent (or a GN-derived contradiction). Conditional receivers
  do not count as a proof of FLT7.

## Current research direction

[Gate 003](instruction-003.md): ensure Gate-002 theorem is reached by
ordinary CI entrances; then audit the **same-source GN7 ↔ cyclotomic norm
↔ ramifier** identities. Avoid re-proving known endpoints. Do not claim
GN-derived FLT7 unless an additional restriction or descent is proven.

## Repository retention and verification policy

**CI is the final integration judge.** Codex may run local builds and
diagnostics, but must **not commit** build logs, console output,
`evidence/`, copied upstream files, generated inventories, or raw test
transcripts. Keep only new proof code, essential regression tests, and
short research documents recording the exact theorem or blocker plus
the nonstandard axiom status if any. No command histories, job counts,
failed-attempt narratives, or parallel-build prescriptions.
Run `#print axioms` locally for exported lemmas; summarize relevant
exceptions in at most one line. Do not relax mathematical trust checks.
Stop after each authorized gate for review.
