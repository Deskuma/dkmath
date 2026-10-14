# Review 016 — Outcome A accepted; permutation-prime image mechanism and source boundary

Date: 2026-10-14
Research branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewed implementation HEAD: `470b1b9e45220429567a75635921a00cd59f3bf5`

## Verdict: ACCEPTED — Outcome A

Reviewed the **actual** GitHub production
`DkMath/FLT/Seven/SevenRamifiedFusionPermutationPrimeSupport.lean`,
DkMathTest source, `report-016.md`, `findings-016.md` and
`evidence/016-verification-summary.md`.

Five new public results:

1. `centeredSevenSextic_cast_difference` proves in any CommRing R,
   for the *actual* sextic F, the cast identity
   `(q+D)^7-(q-D)^7 = 2*D*F(D,q)`.
   Ring subtraction (not truncated Nat subtraction) is used.
2. `zmod_seventh_power_injective` proves that for prime ℓ,
   `Nat.Coprime 7 (ℓ-1)` forces seventh-power injectivity on **all**
   `ZMod ℓ`, by `Nat.Coprime.pow_left_bijective` for the unit group,
   `ZMod.card_units` and a separate zero branch.
3. `centeredSevenSextic_not_dvd_of_seven_power_permutation`:
   for odd prime ℓ satisfying that coprimality, `ℓ∤D` implies
   `ℓ∤F(D,q)` for arbitrary D,q.
4. `nestedAllocation_excluded_of_permutation_prime_support`:
   with explicit `ℓ≠2,7`, `ℓ∤r` and `ℓ|(M/r)`, the SAME selected
   divisor's exact GN/RHS receiver is impossible; fixed gap
   `D=7^27*r^49` and target `448*(M/r)^49` are preserved.
5. `sixthPowerSieved_smallCoefficient_permutation_prime_excluded`:
   prime ℓ as above, `c≤343, n>0` imply
   `¬ SixthPowerSievedNestedCondition (c*ℓ^n)` by the
   kernel-checked gate-015 quotient-support bridge and the
   just-proved receiver consumer.

The tests cover odd positive cases ℓ=11 and ℓ=13,
the unrestricted-prime counterexample `29|F(1,5)`,
characteristic-two counterexample `F(1,1)=64`,
and the gap-specific failure of `ℓ∤D` at ℓ=7.
Modular polynomial zero is **not** an exact endpoint witness.

Codex-reported focused Lake build exited 0 (9090 jobs),
DkMathTest exited 0, and the five exports plus three
named tests have only standard axioms
`[propext, Classical.choice, Quot.sound]` or their
subset. No `sorryAx`. Reviewer inspected source and
evidence but **did not independently rerun Lean**.

## Research interpretation and the open logical direction

The source-independent exact receiver has now been
excluded on substantial finite and infinite classes of
abstract natural cores. This does **not** mean that an
actual `RamifiedSignedRootRoutingPacket p` has a core of
that form. It also does not mean bare p entails the
reconstruction obligation.

A fresh check of the actual source definitions found:

- `internalDepthFourSeventhCore p` is the natAbs of the
  norm packet's preexisting inner root;
  bare p yields `core>0` and `¬7|core`.
- `internalDepthFourReconstruction_iff_sixth_power_sieved p`
  supplies an **equivalence** between reconstruction obligation
  and an exact receiver at that chosen core; equivalence
  alone gives existence of neither side.
- `internalDepthFourReconstruction_iff_finiteCharts p`
  supplies a second equivalence with finite additive chart
  existence. The chart is **not** obtained from p alone.
- `internalDepthFourSummand_nested_normal_form` constructs
  r,s,u-dependent scalar normal form only from an
  **additional** `CounterexamplePack u (carrier p) v`.
  This hypothesis cannot be dropped just because p exists.
- Actual source real-pair/load results give ring-valued
  associated seventh powers, coprimality and gcd loads,
  not an automatically oriented natural endpoint.
  `internalDepthFourReconstructedRoute_root_ne_innerRoot`
  explicitly forbids reusing the old inner root as the
  supposed new away root.

Thus a source-side proof cannot equate the ring-normalized
axis, `quotientRoot`, real-pair loads, or orientation phase
with the exact chart's `u/r/s/q` without a new theorem.
See `source-coupling-map-005.md`; its failure boundary
remains intact after gate 016.

## Next: a deliberately narrow source-indexed gate 017

The new general sieve permits a sound **conditional**
source-indexed theorem: *if* a packet admits reconstruction,
its core cannot equal `c*ℓ^n` with c≤343,n>0 and the
permutation-prime hypotheses. Conversely, under an
explicit equality for the packet's **actual core**, one
can rule out reconstruction and finite charts.
This is a useful formal transport, but is not a new
unconditional condition on bare p.

Authorize `instruction-017.md` to implement that thin,
audited receiver-to-source transport and do a bounded
same-packet provenance audit identifying the **first
missing constructive implication**:
bare packet → existing finite additive chart, or
bare packet → sufficiently strong restriction on its
*actual* core. Produce a precise dependency/negative
evidence statement if no source-side bridge is derivable;
do **not** fabricate an equality or existence certificate.

After 017, decide whether to seek the phase-aware,
natural-endpoint extraction or independent intrinsic
core arithmetic, based on actual proof inventory,
rather than returning to arbitrary new moduli.

Codex implements/verifies/reports only. **No staging,
commit, push, branch creation, PR or merge.** Logs
transient; evidence compact and provenance marked.
