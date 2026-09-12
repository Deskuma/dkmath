# CPG-V1-003 — center and relative phase dynamics

Date: 2026-09-12  
Status: complete

## Implemented API

Extended the production module
[GoldbachPhase.lean](../../../DkMath/NumberTheory/PrimeGauge/GoldbachPhase.lean)
with:

```lean
DkMath.NumberTheory.PrimeGauge.goldbachGaugeMarkers_succ
DkMath.NumberTheory.PrimeGauge.goldbachGaugeRelativePhase
DkMath.NumberTheory.PrimeGauge.goldbachGaugeRelativePhase_eq_pow_two_mul
DkMath.NumberTheory.PrimeGauge.goldbachGaugeRelativePhase_eq_one_iff_dvd_two_center
DkMath.NumberTheory.PrimeGauge.goldbachGaugeRelativePhase_succ
```

`goldbachGaugeMarkers_succ` gives the center step `n → n + 1` for the left
marker and inverse right marker. The relative marker is defined as the left
marker times the inverse of the conjugate marker, and is proved equal to
`regularKernel r ^ (2 * n)`. For positive `r`, its return is equivalent to
`r ∣ 2 * n`. Its center successor is multiplication by the fixed phase
`regularKernel r ^ 2`.

The regression additions in
[PrimeGaugeGoldbachPhase.lean](../../../DkMathTest/NumberTheory/PrimeGaugeGoldbachPhase.lean)
check the marker successor, the double-center normal form, a non-returning
example at `r = 5`, and the successor law.

## Scope boundary and information classification

- The center/relative phase laws are finite group identities over the existing
  CF2D marker and exact-order provider.
- This checkpoint adds no new prime, Goldbach, CRT, capacity, survivor, or
  endpoint result.
- The observed content is a phase lift of the existing residue arithmetic; no
  strict information gain is claimed here. The final CPG-V1-007 audit remains
  mandatory before Projection or continuum work.
- Raw/proper obstruction and the `CPG-V1-004a` target-congruence prerequisite
  remain separate. The existing zero-target child theorem is not promoted to a
  paired Goldbach refinement by this checkpoint.

## Validation

Executed from `lean/dk_math`:

```bash
lake build DkMath.NumberTheory.PrimeGauge.GoldbachPhase \
  DkMathTest.NumberTheory.PrimeGaugeGoldbachPhase
```

Result: exit 0, `Build completed successfully (8701 jobs)`.

Additional checks on the fresh build log `/tmp/cpg-v1-003-build.log`:

- independent `warning:` scan: no matches;
- forbidden-construct scan of the two changed Lean files: no matches for
  `sorry`, `admit`, user `axiom`, `unsafe`, or `native_decide`;
- `#print axioms` for both new phase laws and the two existing bridge laws:
  only `propext`, `Classical.choice`, and `Quot.sound`.

The shell profile emitted an environment permission warning before Lake; the
Lean build itself completed without errors or warnings.

## Roadmap transition

`CPG-V1-003` is complete. The next checkpoint is `CPG-V1-004a`, which must
generalize the existing zero-target child observer to a prescribed target
congruence before any paired fresh-prime Goldbach refinement is attempted.

