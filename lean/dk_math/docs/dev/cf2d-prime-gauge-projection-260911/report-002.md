# CPG-V1-002 — Goldbach conjugate gauge bridge

Date: 2026-09-12  
Status: complete

## Implemented API

Added the thin production module
[GoldbachPhase.lean](../../../DkMath/NumberTheory/PrimeGauge/GoldbachPhase.lean):

```lean
DkMath.NumberTheory.PrimeGauge.goldbachGaugeMarker
DkMath.NumberTheory.PrimeGauge.goldbachGaugeConjugateMarker
DkMath.NumberTheory.PrimeGauge.goldbachLeftObstructed_iff_gauge_eq
DkMath.NumberTheory.PrimeGauge.goldbachRightObstructed_iff_gauge_eq_inv
```

The left theorem translates the existing raw `ZMod` equality for
`n - u` divisibility into equality of `regularKernel r ^ u` and
`regularKernel r ^ n`. It retains the required natural-subtraction hypothesis
`u ≤ n`.

The right theorem translates the existing raw `ZMod` negative-residue equality
for `n + u` divisibility into equality of the left marker and the inverse
(`conjugate`) center marker. Its finite phase calculation uses the
`u + n ≡ 0 [MOD r]` intermediate statement.

The module reuses the CPG-V1-001 return/congruence bridge and the existing
`Goldbach.PrimeWorld` residue theorems. It deliberately does not identify
proper endpoint obstruction with raw obstruction: endpoint filtering remains
outside this checkpoint.

Added the focused regression file
[PrimeGaugeGoldbachPhase.lean](../../../DkMathTest/NumberTheory/PrimeGaugeGoldbachPhase.lean).
It checks positive-modulus left/right examples, non-obstructed residues, and
the two phase bridge directions.

## Scope boundary

- This is a notation/observer bridge for existing finite residue semantics; it
  is not a new Goldbach existence result.
- No proper-obstruction theorem, paired fresh-prime refinement, center-motion
  law, Projection API, or continuum API was added.
- The marker uses the existing exact-order `regularKernel`; no primality of the
  modulus and no prime-existence claim is inferred.
- The bridge is not counted as strict information gain. The CPG-V1-007 audit
  must compare the later dynamic phase APIs against the existing CRT/capacity
  providers.

## Validation

Executed from `lean/dk_math`:

```bash
lake build DkMath.NumberTheory.PrimeGauge.GoldbachPhase \
  DkMathTest.NumberTheory.PrimeGaugeGoldbachPhase
```

Result: exit 0, `Build completed successfully (8701 jobs)`.

Additional checks on the fresh build log `/tmp/cpg-v1-002-build.log`:

- independent `warning:` scan: no matches;
- forbidden-construct scan of the two new Lean files: no matches for
  `sorry`, `admit`, user `axiom`, `unsafe`, or `native_decide`;
- `#print axioms` for both bridge theorems: only `propext`,
  `Classical.choice`, and `Quot.sound`.

The shell profile emitted an environment permission warning before Lake; the
Lean build itself completed without errors or warnings.

## Roadmap transition

`CPG-V1-002` is complete. The next checkpoint is `CPG-V1-003`, which will
formalize center motion and relative phase and first classify whether those
identities provide information beyond a static re-expression.

