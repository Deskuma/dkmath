# FLT7TC-005R39 — C=1 ideal scalarization and unit-only twisted reduction

## Scope

This report records the R39 implementation and verification.  The checkpoint
starts from the R37 canonical `C,U,V` packet and targets only the `C = 1`
branch: scalar principal ideals, model-level units, the unit-only square-twist
identity, and the first theta-adic audit.  It does not claim a successor,
descent, or FLT7 closure.

## Initial investigation

- `PrimeTraceOneDirectRealCubicSquareIdealSupport.lean` already supplies the
  principal-ideal norm bridge and the square-root ideal product/coprimality
  APIs.
- `PrimeTraceOneDirectRealCubicPrimeAllocation.lean` supplies the exact
  product identity for the two square-root ideals.
- The canonical packet supplies `c_eq_gcd`, `c_dvd_a`, `unitPart_eq`, the
  coprimality of `u,v`, and the `c=1` norm equalities.
- `PrimeTraceOneDirectRealCubicSquareTwistObstruction.lean` supplies the
  square-twisted three-term identity, coefficient transport, and coefficient
  projective classes.

## Implementation

The focused production module
`PrimeTraceOneDirectRealCubicTrivialCommonFactor.lean` now provides:

- scalar principal ideals `scalarIdealU` and `scalarIdealV`, with absolute
  norms `U^3` and `V^3`;
- the neutral Dedekind-domain lemma
  `Nat.Coprime (Ideal.absNorm I) (Ideal.absNorm J) -> IsCoprime I J` for
  non-bottom ideals;
- the two cross-coprimality statements between the square-root ideals and the
  opposite scalar ideals;
- the product identity obtained from `unitPart_eq` at `c = 1`, followed by
  ideal-monoid Euclid cancellation;
- the ideal equalities `(r) = (U)` and `(s) = (V)`;
- model-level units `eta` and `xi` with `r = eta * U` and `s = xi * V`;
- rotation transport for the gap scalarization and the unit-only twisted
  seventh-power-square equation.

The cancellation proof uses divisibility orientations explicitly and concludes
ideal equality through `Ideal.dvd_iff_le` and antisymmetry. It does not infer
ideal equality from equal norms alone. The unit-only theorem retains the
`c = 1` hypothesis in its interface, while its body only needs the canonical
packet and the scalarized gap equation.

The public facade `DkMath.FLT.Seven` imports the module. Focused API and axiom
audit files were added for all public R39 declarations.

## Part I theta calibration

The R39 scratch file adds `r39_theta_coordinates_cancel`. From the checked
unit-only equation it applies the existing theta residue, linear, and square
coordinate definitions and proves all three exact cancellations:

```text
thetaResidue term0 + thetaResidue term1 + thetaResidue term2 = 0
thetaLinearModSeven term0 + thetaLinearModSeven term1 + thetaLinearModSeven term2 = 0
thetaSquareModSeven term0 + thetaSquareModSeven term1 + thetaSquareModSeven term2 = 0
```

The proof uses the ring-hom additive law for `thetaResidue` and locally
kernel-checks additivity of the two coordinate forms. No noncancellation was
found, so the current `projectiveLog/theta^3` surface is exhausted for this
equation. The next C=1 frontier is a deeper theta/7-adic coefficient.

The repository scan found mod-49/depth results for the separately normalized
cyclotomic root packet and terminal ramified packets, but no checked
current-provenance bridge whose hypotheses consume this R39 unit-only
equation. No historical terminal import or new mod-49 theory was added.

## Validation

The following sequential checks passed:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactor
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorAxiom
lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorR39Scratch.lean
```

The target production, facade, API, Axiom, and scratch outputs had no new
non-`sorry` warnings. The production warning cleanup removed the unused `hc`
warning by naming it `_hc` and documented the local heartbeat increase. The
Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound` for
the public R39 theorem chain and the scratch theta-cancellation theorem; no
`sorryAx` occurs in the R39 declarations.

Forbidden-source scans found no `sorry`, `sorryAx`, `admit`, `unsafe`, or
project `axiom` in the decisive production/test sources. `git diff --check`
also passes.

## Report questions and outcome

1. Yes: norm-coprime-to-ideal-coprime is checked in the current Dedekind
   domain setting.
2. Yes: scalar and square-root ideal norms are `U^3` and `V^3`.
3. Yes: both cross-coprimality statements are proved.
4. Yes: the product identity rewrites `a = U*V` explicitly.
5. Yes: Euclid cancellation proves both scalar ideal equalities.
6. Yes: model-level `eta` and `xi` are extracted with the requested
   orientations.
7. Yes: the R27 identity is reduced to the unit-only three-term
   seventh-power-square equation.
8. Yes: all three existing mod-7 theta coordinates cancel exactly.
9. No applicable current-provenance mod-49/depth bridge was found.
10. No contradiction arose.

Outcome: **B** — ideal and element scalarization plus the unit-only equation
are green, while the existing theta-cubed data cancels and a deeper local
invariant is required. The work stops at this boundary; no successor,
descent, or FLT7 conclusion is claimed.
