# CGE-002 report

## Scope

Implemented the balanced square-shell certification layer requested by
`instruction-002.md`.  The Cross-Gap generator degrees remain arbitrary; no
near-balanced survivor-existence theorem or Strong Goldbach theorem is added.

## Files

- Added `DkMath/NumberTheory/Goldbach/CrossGapSquareCertification.lean`.
- Added `DkMathTest/NumberTheory/GoldbachCrossGapSquareCertificationAudit.lean`.
- Updated `DkMath/NumberTheory/Goldbach.lean` to export the new module.

## Existing generic bridge

The generic theorem
`DkMath.NumberTheory.FixedBigGauge.prime_iff_supportDisjointFrom_in_squareShell`
already existed and was reused.  No duplicate generic square-shell theorem was
added.

## Production theorems

- `crossPairHeight`
- `CrossGapSquareCertified`
- `prime_pair_of_crossGapSquareCertified`
- `crossPair_lower_bounds_of_balanced_window`
- `crossPair_in_squareShell_of_balanced_window`
- `crossGapSquareCertified_of_balanced_window`
- `goldbachPairAt_of_crossGapSquareCertified`

`CrossGapSquareCertified` retains all six Cross-Gap coordinates and requires,
for one anchor `P`,

```text
P < CrossLeft ≤ squareBody P
P < CrossRight ≤ squareBody P
SupportDisjointFrom (primeScalesUpTo P) CrossLeft
SupportDisjointFrom (primeScalesUpTo P) CrossRight
```

The certification theorem has no restriction on `d₁` or `d₂`; degree two is
used only by the existing `squareBody` envelope.  The fixed-even-fiber bridge
uses CGE-000 conservation to return `GoldbachPairAt n`.

For a balanced window, `w ≤ n`, `CrossLeft ≤ n+w`, and
`CrossRight ≤ n+w` imply both endpoints are at least `n-w`.  Consequently,
`P < n-w` and `n+w ≤ squareBody P` transport both endpoints into the same
square shell.  This is a bounded certification-horizon statement, not a
complexity or existence claim.

## AKS firewall

`AKSBridge` was not imported or used.  The certification relies only on the
existing kernel-checked SquareBody/support-disjoint theorem because the current
AKS layer is not a complete primality converse.

## Regression

The audit includes both firewall examples: `25+27=52` is coprime but not a
prime pair, while `3+3=6` is a prime pair but not coprime.  A degree-one
Cross-Gap configuration produces `3` and `3`, is certified in the `P=2`
square shell, and closes to `GoldbachPairAt 3`.  The composite `9` firewall
shows that support disjointness from `primeScalesUpTo 3` fails.

## Verification

Focused build command:

```text
lake build DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachCrossGapSquareCertificationAudit
```

The focused build completed successfully with 8728 jobs, and the audit
`#print axioms` checks passed.  The axiom output contains no `sorryAx` and no
newly introduced axiom.

Facade build:

```text
lake build DkMath
```

The facade build completed successfully with 9851 jobs.  A fresh warning
filter found no warnings other than the repository's excluded
`declaration uses \`sorry\`` category.

The forbidden-construct grep over the added implementation and audit files
found no `sorry`, `admit`, `native_decide`, `unsafe`, or new `axiom`
declaration.

## Outcome

**Outcome A — LOCAL SQUARE CERTIFICATION GAIN.**

An arbitrary-degree Cross-Gap generator now has a production bridge into a
pair-local SquareBody certification horizon, including balanced-window
transport and the conditional Goldbach endpoint.  This is certification-side
progress only.  A provider proving that a survivor exists in every even fiber
remains unimplemented for the next stage.
