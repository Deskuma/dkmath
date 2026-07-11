# Petal implementation report cp-294

## Closed in this checkpoint

The finite-window boundary term is now closed under sorted-before.

- Added the sorted-list successor lemma:
  a witness with a later larger witness has an adjacent successor whose value
  is no larger than that later witness.
- Proved the unified finite-window boundary carrier is subsingleton.
- Proved:

```text
boundaryWitnesses.card <= 1
```

- Removed the unnecessary sortedness argument from the unresolved-left image
  bound.
- Combined the residue classification with the unresolved-pair and boundary
  bounds.

## Final unconditional inequalities

For a sorted witness list:

```text
positiveWitnesses.card
  <= (hi - lo) / 2 + 2 + unresolvedInternalPairFamily.card

positiveWitnesses.card
  <= nonposPositions.card + 1 + unresolvedInternalPairFamily.card
```

These are bundled as
`sourcePressurePositiveWitnesses_localBig_with_unresolvedInternal`.

## Internal coverage specialization

Under `SourcePressureCanonicalInternalPairCoverageInWindow`, the unresolved
internal family is empty.  The endpoint-corrected local-Big theorem is now:

```text
positiveWitnesses.card <= (hi - lo) / 2 + 2
positiveWitnesses.card <= nonposPositions.card + 1
```

Bundled as
`sourcePressurePositiveWitnesses_endpointCorrectedLocalBig_of_internalCoverage`.

## Interpretation

The finite-window accounting chain is now explicit:

```text
two-spaced canonical separators
  -> canonical pair density
  -> positive-center residue
  -> unresolved internal pairs + one maximal boundary witness
  -> endpoint-corrected local Big
```

The remaining mathematical question is producer-side: prove internal coverage
for every internal adjacent pair, or classify the exact local obstruction when
that coverage fails. No global convergence claim is made here.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

No new `sorry` or `axiom` was introduced.
