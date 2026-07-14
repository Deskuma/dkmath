# Petal implementation report cp-291

## Scope

This checkpoint converts canonical-pair packing into positive-center counting
without turning the existing existential state producers into an unsupported
global coverage claim.

## Implemented

- `sourcePressurePositiveWitnessesInWindow` selects the explicit in-window
  local-island witnesses supplied by `L`.
- `sourcePressureCanonicalLeftWitnessesInWindow` is the left-endpoint image of
  the canonical adjacent-pair family.
- Center-margin positivity is exposed directly from the witness property.
- Recursive adjacent-pair addresses are connected to `L.zip L.tail`.
- Under sorted-before, one left endpoint has at most one immediate right
  endpoint.  The sortedness hypothesis is necessary because arbitrary lists
  may repeat the same witness.
- Projection by `Prod.fst` is injective on the sorted canonical family, giving
  equality between canonical-left and canonical-pair cardinalities.

## Conditional complete coverage

Under `SourcePressureCanonicalLeftCoverageInWindow`, the implementation proves:

```text
positiveWitnesses.card <= (hi - lo) / 2 + 1
positiveWitnesses.card <= nonposPositions.card
```

The two inequalities are also bundled as
`sourcePressurePositiveWitnesses_localBig_of_coverage`.

## Unconditional residue decomposition

`sourcePressurePositiveCoverageResidue` records positive witnesses not yet
certified as canonical left endpoints.  Without any complete-coverage premise:

```text
positiveWitnesses.card
  <= canonicalPairFamily.card + residue.card

positiveWitnesses.card
  <= (hi - lo) / 2 + 1 + residue.card

positiveWitnesses.card
  <= nonposPositions.card + residue.card
```

This is the currently justified all-positive local-Big surface.

## Phase E result

The preferred `residue.card <= 1` theorem does not follow from the current
constructors.  `BeamSeed`, `SortedFailure`, and `FailureResolution` select an
existential diagnosed pair.  They do not certify every member of
`L.zip L.tail`.

The exact missing contract is now represented in Lean as:

```text
SourcePressureCanonicalNonterminalPairCoverageInWindow L lo hi
```

It requires every addressed in-window nonterminal pair to carry
`SourcePressureCanonicalFiniteWindowPackingState`.  A projection theorem shows
that this contract certifies each addressed nonterminal left endpoint.

No endpoint-corrected `+ 1` theorem was asserted.  Doing so before producing
this universal pair contract would incorrectly strengthen local existential
diagnosis into whole-list coverage.

## Established route

```text
canonical separator two-spacing
  -> canonical pair density
  -> canonical left-center density
  -> conditional all-positive density
  -> unconditional positive coverage residue
  -> residue-corrected local Big
```

## Next implementation

Construct a list-recursive classifier that proves
`SourcePressureCanonicalNonterminalPairCoverageInWindow`, or weakens it to an
explicit unresolved-pair Finset.  The latter would refine `residue.card` into
`terminal boundary + unresolved pair states` without claiming that the
unresolved family is empty.
