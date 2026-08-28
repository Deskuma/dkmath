# PUU-L015 — Old-Escape Frontier Equivalence Audit

## Scope

PUU-L015 audits whether a global lower-bound/provider statement for
`successorOldBasisEscapingOffsets` would supply information independent of
Legendre's conjecture.  The checkpoint is an equivalence audit only.  It does
not prove the provider, a lower bound, a propagation theorem, or a new prime
existence result.

The formal implementation is
`DkMath/NumberTheory/Legendre/PrimorialWheelOldEscapeFrontier.lean`, exported
by `DkMath.NumberTheory.Legendre`.

## Formal results

The definition
`SuccessorOldEscapeCriterion n` has the exact branch semantics required by
PUU-L014:

* if `n + 1` is composite, one old-basis escape is required;
* if `n + 1` is prime and `n + 3` is composite, one old-basis escape is
  required;
* if both `n + 1` and `n + 3` are prime, at least two old-basis escapes are
  required, because the second threshold seat can be deleted.

For every `2 ≤ n`, the new criterion is proved equivalent to
`(escapingSquareOffsets (n + 1)).Nonempty`:

```lean
successorOldEscapeCriterion_iff_escapingSquareOffsets_nonempty
```

The proof reuses the PUU-L014 branch theorems and the projected/Legendre
identification.  It does not introduce a new existence assumption.

The same local statement is also proved in prime-witness form:

```lean
successorOldEscapeCriterion_iff_exists_prime_in_successor_squareCell
```

The auxiliary theorem
`escapingSquareOffsets_nonempty_iff_exists_prime_in_squareCell` makes the
existing square-offset/primality bridge explicit.

## Global anti-relabeling result

The global proposition

```lean
def SuccessorOldEscapeProvider : Prop :=
  ∀ n : ℕ, 2 ≤ n → SuccessorOldEscapeCriterion n
```

is proved equivalent to the prime-in-square-cell statement for every anchor
`m ≥ 3`:

```lean
successorOldEscapeProvider_iff_legendre_from_three
```

After the explicit anchors `m = 1` with witness `2` and `m = 2` with witness
`5`, the full equivalence is:

```lean
legendreConjecture_iff_successorOldEscapeProvider
```

The diagnostic corollaries record both directions.  In particular, a proof of
the global old-basis escape provider would already be a proof of Legendre's
conjecture.  Therefore the proposed provider is not a new provider; it is
Legendre's square-cell escape statement expressed through the old-escape
classification.

## Regressions

The implementation includes two concrete branch checks:

* `successorOldEscapeRegression_three_composite`: at `n = 3`, successor `4`
  is composite and the old and projected escape sets are equal;
* `successorOldEscapeRegression_four_twin`: at `n = 4`, successor `5` and the
  next odd threshold `7` are prime, old escape seat `10` is present, and it is
  absent from the projected escape set.  Thus actual escape in this branch
  requires another old escape.

## Boundary and next research step

This checkpoint does not prove `SuccessorOldEscapeProvider`, any cardinality
lower bound for `successorOldBasisEscapingOffsets`, Jacobsthal or max-gap
bounds, square-hole propagation, prime density, PowerSwap, GN/CosmicFormula,
or RH.

To obtain genuinely new progress, the next theorem must be an independent
wheel-geometry or square-anchor-orbit invariant that implies the local
criterion without assuming, or merely renaming, square-shell escape.  A
global old-escape lower bound by itself cannot serve as that independent
provider after this audit.

## Verification

The focused module build succeeded:

```text
lake build DkMath.NumberTheory.Legendre.PrimorialWheelOldEscapeFrontier
```
