# TRM-005 report: uniform piece exchange / boundary forbidden deltas

Date: 2026-09-25
Branch: `research/Tromino-ExchangeCalculus-260924-v0`

## Scope

The state-only piece exchange and boundary-contact calculus is complete. The
implementation imports `State`, `Exchange`, and `ExchangeRescue` only; it does
not import `CosmicBridge` or `Restoration`, and it introduces no planar
geometry, MacroCell, BoundaryIR, graph search, optimization, or Four Color
formalization.

## Uniform exchange

`DkMath.Tromino.PieceExchange` defines:

```lean
uniformExchange (delta : TrominoState) (c : I → TrominoState) (i : I)
```

The theorems `uniformExchange_eq_iff` and `uniformExchange_ne_iff` show that a
common exchange delta preserves equality and inequality between indexed
states. The proof uses additive cancellation in `TrominoState`.

## Boundary contacts and forbidden deltas

`BoundaryContact` contains only an `inside` and an `outside` state. For a
contact, the forbidden delta is:

```lean
forbiddenDelta contact = contact.inside + contact.outside
```

`exchange_eq_contact_iff` proves that this is exactly the unique delta for
which the exchanged inside state equals the outside state. The uniqueness is
also exposed as `existsUnique_forbiddenDelta`, and
`forbiddenDelta_eq_zero_iff` identifies zero as forbidden exactly when the
contact is already conflicting.

For a finite contact set, `forbiddenExchangeSet` is the image of the contact
set under `forbiddenDelta`. Its membership theorem is
`mem_forbiddenExchangeSet_iff`; duplicate contacts with the same forbidden
delta therefore contribute only one forbidden state.

## Compatibility and rescue

`boundaryCompatible delta contacts` means that every recorded contact avoids
the exchanged equality. The bridge theorem
`boundaryCompatible_iff_not_mem` identifies this predicate with avoidance of
`forbiddenExchangeSet`. `compatibleExchanges` is the finite set of all
compatible deltas, and its state-only bridge to `availableExchanges 0` is
`compatibleExchanges_eq_availableExchanges_zero`.

The rescue results are:

- `exists_boundaryCompatible_of_forbiddenExchangeSet_ne_univ` for a non-full
  forbidden set;
- `exists_nonzero_boundaryCompatible_of_not_compatible_zero` when zero is
  currently incompatible and the forbidden set is non-full.

The cardinality identities are:

```lean
compatible.card + forbidden.card = 4
compatible.card = 4 - forbidden.card
```

Consequently, no contacts give four compatible exchanges, a singleton contact
gives three, three distinct forbidden deltas give one, and a full forbidden
set admits none. The implementation does not claim that four contacts are
distinct; the set cardinality records the actual distinct forbidden deltas.

## Regression cases

`DkMathTest/Tromino/PieceExchangeAxiomAudit.lean` checks:

1. no contacts: all four exchanges are compatible;
2. one conflicting contact: zero is forbidden and three exchanges remain;
3. two contacts with the same forbidden delta: only one forbidden state is
   counted;
4. three distinct forbidden deltas: exactly one compatible exchange remains;
5. four forbidden deltas: no compatible exchange exists.

## Validation

Focused build:

```text
lake build DkMath.Tromino.Exchange DkMath.Tromino.ExchangeRescue \
  DkMath.Tromino.PieceExchange \
  DkMathTest.Tromino.PieceExchangeAxiomAudit
```

Result: successful (`Build completed successfully (1493 jobs)`). The audit
reported only standard Lean/Mathlib dependencies (`propext`,
`Classical.choice`, and/or `Quot.sound`). No `sorryAx`, `admitAx`, or new
axiom declaration was introduced, and no unsafe declaration was added.

## Stop boundary

TRM-005 stops at the finite state-only piece boundary model and its rescue
calculus. It does not establish a geometric contact provider, a MacroCell
repair, global proper coloring, or any universal tromino tiling theorem.
