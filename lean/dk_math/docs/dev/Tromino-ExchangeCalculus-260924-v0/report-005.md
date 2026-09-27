# TRM-006 report: atomic four-state colored cell

Date: 2026-09-25
Branch: `research/Tromino-ExchangeCalculus-260924-v0`

## Scope

The atomic geometric colored-cell layer is complete. It introduces one
finite colored shape on the existing `block2` footprint and stops before
MacroCell recursion, peel/restore stacks, BoundaryIR, graph traversal,
residual optimization, and Four Color claims.

## Computability decision

`compatibleExchanges` was changed from a filtered definition requiring
classical predicate decidability to the computable definition

```lean
def compatibleExchanges (contacts : Finset BoundaryContact) :
    Finset TrominoState :=
  availableExchanges 0 (forbiddenExchangeSet contacts)
```

The existing theorem
`compatibleExchanges_eq_availableExchanges_zero` is preserved and is now
proved by `rfl`. The existing membership and cardinality behavior remains
unchanged. A decidable audit example computes a singleton conflicting contact
set to three compatible exchanges.

No `noncomputable` declaration was introduced in the new local solver path.

## ColoredShape representation

The chosen representation is:

```lean
structure ColoredShape where
  shape : Shape
  color : Cell → TrominoState
```

This keeps the geometric footprint explicit while allowing uniform exchange
to act pointwise without dependent subtype transport. Colors outside the
finite shape are semantically irrelevant and do not affect the local
predicates.

## CompleteFourState

`CompleteFourState P` is defined structurally by:

```lean
P.shape.card = 4 ∧ P.shape.image P.color = Finset.univ
```

The image-card argument yields `Set.InjOn` on the shape. Consequently,
`completeFourState_existsUnique_cell` proves that every `TrominoState` occurs
at exactly one cell, and `completeFourState_stateMultiplicity` records the
corresponding multiplicity-one statement. Pairwise state distinctness is
exposed by `PairwiseDistinctOnShape`.

## Canonical atomic cell

`atomicFourColorCell` uses `DkMath.Polyomino.Tromino.block2` and assigns the
four coordinates in the fixed order

```text
(0,0) -> (0,0)   (1,0) -> (1,0)
(0,1) -> (0,1)   (1,1) -> (1,1)
```

These are algebraic `TrominoState` values, not named colors. The kernel checks
the footprint equality, card four, complete four-state property, unique
state occurrence, pairwise distinctness, and internal properness.

## Uniform exchange action

`uniformExchangeColoredShape` preserves the footprint. The public theorems
prove:

- state equality and inequality preservation via the existing
  `uniformExchange_eq_iff` / `uniformExchange_ne_iff`;
- state multiplicity reindexing under the involution;
- preservation of `CompleteFourState`;
- preservation of `PairwiseDistinctOnShape` and `internalProper`;
- zero identity and involutivity;
- completeness of every exchanged canonical cell;
- injectivity of the delta orbit for every nonempty colored shape.

## Adjacency outcome

Outcome A was selected. A local `gridAdjacent` predicate expresses horizontal
or vertical unit separation of two integer grid cells. `internalProper` only
quantifies over adjacent cells already belonging to the finite shape; no
general graph framework was introduced. The canonical `block2` cell is
internally proper because its complete four-state structure gives pairwise
distinct states and grid adjacency is irreflexive.

## Regression audit

`DkMathTest/Tromino/FourColorCellAxiomAudit.lean` checks:

1. canonical footprint equals `block2`;
2. footprint card is four;
3. every state occurs exactly once;
4. zero exchange is identity;
5. arbitrary exchange preserves completeness;
6. multiplicity, pairwise distinctness, and internal properness are preserved;
7. the atomic exchange orbit is injective;
8. the now-computable `compatibleExchanges` returns card three for a small
   conflicting contact set.

## Validation

Focused build:

```text
lake build DkMath.Tromino.Exchange DkMath.Tromino.ExchangeRescue \
  DkMath.Tromino.PieceExchange DkMath.Tromino.FourColorCell \
  DkMathTest.Tromino.PieceExchangeAxiomAudit \
  DkMathTest.Tromino.FourColorCellAxiomAudit
```

Result: successful (`Build completed successfully (8932 jobs)`). The
substantive `#print axioms` audit reported only standard Lean/Mathlib
dependencies (`propext`, `Classical.choice`, and/or `Quot.sound`). No
`sorryAx`, `admitAx`, or new axiom declaration was introduced, and no unsafe
declaration was added.

## Remaining boundary

The atomic cell is kernel-checked, but no geometric boundary-contact provider
or MacroCell collapse/expand API exists yet. Those interfaces, together with
restoration and recursive solver structure, remain outside TRM-006 and must
be reviewed before implementation.
