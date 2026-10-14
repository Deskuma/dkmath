# TRM-004 report: forbidden-state rescue / exchange liberty

Date: 2026-09-25
Branch: `research/Tromino-ExchangeCalculus-260924-v0`

## Scope

The state-only forbidden-set rescue calculus is complete. The implementation
does not import CosmicBridge or Restoration and does not add geometry, boundary
contacts, colored pieces, MacroCell, BoundaryIR, graph search, or optimization.

## Complete exchange-to-target API

`DkMath.Tromino.Exchange` now exposes:

```lean
existsUnique_exchange_to (x y : TrominoState) :
  ∃! delta, exchange delta x = y
```

The equal-source case uses the identity delta; the distinct-source case
reduces to the existing nonzero theorem. The optional permutation was also
introduced:

```lean
exchangeEquiv (x : TrominoState) : TrominoState ≃ TrominoState
```

It is Mathlib's `Equiv.addRight`, with `exchangeEquiv_apply` identifying its
application with `exchange delta x` using commutativity.

## Available exchanges

The production definition is:

```lean
def availableExchanges (x : TrominoState) (B : Finset TrominoState) :=
  Finset.univ.filter (fun delta => exchange delta x ∉ B)
```

The main rewrite theorem is
`mem_availableExchanges_iff`. No separate forbidden-delta API was added; its
filter is kept internal to the cardinality proof to avoid duplicate surfaces.

## Rescue theorem surface

The public theorems are:

- `exists_availableExchange_of_ne_univ`: a non-full forbidden target set has a
  legal exchange;
- `exists_nonzero_availableExchange_of_mem_of_ne_univ`: if the current state
  is forbidden and the set is not full, a legal nonzero exchange exists;
- `card_availableExchanges_add_card_forbidden`:
  `available.card + B.card = 4`;
- `card_availableExchanges`:
  `available.card = 4 - B.card`;
- `card_availableExchanges_eq_one_of_card_eq_three`;
- `availableExchanges_eq_empty_of_eq_univ`;
- `availableExchanges_eq_empty_iff`.

The rescue proof obtains a target outside `B` and uses
`existsUnique_exchange_to`; it does not enumerate the four states. The exact
cardinality proof transports the forbidden-target filter through
`exchangeEquiv` and then uses the Finset filter partition identity.

## Regression cases

`DkMathTest/Tromino/ExchangeRescueAxiomAudit.lean` covers:

1. empty forbidden set gives four legal exchanges;
2. `{x}` gives three legal exchanges, and every legal delta is nonzero;
3. forbidden cardinality three gives one legal exchange;
4. `Finset.univ` gives an empty available set;
5. non-full rescue and nonzero rescue existences;
6. the empty-set iff all-forbidden theorem.

All cases remain state-only and use no color names.

## Validation

Focused build:

```text
lake build DkMath.Tromino.Exchange DkMath.Tromino.ExchangeRescue DkMathTest.Tromino.ExchangeRescueAxiomAudit
```

Result: successful (`Build completed successfully (1492 jobs)`). The substantive
`#print axioms` audit reported only standard Lean/Mathlib dependencies:
`propext`, `Classical.choice`, and/or `Quot.sound`, depending on the theorem.
No `sorryAx`, `admitAx`, or new axiom declaration was introduced, and no
unsafe declaration was added.

## Stop boundary

TRM-004 stops at the finite state-only liberty/rescue calculus. It does not
claim that a geometric boundary contact produces a particular forbidden state,
that a colored piece remains proper, or that a piece-level forbidden set is
non-full. Those remain later checkpoints.
