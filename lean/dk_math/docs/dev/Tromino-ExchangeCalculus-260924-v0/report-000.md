# TRM-000 / TRM-001 report

Date: 2026-09-24
Branch: `research/Tromino-ExchangeCalculus-260924-v0`
Base develop: `11f1762613ce8ca6d971956c18e13077388a202e`

## Scope

The repository-first audit and minimal four-state / exchange kernel are
complete. `DkMath/Tromino.lean` was not refactored. No BoundaryIR, graph
search, macro recursion, optimization, exchange-rescue, or Four Color layer
was started.

The branch is based on the requested develop commit. The working tree already
contained the branch README and instruction changes; they were preserved.

## Representation decision

The production carrier is:

```lean
abbrev DkMath.Tromino.TrominoState := ZMod 2 × ZMod 2
```

This is the requested default because addition is the exchange law, the
carrier has four states, and its three nonzero elements are the three
nontrivial choices. `Bool × Bool` does not provide the same natural
additive-group API, while `Fin 4` would require an additional modular
operation layer. Repository search found no production four-state exchange
carrier that should own this API instead.

Mathlib owner API:

- `Mathlib.GroupTheory.SpecificGroups.KleinFour`
- `IsAddKleinFour`
- the existing instance `IsAddKleinFour (ZMod 2 × ZMod 2)`
- `IsAddKleinFour.card_four`

The NumberGeometry modules were inspected read-only and are not dependencies
of this kernel.

## Production declarations

Added under `DkMath.Tromino`:

- `DkMath/Tromino/State.lean`: `TrominoState`, `card_state`,
  `waitingStates`, `mem_waitingStates_iff`, `card_waitingStates`,
  `state_add_self`, `nonzeroStates_eq_waitingStates_zero`, and
  `card_nonzeroStates`.
- `DkMath/Tromino/Exchange.lean`: `exchange`, `exchange_zero`,
  `exchange_self_inverse`, `exchange_comp`, `exchange_commute`,
  `exchange_ne_of_nonzero`, `existsUnique_nonzero_exchange_to`, and
  `exchange_delta_ne_zero_iff`.

The kernel contains no color names and no geometric solver state.

## CosmicFormula reconnaissance

TRM-002 can expose a `DkMath.CosmicFormula.Mass.BodyGapSplit ℕ` with

```text
big  := area block2
body := area L_tromino
gap  := area hole2
```

using the existing theorem
`DkMath.Polyomino.Tromino.area_block2_eq_area_L_add_area_hole` as the stored
split. Existing area theorems calibrate these fields as `4`, `3`, and `1`.

The independent degree-two calibration is feasible through
`DkMath.CosmicFormula.CoreBeamGap`: `Big`, `BodyN`, and `Gap`, together with
`big_eq_body_add_gap`, reduce `d = 2`, `x = 1`, `u = 1` to `Big = 4`,
`Body = 3`, and `Gap = 1`. This remains reconnaissance only; no
CosmicFormula bridge was added.

## GapCrystal reconnaissance

`DkMath.BookOfMagic.GapCrystal` already provides the relevant dependent shape:
`GapFiber` stores a certified gap over a fixed core, and `GapCrystal` stores a
core, dependent gap, and restoration certificate. It is sufficient as the
future semantic owner for “a removed slot remembers what can be restored”. No
duplicate typed-gap abstraction was introduced.

## Validation

Focused build:

```text
lake build DkMath.Tromino.State DkMath.Tromino.Exchange DkMathTest.Tromino.ExchangeAxiomAudit
```

Result: successful (`Build completed successfully (1491 jobs)`). The test
module checks state cardinality, three waiting/nonzero choices, zero exchange,
involution, additive composition, commutativity, and unique nonzero exchange
to a distinct target.

`#print axioms` showed only standard Lean/Mathlib dependencies:
`propext`, `Classical.choice`, and/or `Quot.sound`, depending on the theorem.
No `sorryAx`, `admitAx`, or unsafe declaration was introduced.

## Dependency and naming issues

- The new algebra namespace is `DkMath.Tromino`; the existing geometric owner
  remains `DkMath.Polyomino.Tromino`.
- The instruction's repository-level `ROADMAP.md` is not present at the
  checked-out root. The active roadmap is
  `docs/dev/Tromino-ExchangeCalculus-260924-v0/ROADMAP.md`.
- The four dated Tromino plans are in repository-level `docs/not_implements/`,
  not under `lean/dk_math/docs`.

## Stop boundary

TRM-000 / minimal TRM-001 is the terminal scope of this report. Review is
required before starting TRM-002 or any rescue, macro-cell, boundary graph,
optimization, or planar-coloring work.
