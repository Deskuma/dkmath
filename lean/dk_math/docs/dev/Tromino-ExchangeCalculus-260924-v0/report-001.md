# TRM-002 report: three-way Body/Gap calibration

Date: 2026-09-24
Branch: `research/Tromino-ExchangeCalculus-260924-v0`

## Scope

The exact numerical calibration requested by TRM-002 is complete. The state,
geometric, and CosmicFormula layers remain separate. No exchange rescue,
forbidden set, GapCrystal adapter, macro-cell recursion, BoundaryIR, graph,
optimization, or Four Color layer was added.

## Exact imports

`DkMath.Tromino.CosmicBridge` imports:

- `DkMath.Tromino.State`
- `DkMath.Tromino.Exchange`
- `DkMath.Tromino`
- `DkMath.CosmicFormula.Mass.BodyGapSplit`
- `DkMath.CosmicFormula.CoreBeamGap`

`BodyN` is consumed from the existing `CosmicFormulaBinom` owner through the
public `CoreBeamGap` dependency. NumberGeometry is not in the dependency
graph.

## Definitions added

`DkMath/Tromino/CosmicBridge.lean` adds:

- `stateSplit (x) : BodyGapSplit ℕ`, with
  `big = Nat.card TrominoState`, `body = card (waitingStates x)`, and
  `gap = 1`;
- `geometricSplit : BodyGapSplit ℕ`, with the existing block2, L-tromino,
  and hole areas;
- `cosmicUnitSquareSplit : BodyGapSplit ℕ`, with degree `2`, `x = 1`, and
  `u = 1`;
- projection calibration theorems for all three packets;
- `state_card_eq_waiting_add_one`;
- `threeWay_big`, `threeWay_body`, `threeWay_gap`, and
  `threeWay_calibration`.

The state packet's gap is the cardinality `1` of the distinguished current
slot. It is not the algebraic zero state.

## Three split constructions

The state packet stores its split from `card_state` and
`card_waitingStates`. The geometric packet stores the exact existing theorem
`DkMath.Polyomino.Tromino.area_block2_eq_area_L_add_area_hole`; it does not
recompute the split with a new arithmetic proof.

The CosmicFormula packet stores
`DkMath.CosmicFormula.CoreBeamGap.big_eq_body_add_gap`. Its `Big` and `Gap`
values are evaluated at the unit square, and `Body = 3` is derived from the
stored conservation identity plus `Big = 4` and `Gap = 1`, rather than by
unfolding the GN/GTail internals.

All three packets expose:

```text
big  = 4
body = 3
gap  = 1
```

The public result is exact shared additive calibration only; it does not state
that the three underlying worlds are isomorphic or that any stronger coloring
or CosmicFormula uniqueness result follows.

## Equality surface choice

Componentwise equalities were chosen instead of equality of the three
`BodyGapSplit` structures. Structure equality would also compare the stored
proof fields, while the intended mathematical content is exactly the equality
of `big`, `body`, and `gap`. The `threeWay_*` theorems expose these three
components directly, and `threeWay_calibration` packages them as a conjunction.

## Validation

Focused build:

```text
lake build DkMath.Tromino.CosmicBridge DkMathTest.Tromino.CosmicBridgeAxiomAudit
```

Result: successful (`Build completed successfully (8944 jobs)`). The audit
test checks the state `4 = 3 + 1` theorem, all three packet projections, and
the full three-way calibration theorem.

The substantive `#print axioms` output was:

```text
state_card_eq_waiting_add_one       [propext, Classical.choice, Quot.sound]
geometricSplit_big                  [propext, Classical.choice, Quot.sound]
cosmicUnitSquare_body               [propext, Classical.choice, Quot.sound]
threeWay_calibration                [propext, Classical.choice, Quot.sound]
```

These are standard Lean/Mathlib dependencies. No `sorryAx`, `admitAx`, or
new user axiom was introduced, and no unsafe declaration was added.

## Stop boundary

TRM-002 is complete at the exact `4 = 3 + 1` three-way calibration. TRM-003
must separately decide typed restoration semantics before any GapCrystal layer
is connected.
