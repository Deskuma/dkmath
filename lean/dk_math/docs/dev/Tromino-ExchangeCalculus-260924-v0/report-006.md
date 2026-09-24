# TRM-007 report: FourColorMacroCell collapse / expand

Date: 2026-09-25
Branch: `research/Tromino-ExchangeCalculus-260924-v0`

## Scope

The level-0 macro wrapper is complete. A certified complete four-state
`ColoredShape` can be collapsed to one `FourColorMacroCell` and expanded back
without loss. No recursive substitution, scaled levels, 3+1 composition,
BoundaryIR, graph traversal, residual optimization, or Four Color claim was
introduced.

## Representation choice

The production representation is the structure form:

```lean
structure FourColorMacroCell where
  payload : ColoredShape
  complete : CompleteFourState payload
```

This keeps the certified payload and its proof together, gives direct access
to the expanded geometry, and makes the exchange action a transparent lift.
The wrapper is explicitly level-0; it is not the future recursive
`ScaledMacroCell` or `MacroLevel` type.

## Collapse and expansion

The public definitions are:

```lean
collapseFourColorCell
expandFourColorMacroCell
```

The exact reversibility theorems are:

- `expand_collapseFourColorCell`, which is definitionally the original
  payload;
- `collapse_expandFourColorMacroCell`, which uses the payload extensionality
  theorem and proof irrelevance for the certification field.

The canonical value
`atomicFourColorMacroCell` is obtained by collapsing the existing
`atomicFourColorCell`; its coloring definition is not duplicated.

## Atomic versus macro count

`macroCount` is definitionally `1` for every level-0 wrapper, while
`atomicCellCount` is the card of the expanded shape. Since the certification
contains `shape.card = 4`, the module proves:

```lean
atomicCellCount M = 4
macroCount M = 1
atomicCellCount M = 4 * macroCount M
```

For the canonical macro cell, expansion is the existing `block2` payload and
has card `4`.

## Exchange action

`exchangeFourColorMacroCell` uniformly exchanges the expanded payload and
rebuilds its `CompleteFourState` certificate using
`completeFourState_uniformExchangeColoredShape`.

The commuting square
`expand_exchangeFourColorMacroCell` is definitionally true. The module also
proves zero identity, involutivity, preservation of the expanded atomic cell
count, and injectivity of the exchange orbit on the canonical nonempty atomic
payload.

## Restoration reconnaissance

`DkMath.Tromino.Restoration` currently owns geometric restoration over
`Shape`: `restoreShape` adjoins a retained core and gap, while
`shapeRestoreRel`, `shapeGapFiber`, and `shapeGapCrystal` certify the fixed
footprint relation. The existing atomic bridge restores `L_tromino` plus
`hole2` to `block2`; it does not carry a colored payload.

The next bridge should therefore use a lightweight certified slot record that
stores a `FourColorMacroCell` together with its restoration certificate. At
the current level the macro payload is independent of the retained core, so a
dependent `Gap : Core → Type` would add type-level coupling before a genuine
core-dependent interface exists. A dependent gap should be introduced later
if recursive levels or boundary interfaces make the allowable payload depend
on the core.

`Restoration.lean` was read for this reconnaissance and was not modified.

## Computability

No new declaration in `MacroCell.lean` is marked `noncomputable`. The data
definitions use direct structure construction and the existing computable
colored-shape action; proof fields are propositions and are erased. The
focused audit includes a decidable calibration of `macroCount`. The theorem
axiom report may contain `Classical.choice` through inherited certification
proofs, but no new noncomputable keyword or axiom declaration was added.

## Regression audit

`DkMathTest/Tromino/MacroCellAxiomAudit.lean` checks:

1. expansion after collapse;
2. collapse after expansion;
3. canonical expansion and `block2` footprint;
4. atomic card `4`, macro count `1`, and the multiplication calibration;
5. exchange commuting with expansion;
6. zero exchange identity;
7. involutive exchange;
8. unchanged atomic cell count;
9. injective canonical exchange orbit;
10. executable macro-count calibration.

## Validation

Focused build:

```text
lake build DkMath.Tromino.Exchange DkMath.Tromino.ExchangeRescue \
  DkMath.Tromino.PieceExchange DkMath.Tromino.FourColorCell \
  DkMath.Tromino.MacroCell \
  DkMathTest.Tromino.PieceExchangeAxiomAudit \
  DkMathTest.Tromino.FourColorCellAxiomAudit \
  DkMathTest.Tromino.MacroCellAxiomAudit
```

Result: successful (`Build completed successfully (8934 jobs)`). The
substantive `#print axioms` audit reported only standard Lean/Mathlib
dependencies (`propext`, `Classical.choice`, and/or `Quot.sound`). No
`sorryAx`, `admitAx`, or new axiom declaration was introduced, and no unsafe
declaration was added.

## Stop boundary

The level-0 complete payload can now be losslessly collapsed to one macro unit
and expanded back, with uniform exchange transported through the wrapper.
Recursive 3+1 macro construction, typed macro gaps, BoundaryIR, graph search,
residual optimization, and Four Color claims remain deferred.
