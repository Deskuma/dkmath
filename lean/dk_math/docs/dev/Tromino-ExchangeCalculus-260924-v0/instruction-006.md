
# TRM-007 — FourColorMacroCell collapse / expand

## Goal

Introduce the first explicit macro abstraction above the atomic
`FourColorCell` layer.

This checkpoint must formalize the statement:

> a certified complete four-state colored shape can be treated as one macro
> unit, while retaining an exact reversible expansion back to its atomic
> colored geometry.

Important design boundary:

`CompleteFourState` currently includes `shape.card = 4`. Therefore this
checkpoint must **not** pretend that the same type is already the recursively
scaled macro-cell type for all levels.

Use a name such as `FourColorMacroCell` (preferred) or an equally explicit
level-0 name. Reserve a future `ScaledMacroCell` / `MacroLevel` abstraction
for recursive substitution.

Do not implement recursive substitution, macro 3+1 composition, BoundaryIR,
graph traversal, residual optimization, or Four Color claims in this
checkpoint.

## Existing owners

Reuse:

- `DkMath.Tromino.ColoredShape`
- `DkMath.Tromino.CompleteFourState`
- `DkMath.Tromino.atomicFourColorCell`
- `DkMath.Tromino.atomicFourColorCell_complete`
- `DkMath.Tromino.uniformExchangeColoredShape`
- `DkMath.Tromino.completeFourState_uniformExchangeColoredShape`
- `DkMath.Tromino.uniformExchangeColoredShape_zero`
- `DkMath.Tromino.uniformExchangeColoredShape_involutive`

Keep the module independent of BoundaryIR and solver code.

## Proposed production module

`DkMath/Tromino/MacroCell.lean`

Audit:

`DkMathTest/Tromino/MacroCellAxiomAudit.lean`

## A. Certified level-0 macro payload

Preferred representation:

```lean
structure FourColorMacroCell where
  payload : ColoredShape
  complete : CompleteFourState payload
```

A subtype representation is also acceptable if it produces a cleaner API:

```lean
def FourColorMacroCell := {P : ColoredShape // CompleteFourState P}
```

Choose the form that gives the cleanest extensionality and exchange action.

This type means:

- one macro unit;
- carrying one complete four-state atomic payload;
- whose expansion has exactly four atomic cells.

It does **not** yet mean an arbitrary recursive macro level.

## B. Collapse / expand

Define:

```text
collapseFourColorCell
expandFourColorMacroCell
```

with semantic types equivalent to:

```lean
collapseFourColorCell
    (P : ColoredShape) (hP : CompleteFourState P) :
    FourColorMacroCell

expandFourColorMacroCell
    (M : FourColorMacroCell) :
    ColoredShape
```

Prove the exact reversibility laws:

```text
expand (collapse P hP) = P
collapse (expand M) M.complete = M
```

The second theorem should rely on proof irrelevance/extensionality rather than
comparing proof terms manually.

If an `Equiv` between
`{P : ColoredShape // CompleteFourState P}` and `FourColorMacroCell` is
natural, expose it. Do not create redundant wrappers only to satisfy this
instruction.

## C. Canonical atomic macro-cell

Construct:

```text
atomicFourColorMacroCell
```

by collapsing the existing `atomicFourColorCell`.

Target theorems:

- its expansion is `atomicFourColorCell`;
- expanded shape is `block2`;
- expanded atomic area/cardinality is `4`;
- expanded payload is complete.

Do not duplicate the atomic coloring definition.

## D. Atomic area versus macro count

Expose the level-0 scale relation explicitly.

A `FourColorMacroCell` is one macro unit:

```text
macroCount = 1
```

while its expanded atomic footprint has card 4.

Possible API:

```lean
def macroCount (_ : FourColorMacroCell) : Nat := 1
def atomicCellCount (M : FourColorMacroCell) : Nat :=
  (expandFourColorMacroCell M).shape.card
```

Required semantic theorem:

```text
atomicCellCount M = 4 * macroCount M
```

or the equivalent pair:

```text
atomicCellCount M = 4
macroCount M = 1
```

Prefer the simpler public API if the multiplication theorem is artificial.

This is the exact formal meaning of:

```text
4 atomic cells -> 1 macro unit
```

at level 0.

## E. Uniform exchange action descends to macro-cells

Define:

```text
exchangeFourColorMacroCell delta M
```

by uniformly exchanging the expanded payload and reusing
`completeFourState_uniformExchangeColoredShape` to certify completeness.

Prove the commuting square:

```text
expand (exchangeMacro delta M)
=
uniformExchangeColoredShape delta (expand M)
```

Then prove:

- zero exchange is identity;
- every exchange is involutive;
- macro completeness is preserved by construction;
- atomic cell count is unchanged.

If easy, prove the exchange orbit on the canonical atomic macro-cell is
injective in delta, reusing the existing nonempty-payload theorem.

## F. Geometry ownership boundary

The macro-cell wrapper should not define new geometric adjacency or boundary
notions.

All geometry remains in the expanded `ColoredShape`.

Future boundary signatures should be observers on the expanded payload or on a
separate interface object, not fields embedded prematurely in
`FourColorMacroCell`.

## G. Restoration reconnaissance

Read `DkMath.Tromino.Restoration` and record, but do not yet implement, the
next bridge:

- geometric `Shape` restoration currently restores a missing footprint;
- future macro restoration must restore a missing `FourColorMacroCell`
  payload, not merely its footprint.

Determine whether the next checkpoint should use a dependent
`Gap : Core -> Type` carrying a macro payload, or a lighter certified slot
record.

Do not modify `Restoration.lean` in TRM-007 unless a tiny generic lemma is
strictly necessary.

## H. Recursive-type warning

Do not define:

```text
MacroCell := FourColorMacroCell
```

as the final recursive abstraction.

The future recursion must be able to represent an object whose atomic area is

```text
4, 16, 64, ...
```

or, equivalently, carry a scale/level parameter.

TRM-007 is only the level-0 collapse/expand contract.

## I. Regression examples

Audit/test at least:

1. expand(collapse atomicFourColorCell) = atomicFourColorCell;
2. collapse(expand atomicMacro) = atomicMacro;
3. atomic macro expands to block2;
4. atomicCellCount atomicMacro = 4;
5. macroCount atomicMacro = 1 if macroCount is introduced;
6. arbitrary exchange commutes with expansion;
7. zero exchange leaves macro unchanged;
8. applying the same exchange twice restores the macro;
9. all new definitions remain computable where possible.

## J. Validation

Run focused builds for:

- DkMath.Tromino.FourColorCell
- DkMath.Tromino.MacroCell
- DkMathTest.Tromino.MacroCellAxiomAudit

Run `git diff --check`.

Audit substantive public theorems with `#print axioms`.

Scan new/changed files for:

- `sorry`
- `admit`
- `unsafe`
- new `axiom`
- unintended `noncomputable`

Report any unavoidable noncomputability explicitly.

## K. Report

Create:

`docs/dev/Tromino-ExchangeCalculus-260924-v0/report-006.md`

Record:

- structure vs subtype representation choice;
- collapse/expand API;
- exact reversibility theorems;
- atomic/macro count calibration;
- exchange action and commuting theorem;
- computability status;
- restoration reconnaissance;
- what is still missing before recursive 3+1 macro construction.

## Stop condition

Stop after a complete four-state atomic payload can be losslessly collapsed to
one level-0 macro unit and expanded back, with uniform exchange transported
through the abstraction.

Do not proceed to recursive 3+1 macro composition, typed macro gaps,
BoundaryIR, graph search, residual optimization, or Four Color claims without
review.
