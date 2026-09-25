# TRM-009 report: recursive scaled macro levels

Date: 2026-09-25
Branch: `research/Tromino-ExchangeCalculus-260924-v0`

## Scope

TRM-009 is implemented through the exact recursive scale law. The new
carrier has level `0` equal to `FourColorMacroCell`, and each successor level
is a function from the four typed positions of `block2` to the preceding
level. No BoundaryIR, graph traversal, residual optimization, physical
flattening, or new Four Color claim was introduced.

## Typed block positions

`Block2Pos` is the finite subtype

```lean
{c : Cell // c ∈ block2}
```

with a kernel-checked finite cardinality theorem
`card_Block2Pos : Nat.card Block2Pos = 4`. The computable observers
`bodyPositions` and `gapPositions` filter this carrier by `L_tromino` and
`hole2`. They prove:

```text
card body = 3
card gap  = 1
body ∪ gap = univ
Disjoint body gap
```

`gapPosition` and `gapChild` expose the successor gap as a child of exactly
the lower-level type `ScaledMacroCell k`; no dependent BookOfMagic adapter was
added.

## Recursive carrier and canonical cell

```lean
def ScaledMacroCell : Nat → Type
  | 0 => FourColorMacroCell
  | k + 1 => Block2Pos → ScaledMacroCell k
```

`canonicalScaledMacroCell 0` is `atomicFourColorMacroCell`. At every successor
level it is constant with the canonical lower-level cell at all four
positions.

## Atomic mass law

`atomicMass` counts level-zero atomic cells directly and sums the four child
masses at successor levels. The general theorem is:

```text
atomicMass k M = 4 ^ (k + 1)
```

The successor observers satisfy:

```text
bodyAtomicMass k M = 3 * 4^(k+1)
gapAtomicMass  k M =     4^(k+1)
body + gap            = atomicMass (k+1) M
```

This exposes the requested user-facing law `3 lower units + 1 residual = 4
lower units = 1 higher unit`. The canonical calibrations are:

```text
level 0 total = 4
level 1 total = 16, body = 12, gap = 4
level 2 total = 64, body = 48, gap = 16
```

The level-one values agree componentwise with the existing `MacroTromino`
frame counts; no structural equality between the recursive function carrier
and `MacroShape` was forced.

## Recursive exchange

`exchangeScaledMacroCell` is the existing certified four-state exchange at
level zero and is pointwise recursive at successors. The audit proves zero,
involution, and preservation of `atomicMass` at every level. The canonical
exchange mass theorem follows from the general mass law.

## Computability and axioms

All data definitions are computable. Finite cardinality and geometry checks
use ordinary `decide`; no declaration is marked `noncomputable`, and no new
axiom declaration, `sorry`, `admit`, or `unsafe` declaration was added. The
focused `#print axioms` output for the audited theorems contains only the
standard `propext`, `Classical.choice`, and `Quot.sound` dependencies already
used by the finite certified infrastructure.

## Regression audit

`DkMathTest/Tromino/RecursiveMacroAxiomAudit.lean` checks:

1. `Nat.card Block2Pos = 4`;
2. body/gap cardinalities `3` and `1`, union, disjointness, and `3 + 1 = 4`;
3. canonical level `0`, `1`, and `2` masses `4`, `16`, and `64`;
4. canonical level-one body/gap masses `12` and `4`;
5. canonical level-two body/gap masses `48` and `16`;
6. the general body-plus-gap mass split;
7. recursive zero exchange, involution, mass preservation, and typed gap
   projection.

## Validation

Focused build:

```text
lake build DkMath.Tromino.MacroCell DkMath.Tromino.Restoration \
  DkMath.Tromino.MacroTromino DkMath.Tromino.RecursiveMacro \
  DkMathTest.Tromino.RecursiveMacroAxiomAudit
```

Result: successful (`Build completed successfully (8937 jobs)`). A forbidden
construct scan was run over the new production and audit modules; it found no
`sorry`, `admit`, `unsafe`, `axiom`, or `noncomputable` declarations.

## Stop boundary

TRM-009 stops at the exact recursive scale law and successor `3 + 1` split.
Physical flattening, boundary signatures, graph interfaces, residual
optimization, and any universal Four Color or tiling conclusion remain
deferred.
