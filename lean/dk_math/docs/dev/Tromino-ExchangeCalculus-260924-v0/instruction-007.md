
# TRM-008 — MacroTrominoFrame / typed macro gap

## Goal

Implement the first level-1 macro composition above FourColorMacroCell.

The target finite structure is the macro-coordinate analogue of the original
2×2 / L + hole geometry:

~~~text
[M][G]
[M][M]
~~~

where each M is a FourColorMacroCell and G is a typed slot whose expected
payload is also a FourColorMacroCell.

This checkpoint should formalize:

- macro body count = 3;
- macro gap count = 1;
- macro total count = 4;
- atomic payload count = 12 + 4 = 16;
- the missing macro payload is retained explicitly and can be restored.

Do not yet implement arbitrary recursive levels, physical 4×4 flattening,
BoundaryIR, graph traversal, residual optimization, or Four Color claims.

## Design principle

Keep two layers distinct:

1. macro-coordinate geometry:
   block2 / L_tromino / hole2 reused as a coordinate pattern;
2. payload:
   FourColorMacroCell values assigned to macro positions.

The macro coordinates are not atomic lattice cells semantically, even though
the same Cell/Shape representation is reused as a convenient finite coordinate
carrier.

Document this distinction explicitly.

## Existing owners

Reuse:

- DkMath.Polyomino.Cell
- DkMath.Polyomino.Shape
- DkMath.Polyomino.Tromino.block2
- DkMath.Polyomino.Tromino.L_tromino
- DkMath.Polyomino.Tromino.hole2
- block2_eq_L_union_hole
- disjoint_L_hole
- DkMath.Tromino.FourColorMacroCell
- atomicFourColorMacroCell
- macroCount
- atomicCellCount
- DkMath.Tromino.shapeRestoreRel
- DkMath.Tromino.shapeRestoreRel_gap_unique
- DkMath.BookOfMagic.GapCrystal if a thin adapter is useful
- DkMath.CosmicFormula.Mass.BodyGapSplit only for an optional count-calibration bridge

Do not modify BookOfMagic.

## Proposed production module

Preferred:

DkMath/Tromino/MacroTromino.lean

Audit:

DkMathTest/Tromino/MacroTrominoAxiomAudit.lean

## A. MacroShape

Introduce the minimal one-level-up analogue of ColoredShape:

structure MacroShape where
  shape : Shape
  payload : Cell -> FourColorMacroCell

As with ColoredShape, payload values outside shape are semantically irrelevant.

Do not call this the final recursive MacroCell type.

The meaning is:

- shape: finite macro-coordinate footprint;
- payload: one certified FourColorMacroCell at each occupied macro coordinate.

Provide extensionality if useful.

## B. Restriction

Define a restriction operation:

restrictMacroShape P S

whose footprint is P.shape ∩ S (or S under an explicit subset hypothesis) and
whose payload is inherited from P.

Choose the simplest API needed to obtain the L-shaped body from a 2×2 macro
frame.

Avoid introducing a general category of subobjects.

## C. Typed macro gap slot

Following report-006 reconnaissance, use a lightweight data record rather than
a dependent gap family.

Preferred semantic fields:

structure MacroGapSlot where
  footprint : Shape
  expected : FourColorMacroCell

For this checkpoint the canonical footprint is hole2, hence one macro
coordinate.

If it is cleaner, include a proof footprint.card = 1. Otherwise prove the
canonical slot has card one without making singleton-ness part of the generic
type.

Important:

- the footprint says where the macro unit is missing;
- expected says exactly which FourColorMacroCell is restored.

This is richer than geometric shapeRestoreRel, which remembers only the
missing footprint.

## D. Macro restoration relation

Define a relation for restoring a target MacroShape from:

- retained body MacroShape;
- MacroGapSlot.

The relation must express at least:

1. body footprint and gap footprint are disjoint;
2. their union is the target footprint;
3. payloads on the retained body agree with the target;
4. the gap's expected payload agrees with the target at the gap position.

Because the canonical gap has one macro coordinate, a singleton-specific
formulation is acceptable if it keeps the proof small and exact.

Do not invent a general multi-gap framework yet.

## E. Canonical complete macro frame

Construct a canonical 2×2 MacroShape with footprint block2.

Initially it is acceptable for all four macro positions to carry
atomicFourColorMacroCell.

If using different exchanged payloads makes later boundary work easier, do not
introduce that complexity here. Keep the first frame canonical and uniform.

Target facts:

- footprint = block2;
- macro position count = 4;
- every occupied macro position has atomicCellCount = 4.

## F. Canonical macro body and gap

Define:

- canonical body with footprint L_tromino;
- canonical MacroGapSlot with footprint hole2;
- expected payload = the payload removed from the canonical frame.

Prove the canonical macro restoration relation.

The proof of footprint restoration must reuse:

- disjoint_L_hole;
- block2_eq_L_union_hole.

Do not re-enumerate coordinates for the set-theoretic part.

## G. Macro counts

Expose exact counts:

- body macro count = 3;
- gap macro count = 1;
- total macro count = 4.

If useful, package this as:

BodyGapSplit Nat

at the macro-count level.

This should be a thin calibration analogous to TRM-002, not a dependency of
the core MacroShape type.

## H. Atomic mass / count lift

Define the atomic payload mass of a MacroShape as the sum over occupied macro
coordinates:

sum c in P.shape, atomicCellCount (P.payload c).

For the canonical frame prove:

- body atomic count = 12;
- gap expected atomic count = 4;
- total atomic count = 16;
- 12 + 4 = 16.

Prefer Finset.sum and existing atomicCellCount_eq_four. Do not flatten geometry
to a physical 4×4 Shape yet.

Also expose:

16 = 4 * 4

as the first scale relation if it is naturally useful.

## I. CosmicFormula calibration — optional thin bridge

If dependency-clean, expose a BodyGapSplit Nat for the canonical atomic counts:

big = 16
body = 12
gap = 4.

Do not claim this is a new CosmicFormula theorem by itself.

The intended interpretation is:

macro 3+1 decomposition
scaled by atomicCellCount = 4
gives atomic 12+4=16.

If this bridge creates unnecessary imports or file coupling, record it for the
next checkpoint instead.

## J. Unique typed restoration

There are two different uniqueness questions; keep them distinct.

1. footprint uniqueness:
   for fixed target/body footprints, shapeRestoreRel already makes the gap
   footprint unique.

2. payload uniqueness:
   for a fixed target MacroShape and fixed gap coordinate, the expected
   FourColorMacroCell should be forced by the target payload at that coordinate.

Prove the canonical or generic payload-uniqueness theorem if the chosen
restoration relation makes it straightforward.

Do not claim a global uniqueness theorem for arbitrary missing multi-cell
macro regions.

## K. Exchange action

Do not yet define exchange on the entire MacroShape unless it is a trivial
pointwise lift.

If implemented, require:

- footprint unchanged;
- every payload exchanged by exchangeFourColorMacroCell;
- canonical counts unchanged;
- restoration relation preserved when body, gap expected payload, and target
  are all exchanged uniformly.

The final restoration-preservation theorem is optional in this checkpoint if
it significantly increases scope.

## L. Recursive-level boundary

Do not define the final recursive type yet.

After TRM-008 we should have exactly one level of macro composition:

atomic colored cells
  -> FourColorMacroCell
  -> MacroShape with four macro positions
  -> L-shaped body + one typed macro gap.

Only the next checkpoint should decide the representation of levels k and
k+1.

## M. Regression examples

Audit at least:

1. canonical macro frame footprint = block2;
2. macro position count = 4;
3. canonical body footprint = L_tromino and count = 3;
4. canonical gap footprint = hole2 and count = 1;
5. canonical gap expected payload = atomicFourColorMacroCell;
6. canonical restoration certificate;
7. body atomic count = 12;
8. gap atomic count = 4;
9. total atomic count = 16;
10. footprint or payload uniqueness theorem, whichever is implemented.

## N. Validation

Run focused builds for:

- DkMath.Tromino.MacroCell
- DkMath.Tromino.Restoration
- DkMath.Tromino.MacroTromino
- DkMathTest/Tromino/MacroTrominoAxiomAudit

Run git diff --check.

Audit substantive public theorems with #print axioms.

Scan new/changed files for:

- sorry
- admit
- unsafe
- new axiom
- unintended noncomputable

## O. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-007.md

Record:

- MacroShape representation;
- MacroGapSlot representation;
- restoration relation;
- canonical frame/body/gap;
- macro 3+1 count;
- atomic 12+4=16 count;
- uniqueness results;
- whether a BodyGapSplit bridge was added;
- computability status;
- what remains before recursive levels.

## Stop condition

Stop after the first macro-coordinate Tromino frame has an exact typed-gap
restoration certificate and the count laws

3 + 1 = 4
and
12 + 4 = 16.

Do not proceed to arbitrary recursive levels, physical flattening, BoundaryIR,
graph search, residual optimization, or Four Color claims without review.
