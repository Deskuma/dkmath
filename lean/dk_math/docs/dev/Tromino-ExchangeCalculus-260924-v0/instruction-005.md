
# TRM-006 — Atomic FourColorCell / executable local kernel

## Goal

Introduce the first geometric colored object that will later become one
MacroCell.

The atomic object is the existing 2×2 geometric block equipped with the four
Tromino states exactly once.

This checkpoint must also audit the computability of the local exchange
candidate API before higher solver layers depend on it.

Do not implement MacroCell recursion, peel/restore stacks, BoundaryIR, graph
traversal, residual optimization, or Four Color claims yet.

## Existing owners

Reuse:

- DkMath.Polyomino.Cell
- DkMath.Polyomino.Shape
- DkMath.Polyomino.Tromino.block2
- DkMath.Polyomino.Tromino.area_block2
- DkMath.Tromino.TrominoState
- DkMath.Tromino.uniformExchange
- DkMath.Tromino.uniformExchange_eq_iff
- DkMath.Tromino.uniformExchange_ne_iff
- DkMath.Tromino.availableExchanges
- DkMath.Tromino.forbiddenExchangeSet

Do not import CosmicBridge or Restoration unless a concrete theorem needs
them. The atomic colored-cell layer should remain as low-dependency as
possible.

## A. Computability audit / repair

Before adding the colored cell, inspect:

compatibleExchanges : Finset BoundaryContact -> Finset TrominoState

It is currently declared noncomputable.

Determine whether it can be made computable without changing semantics.

Preferred route:

compatibleExchanges contacts :=
  availableExchanges 0 (forbiddenExchangeSet contacts)

or an equivalent direct Finset filter with synthesized decidability.

If this is clean:

- replace the noncomputable definition;
- preserve existing theorem names and behavior where practical;
- keep compatibleExchanges_eq_availableExchanges_zero as rfl/simp or a thin
  theorem.

If Mathlib elaboration genuinely requires classical choice, record why and
leave it unchanged. Do not force a brittle refactor.

This audit matters because later LocalSolver / Optimizer code should be
executable.

## B. Atomic colored cell representation

Introduce a minimal structure representing a finite geometric shape with a
state assignment.

Preferred shape:

structure ColoredShape where
  shape : Shape
  color : Cell -> TrominoState

or, if stronger typing is cleaner:

structure ColoredShape where
  shape : Shape
  color : {c // c in shape} -> TrominoState

Compare the two carefully.

The second form prevents meaningless colors outside the piece, but may make
uniform exchange and boundary APIs heavier. Choose the representation that
best supports future MacroCell and restoration work.

Report the decision.

Do not yet introduce general planar-map coloring infrastructure.

## C. Complete four-state predicate

Define a predicate expressing that the four states appear exactly once on the
atomic shape.

Prefer a structural/bijective definition over four named colors.

Possible formulations:

- color restricted to the shape is injective and shape.card = 4;
- the image of the shape under color is Finset.univ;
- an Equiv exists between the four cells and TrominoState.

Choose the formulation that gives the best reusable theorem surface.

Target semantic theorem:

CompleteFourState P
->
every TrominoState occurs at exactly one cell of P.

If the selected representation makes this theorem immediate, expose useful
projection lemmas rather than duplicating proof content.

## D. Canonical FourColorCell

Construct one canonical atomic colored block on the existing block2 footprint.

Use the four coordinate cells already present in block2 and assign:

(0,0), (1,0), (0,1), (1,1)

to the four TrominoState values in any fixed algebraic order.

Do not use color names in production.

The construction should satisfy:

- shape = block2;
- shape.card = 4;
- CompleteFourState;
- each state occurs exactly once.

The exact assignment is a calibration choice, not a theorem about colors.

## E. Uniform exchange action on colored shapes

Define uniformExchangeColoredShape delta P, preserving the footprint and
adding delta to every stored state.

Prove:

- shape is unchanged;
- CompleteFourState is preserved;
- state multiplicity is preserved;
- if two cells had distinct states, they remain distinct.

The key proof should reuse uniformExchange injectivity rather than enumerate
the four states.

## F. Internal grid adjacency — bounded scope

The repository currently has no obvious production owner for Cell adjacency.

For this checkpoint, do one of the following:

Outcome A (preferred if simple):
Define a Tromino-local grid adjacency predicate for Cell:

cells differ by exactly one unit horizontally or vertically.

Then define internalProper for a ColoredShape only over adjacent cells that
belong to its shape, and prove uniform exchange preserves internalProper.

Outcome B:
If introducing adjacency would start a broader geometry ownership decision,
defer it and prove only pairwise distinctness preservation on the atomic
FourColorCell.

Do not create a general graph framework merely to satisfy this checkpoint.

Record which outcome was chosen.

## G. Atomic properness

If adjacency is introduced, prove the canonical FourColorCell is internally
proper.

If adjacency is deferred, prove the stronger/simple fact that all four cells
have pairwise distinct states; this already implies properness for any
irreflexive adjacency restricted to distinct cells.

## H. Exchange orbit of the atomic cell

Show that uniform exchange gives four state-complete versions of the same
geometric block.

Useful theorem candidates:

uniformExchangeColoredShape_zero
uniformExchangeColoredShape_involutive
atomicFourColorCell_exchange_complete

If cheap, prove that two different deltas produce different colorings on the
same nonempty atomic cell.

Do not introduce GL(2,2), affine S4, or spatial D4 actions yet.

## I. Relation to TRM-002

Optionally expose a very thin cardinal calibration:

atomic FourColorCell has

- 4 geometric cells;
- 4 states exactly once.

Do not merge it into CosmicBridge in this checkpoint.

The purpose is to prepare the later collapse:

atomic FourColorCell -> one MacroCell.

## J. Regression examples

Audit/test:

1. canonical atomic cell has block2 footprint;
2. card footprint = 4;
3. all four states occur exactly once;
4. exchange by zero leaves the coloring unchanged;
5. any exchange preserves completeness;
6. if computability repair succeeded, #eval or a decidable example may verify
   compatibleExchanges for a small contact set.

Do not require #eval if the project test style avoids executable output; a
decidable theorem/example is sufficient.

## K. Proposed modules

Preferred production:

- DkMath/Tromino/FourColorCell.lean

Audit:

- DkMathTest/Tromino/FourColorCellAxiomAudit.lean

If a generic ColoredShape abstraction is clearly reusable and substantial,
it may be split into:

- DkMath/Tromino/ColoredShape.lean
- DkMath/Tromino/FourColorCell.lean

Do not split files merely for size.

## L. Validation

Run focused builds for all changed/new modules, including PieceExchange if its
computability definition changes.

Run git diff --check.

Audit substantive public theorems with #print axioms.

Scan new/changed files for:

- sorry
- admit
- unsafe
- new axiom declarations

Also report any remaining noncomputable declarations introduced or inherited
in the new local solver path.

## M. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-005.md

Record:

- compatibleExchanges computability decision;
- ColoredShape representation choice;
- CompleteFourState representation;
- canonical atomic assignment;
- exchange preservation theorems;
- adjacency outcome A/B;
- regression results;
- build / axiom audit;
- any remaining obstacle before MacroCell.

## Stop condition

Stop once the atomic 2×2 four-state cell is kernel-checked and uniform exchange
preserves its complete four-state structure.

Do not proceed to MacroCell collapse/expand, recursive substitution,
BoundaryIR, graph, residual optimization, or Four Color claims without review.
