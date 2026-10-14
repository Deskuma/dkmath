
# TRM-003 — Certified geometric restoration / GapCrystal bridge

## Goal

Connect Tromino geometry to the existing BookOfMagic restoration infrastructure
without introducing a duplicate TypedGap abstraction.

This checkpoint should establish the smallest exact statement:

> a geometric core together with a certified disjoint missing shape restores a
> fixed target shape, and for the atomic block2 / L-tromino example the missing
> shape is exactly the existing hole2.

The main purpose is to turn the informal "typed hole remembers what returns"
idea into a reusable restoration relation.

Do not implement MacroCell, recursive substitution, BoundaryIR, rescue, graph
search, or optimization in this checkpoint.

## Existing owners to reuse

- DkMath.Polyomino.Shape
- DkMath.Polyomino.Tromino.block2
- DkMath.Polyomino.Tromino.L_tromino
- DkMath.Polyomino.Tromino.hole2
- DkMath.Polyomino.Tromino.block2_eq_L_union_hole
- DkMath.Polyomino.Tromino.disjoint_L_hole
- DkMath.BookOfMagic.UniqueGap
- DkMath.BookOfMagic.GapFiber
- DkMath.BookOfMagic.GapCrystal

The dependency direction must be one-way:

DkMath.Tromino -> DkMath.BookOfMagic

Do not modify BookOfMagic.

## Proposed production module

DkMath/Tromino/Restoration.lean

Test/audit:

DkMathTest/Tromino/RestorationAxiomAudit.lean

## A. Generic shape restoration relation

Use the existing Polyomino Shape type.

Define a relation equivalent in meaning to:

shapeRestoreRel target core gap :=
  Disjoint core gap ∧ core ∪ gap = target

The exact name may be adjusted if repository conventions suggest a better one.

Important:

- target is fixed;
- core is the retained geometry;
- gap is the removed geometry;
- disjointness prevents overlap;
- union equality is the restoration certificate.

Also expose a thin restoration operation if useful:

restoreShape core gap := core ∪ gap

but do not add it merely for notation if the relation alone is cleaner.

## B. GapCrystal adapter

Instantiate the existing dependent infrastructure with:

Core := Shape
Gap := fun _ => Shape
RestoreRel := shapeRestoreRel target

Expose thin Tromino-owned aliases/adapters only if they improve usability.

Possible shapes:

shapeGapFiber target core
shapeGapCrystal target

Do not copy the definitions of GapFiber or GapCrystal.

## C. Atomic certified gap

Construct the certified object for the existing geometry:

target = block2
core   = L_tromino
gap    = hole2

The certificate must use the existing theorems:

- disjoint_L_hole
- block2_eq_L_union_hole

rather than recomputing the finite-set facts.

Target theorem meaning:

restoreShape L_tromino hole2 = block2

or the equivalent relation statement if no restoreShape def is added.

## D. Uniqueness of the missing shape

This is the central theorem of the checkpoint.

For a fixed target and fixed core, any two gaps satisfying shapeRestoreRel must
be equal.

Mathematically, the gap is forced to be target \ core.

Target theorem shape:

shapeRestoreRel_gap_unique
  (h1 : shapeRestoreRel target core gap1)
  (h2 : shapeRestoreRel target core gap2) :
  gap1 = gap2

Prefer a generic Finset proof. Do not enumerate block2 cells.

Then derive:

if a certified restoring gap exists for target/core, the existing
BookOfMagic.UniqueGap contract holds.

Possible theorem shape:

uniqueGap_of_shapeRestoreRel
  (h : shapeRestoreRel target core gap) :
  BookOfMagic.UniqueGap (shapeRestoreRel target) core

The exact elaborated dependent function spelling may differ.

## E. Atomic unique-gap theorem

Specialize the generic uniqueness theorem to the atomic Tromino:

block2 has a unique restoring Shape gap over L_tromino,
and hole2 is that gap.

Expose a user-facing theorem with this semantic content.

This theorem should justify the phrase:

"the atomic Tromino hole is typed by its restoration target and core; it is not
an unstructured blank."

## F. Optional complement characterization

If clean and cheap, prove:

shapeRestoreRel target core gap -> gap = target \ core

and/or the converse under the expected subset condition.

This is useful because future peel can compute the missing footprint by
difference.

Do not force this if Mathlib Finset API makes it substantially more complex
than the uniqueness proof. Record it as deferred if necessary.

## G. Interpretation boundary

This checkpoint establishes geometric restoration typing only.

It does not yet prove that a gap remembers:

- a color state;
- a four-state macro-cell payload;
- an orientation;
- a boundary signature;
- a recursive scale level.

Those belong to later MacroCell / BoundarySignature layers.

Thus BookOfMagic GapCrystal is reused now as the semantic owner of certified
restoration, while richer payloads may later be supplied by changing the
dependent Gap type.

## H. Relation to TRM-002

Do not merge restoration semantics into CosmicBridge.

TRM-002 says three worlds share the numeric Body/Gap signature 4=3+1.

TRM-003 says the geometric Gap can additionally carry an exact restoration
certificate.

Keep those two claims separate.

If useful, a tiny theorem may note that the atomic certified gap has area 1,
reusing area_hole2, but this is not the central theorem.

## I. Validation

Run focused builds for:

- DkMath.Tromino.Restoration
- DkMathTest.Tromino.RestorationAxiomAudit

Run git diff --check.

Audit substantive public theorems with #print axioms.

Scan new/changed files for:

- sorry
- admit
- unsafe
- new axiom declarations

## J. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-002.md

Record:

- exact generic restoration relation;
- whether restoreShape was added;
- exact GapCrystal / GapFiber adapter shape;
- generic uniqueness theorem;
- atomic block2 / L / hole2 theorem;
- whether complement characterization was proved or deferred;
- build / axiom audit;
- any dependency or Finset API issue.

## Stop condition

Stop when the atomic hole is a certified unique geometric restoring gap through
the existing BookOfMagic infrastructure.

Do not proceed to MacroCell, FourColorCell, rescue, BoundaryIR, graph, or
optimization without review.
