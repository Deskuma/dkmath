
# TRM-009 — Recursive scaled macro levels

## Goal

Generalize the one-level MacroTromino construction into a level-indexed
recursive macro carrier.

TRM-008 established one concrete level:

4 atomic cells
  -> 1 FourColorMacroCell

and then

3 macro payloads + 1 typed macro gap = 4 macro payloads

with total atomic mass 12 + 4 = 16.

TRM-009 should extract the scale law itself:

level k cell
  -> four level k children
  -> one level k+1 cell

and prove the exact atomic mass formula at arbitrary depth.

This checkpoint is about recursive scale and count only.

Do not implement BoundaryIR, graph traversal, residual optimization,
physical flattening into lattice coordinates, or Four Color claims.

## Design recommendation

Prefer a level-indexed recursive type rather than attaching a Nat field to an
unindexed structure.

A good target shape is conceptually:

ScaledMacroCell 0     := FourColorMacroCell
ScaledMacroCell (k+1) := four positions carrying ScaledMacroCell k

The four positions should be represented by a finite four-element type tied to
the existing macro block pattern.

Avoid a recursive structure whose children can have mixed levels.

## A. Block2 position type

Define a finite type representing exactly the four macro positions of block2.

Preferred semantic form:

Block2Pos := {c : Cell // c ∈ block2}

or an equivalent Fin 4 representation with explicit coordinate equivalence.

If using the subtype form, prove:

Nat.card Block2Pos = 4

and identify the unique hole2 position / the three L_tromino positions by
membership predicates.

Prefer reuse of the existing geometric constants over a duplicated custom
enumeration.

## B. Level-indexed recursive carrier

Define a recursive family equivalent to:

def ScaledMacroCell : Nat -> Type
| 0       => FourColorMacroCell
| k + 1   => Block2Pos -> ScaledMacroCell k

If Lean elaboration is cleaner with an inductive family, that is acceptable,
but preserve the invariant:

all children of a level k+1 cell are level k cells.

Do not store redundant level numbers inside values.

## C. Canonical recursive cell

Define:

canonicalScaledMacroCell : (k : Nat) -> ScaledMacroCell k

with:

- level 0 = atomicFourColorMacroCell;
- level k+1 = constant four-child frame filled with canonical level k cells.

This is the recursive generalization of canonicalMacroFrame.

## D. Child / body / gap observers

For level k+1, define observers corresponding to:

- all four child positions;
- the three L_tromino body positions;
- the one hole2 gap position.

Do not immediately create a new general restoration framework.

It is enough to define:

bodyPositions : Finset Block2Pos
gapPositions  : Finset Block2Pos

or equivalent predicates/finite sets.

Required cardinal facts:

bodyPositions.card = 3
gapPositions.card = 1
bodyPositions ∪ gapPositions = univ
Disjoint bodyPositions gapPositions

Reuse L_tromino / hole2 geometry wherever practical.

## E. Recursive atomic mass

Define atomic mass by recursion:

- level 0:
  atomicMass M = atomicCellCount M;
- level k+1:
  atomicMass M = sum over four child positions of atomicMass (M p).

Then prove the general closed form:

atomicMass (M : ScaledMacroCell k) = 4^(k+1)

for every M.

This theorem should not require canonicity: every level-0 payload has
atomicCellCount = 4, so every level-k object has the same total atomic count.

Equivalent exponent normalization is acceptable if Lean prefers:

atomicMass M = 4 * 4^k.

Expose both forms only if useful.

## F. Recursive Body/Gap mass split

For M : ScaledMacroCell (k+1), define:

bodyAtomicMass M :=
  sum over bodyPositions of atomicMass child

gapAtomicMass M :=
  sum over gapPositions of atomicMass child

Prove:

bodyAtomicMass M = 3 * 4^(k+1)

gapAtomicMass M  =     4^(k+1)

atomicMass M     = 4 * 4^(k+1)

and therefore:

bodyAtomicMass M + gapAtomicMass M = atomicMass M.

This is the arbitrary-level form of:

12 + 4 = 16.

Also expose the macro-position count law:

3 + 1 = 4.

## G. Scaled Tromino law

Package the previous theorem into one user-facing statement.

Desired mathematical reading:

At every successor level,

~~~text
3 lower-level macro units
+ 1 typed residual macro unit
= 4 lower-level macro units
= 1 higher-level macro unit.
~~~

The count theorem may be stated without introducing a new record if a tuple of
equalities is simpler.

Do not claim boundary equivalence or coloring solvability.

## H. Canonical calibration

For k = 0 / level 1, prove that the recursive mass theorem reproduces the
existing TRM-008 values:

body = 12
gap = 4
total = 16.

If practical, bridge the canonical level-1 recursive cell to
canonicalMacroFrame componentwise.

Do not force structural equality if the representations differ and a thin
calibration theorem is cleaner.

## I. Exchange action

Define a recursive uniform exchange:

exchangeScaledMacroCell : TrominoState -> ScaledMacroCell k -> ScaledMacroCell k

by:

- level 0: exchangeFourColorMacroCell;
- successor: pointwise recurse through all children.

Prove:

- zero exchange identity;
- involutive exchange;
- atomicMass preserved.

If straightforward, prove canonical orbit injectivity at every level by
reducing to any child / ultimately to level 0.

Do not add GL(2,2), affine color symmetry, or spatial D4 yet.

## J. Typed-gap interpretation boundary

At successor level, the unique hole position carries one full
ScaledMacroCell k.

That child is the recursive typed residual.

For this checkpoint, it is acceptable to expose the gap child directly rather
than creating a new dependent GapCrystal layer.

Record the interpretation:

gap at level k+1 has the same payload type as each body child, namely
ScaledMacroCell k.

This is exactly the type-level statement that the gap knows the scale of what
must return.

A BookOfMagic dependent adapter may be considered later, after the recursive
carrier stabilizes.

## K. No physical flattening yet

Do not map level k cells to a physical 2^(k+1) by 2^(k+1) lattice Shape in this
checkpoint.

Mass/count recursion is sufficient.

Physical coordinate flattening requires a separate embedding/scaling design
and should not contaminate the recursive carrier.

## L. Computability

Keep all data definitions computable.

No new noncomputable declaration should be necessary.

If finite subtype enumeration for Block2Pos creates a classical dependency,
prefer an explicit finite equivalence / Fin 4 representation rather than
making the recursive solver noncomputable.

## M. Regression tests

Audit at least:

1. card Block2Pos = 4;
2. bodyPositions.card = 3;
3. gapPositions.card = 1;
4. level 0 canonical atomicMass = 4;
5. level 1 canonical atomicMass = 16;
6. level 2 canonical atomicMass = 64;
7. level 1 body/gap masses = 12/4;
8. level 2 body/gap masses = 48/16;
9. general body + gap = total theorem;
10. zero exchange and involution at recursive levels;
11. atomicMass preservation under exchange.

## N. Proposed modules

Preferred production:

DkMath/Tromino/RecursiveMacro.lean

Audit:

DkMathTest/Tromino/RecursiveMacroAxiomAudit.lean

Do not refactor MacroTromino.lean unless a small helper theorem is genuinely
needed.

## O. Validation

Run focused builds for:

- DkMath.Tromino.MacroCell
- DkMath.Tromino.MacroTromino
- DkMath.Tromino.RecursiveMacro
- DkMathTest/Tromino/RecursiveMacroAxiomAudit

Run git diff --check.

Audit substantive public theorems with #print axioms.

Scan new/changed files for:

- sorry
- admit
- unsafe
- new axiom
- unintended noncomputable

## P. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-008.md

Record:

- Block2Pos representation;
- ScaledMacroCell representation;
- canonical recursion;
- atomicMass definition;
- closed-form mass theorem;
- body/gap recursive split;
- exchange recursion;
- computability status;
- calibration back to TRM-008;
- any obstacle before boundary signatures.

## Stop condition

Stop once arbitrary recursive levels satisfy the exact scale law

atomicMass(level k) = 4^(k+1)

and every successor level decomposes as

3 lower-level units + 1 typed residual unit = 4 lower-level units.

Do not proceed to physical flattening, BoundaryIR, graph traversal,
residual optimization, or Four Color claims without review.
