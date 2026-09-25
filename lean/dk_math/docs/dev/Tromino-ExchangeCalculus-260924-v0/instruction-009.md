
# TRM-010 — Recursive CosmicFormula scale bridge

## Goal

Connect the arbitrary-level Tromino mass recursion from TRM-009 to the
degree-two CosmicFormula at a level-dependent equal scale.

This checkpoint should prove an exact calibration, not an analogy.

For successor level k+1, define the lower-level side scale

s(k) = 2^(k+1).

Then:

s(k)^2 = 4^(k+1),

and the degree-two equal-axis CosmicFormula

d = 2
x = s(k)
u = s(k)

has:

Gap  = `s(k)^2`       = `4^(k+1)`
Body = `3*s(k)^2`     = `3*4^(k+1)`
Big  = `4*s(k)^2`     = `4^(k+2)`.

These are exactly the existing recursive Tromino quantities:

gapAtomicMass k M
bodyAtomicMass k M
atomicMass (k+1) M.

Do not introduce BoundaryIR, graph traversal, physical flattening, residual
optimization, or Four Color claims.

## Existing owners

Reuse:

- DkMath.Tromino.RecursiveMacro
- DkMath.CosmicFormula.CoreBeamGap
- DkMath.CosmicFormula.Mass.BodyGapSplit
- DkMath.CosmicFormulaBinom.BodyN
- atomicMass_eq_pow_succ
- bodyAtomicMass_eq_three_mul_pow
- gapAtomicMass_eq_pow
- body_gap_mass_split

Keep NumberGeometry out of the dependency graph.

## Proposed production module

DkMath/Tromino/RecursiveCosmicBridge.lean

Audit:

DkMathTest/Tromino/RecursiveCosmicBridgeAxiomAudit.lean

## A. Level side scale

Define a natural-number scale:

macroSideScale (k : Nat) : Nat := 2 ^ (k + 1)

This is the side-length scale whose square equals the atomic mass of one
level-k child.

Prove:

macroSideScale k ^ 2 = 4 ^ (k + 1).

Prefer a generic power identity proof over induction if Mathlib makes that
clean.

Also expose:

macroSideScale 0 = 2
macroSideScale 1 = 4

as regression facts if useful.

## B. Recursive BodyGapSplit packet

For M : ScaledMacroCell (k+1), package the already-proved recursive quantities
into:

recursiveMassSplit k M : BodyGapSplit Nat

with:

big  := atomicMass (k+1) M
body := bodyAtomicMass k M
gap  := gapAtomicMass k M

and split certificate := body_gap_mass_split k M.

This should be a thin owner bridge, not a reproof.

## C. Cosmic level packet

Define the level-k degree-two equal-scale CosmicFormula packet:

recursiveCosmicSplit k : BodyGapSplit Nat

with:

big  := CoreBeamGap.Big  2 (macroSideScale k) (macroSideScale k)
body := CosmicFormulaBinom.BodyN 2 (macroSideScale k) (macroSideScale k)
gap  := CoreBeamGap.Gap  2 (macroSideScale k)

and split certificate from:

CoreBeamGap.big_eq_body_add_gap.

Do not unfold GN/GTail unless needed for a calibration theorem that cannot be
obtained from the conservation identity.

## D. Cosmic component formulas

Prove:

recursiveCosmicSplit k .gap = 4^(k+1)

recursiveCosmicSplit k .body = 3 * 4^(k+1)

recursiveCosmicSplit k .big = 4^(k+2)

Preferred strategy:

- evaluate Big and Gap using macroSideScale;
- derive Body from Big = Body + Gap whenever practical, following TRM-002.

Avoid a deep GN expansion.

## E. Exact recursive calibration

For every:

M : ScaledMacroCell (k+1)

prove componentwise:

recursiveMassSplit k M .big
  = recursiveCosmicSplit k .big

recursiveMassSplit k M .body
  = recursiveCosmicSplit k .body

recursiveMassSplit k M .gap
  = recursiveCosmicSplit k .gap

Package them in:

recursive_threeWay_cosmic_calibration

or an equivalent user-facing theorem.

Do not force equality of BodyGapSplit structures; componentwise equality is
preferred for the same proof-field reason as TRM-002.

## F. Core / Beam / Gap refinement

At equal scale x=u=s(k), the CosmicFormula refines the Tromino 3+1 split:

~~~text
Core = 1 * 4^(k+1)
Beam = 2 * 4^(k+1)
Gap  = 1 * 4^(k+1)
Big  = 4 * 4^(k+1).
~~~

Prove the numeric formulas:

CoreBeamGap.Core 2 (macroSideScale k) = 4^(k+1)

CoreBeamGap.Beam 2 (macroSideScale k) (macroSideScale k)
  = 2 * 4^(k+1)

CoreBeamGap.Gap 2 (macroSideScale k) = 4^(k+1)

and therefore:

Big = Core + Beam + Gap.

Important interpretation boundary:

This is a **mass/count calibration only**.

Do not identify a specific one of the three L-body macro positions as the
geometric Core or the other two as Beam positions yet. Such a positional
interpretation would require an orientation/boundary convention that does not
exist in the current API.

The allowed statement is:

the body mass `3*m` refines numerically as core mass m + beam mass `2*m`.

## G. Recursive law as scaled unit law

Expose a theorem whose mathematical reading is:

The arbitrary-level Tromino law is the unit 4=3+1 law scaled by

4^(k+1).

Suggested theorem content:

bodyAtomicMass k M = 3 * gapAtomicMass k M

atomicMass (k+1) M = 4 * gapAtomicMass k M

or an equivalent pair.

These follow from the existing general mass formulas and are useful even
without CosmicFormula terminology.

This gives:

3G + G = 4G

with G = 4^(k+1).

## H. Calibration back to previous checkpoints

Regression/calibration:

k=0:
side scale = 2
Gap = 4
Body = 12
Big = 16

matching TRM-008.

k=1:
side scale = 4
Gap = 16
Body = 48
Big = 64

matching TRM-009 level 2.

Note carefully that TRM-002 used d=2, x=u=1 to calibrate the unscaled
signature 4=3+1. TRM-010 begins from successor macro levels where one child
already has atomic mass 4, hence k=0 uses x=u=2.

If useful, also record the conceptual base identity:

d=2, x=u=1
-> 4=3+1

and recursive scale:

multiply the mass by 4^(k+1)
-> 4^(k+2)=3*4^(k+1)+4^(k+1).

Do not alter CosmicBridge.lean unless a tiny reusable helper is clearly owned
there.

## I. No stronger structural claim

This checkpoint must not claim:

- ScaledMacroCell is isomorphic to a CosmicFormula object;
- Core/Beam/Gap positions have been geometrically identified;
- the recursive coloring structure follows from the CosmicFormula alone;
- boundary compatibility is preserved merely by mass equality.

The exact result is equality of conservation quantities.

## J. Computability

Keep data definitions computable.

No new noncomputable declaration should be required.

## K. Regression tests

Audit at least:

1. macroSideScale 0 = 2;
2. macroSideScale 1 = 4;
3. macroSideScale k ^ 2 = 4^(k+1);
4. recursive mass split packet has existing body/gap/total fields;
5. cosmic split k=0 gives 16/12/4;
6. cosmic split k=1 gives 64/48/16;
7. general componentwise calibration;
8. Core = child mass;
9. Beam = 2 * child mass;
10. Gap = child mass;
11. scaled-unit-law corollaries.

## L. Validation

Run focused builds for:

- DkMath.Tromino.RecursiveMacro
- DkMath.Tromino.RecursiveCosmicBridge
- DkMathTest/Tromino/RecursiveCosmicBridgeAxiomAudit

Run git diff --check.

Audit substantive public theorems with #print axioms.

Scan new/changed files for:

- sorry
- admit
- unsafe
- new axiom
- unintended noncomputable

## M. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-009.md

Record:

- macroSideScale definition;
- square/mass identity;
- recursiveMassSplit;
- recursiveCosmicSplit;
- componentwise calibration;
- Core/Beam/Gap formulas;
- exact scope boundary;
- computability and axiom audit;
- whether this bridge suggests any boundary-signature invariant for the next
  checkpoint.

## Stop condition

Stop once the arbitrary-level recursive Tromino mass split is exactly
calibrated with the degree-two equal-scale CosmicFormula.

Do not proceed to positional Core/Beam assignment, BoundaryIR, graph
traversal, physical flattening, residual optimization, or Four Color claims
without review.
