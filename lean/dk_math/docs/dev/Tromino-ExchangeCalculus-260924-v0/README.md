
# Tromino Exchange Calculus 260924 v0

Status: active research / Lean implementation

Base: develop at 11f1762613ce8ca6d971956c18e13077388a202e
(the merge of PR #107, NumberGeometry TwoPointGauge)

## Purpose

Promote the existing geometric Tromino layer into a reusable finite-state
calculus.

Spine:

geometric 3 + 1
→ four-state kernel
→ Klein-four exchange
→ CosmicFormula Body/Gap calibration
→ typed recoverable gap
→ macro-cell substitution
→ boundary IR / transition graph
→ residual minimization
→ certified restore

The first phase does not attempt the Four Color Theorem, a planar-map solver,
or complexity claims.

## Repository observations

The current DkMath/Tromino.lean remains the geometric owner under
DkMath.Polyomino.Tromino and already proves:

- block2 = L_tromino ∪ hole2
- Disjoint L_tromino hole2
- area block2 = area L_tromino + area hole2
- areas 4, 3, 1
- translation, rotation, reflection invariance

Reusable infrastructure includes:

- Mathlib IsAddKleinFour
- ZMod 2 × ZMod 2 as the intended state carrier candidate
- DkMath.CosmicFormula.Mass.BodyGapSplit
- DkMath.CosmicFormula.CoreBeamGap
- DkMath.BookOfMagic.GapCrystal / GapFiber
- recent DkMath.NumberGeometry transport/gauge APIs

NumberGeometry is architectural context, not an initial dependency.

## Ownership

New algebra namespace: DkMath.Tromino

Existing geometric namespace remains:
DkMath.Polyomino.Tromino

Do not refactor the old geometric file in the first checkpoint.

## Scope boundary

Do not claim yet:

- a new proof of the Four Color Theorem;
- every planar map is recursively Tromino-decomposable;
- every local deadlock has an exchange rescue;
- polynomial/constant-time coloring;
- quantum advantage or quantum irrelevance.

First fix the local algebra and exact bridges.
