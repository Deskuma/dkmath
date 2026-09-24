
# TRM-000 — Repository-first audit and TRM-001 launch

## Goal

Start the Tromino Exchange Calculus from the current develop branch.

This checkpoint is bounded. Do not begin BoundaryIR, graph search, macro
recursion, optimization, or Four Color work yet.

Determine the exact finite-state representation and, if the audit is clean,
implement the smallest four-state / exchange kernel.

## Base

Repository: Deskuma/dkmath
Branch: research/Tromino-ExchangeCalculus-260924-v0
Base develop HEAD: 11f1762613ce8ca6d971956c18e13077388a202e

Read first:

- README.md
- AGENT.md
- SUMMARY.md
- DkMath/Tromino.lean
- the four Tromino implementation plans in docs/not_implements dated 260912–260913

Also inspect read-only:

- DkMath/CosmicFormula/Mass/BodyGapSplit.lean
- DkMath/CosmicFormula/CoreBeamGap.lean
- DkMath/BookOfMagic/GapCrystal.lean
- DkMath/NumberGeometry/Basic.lean
- DkMath/NumberGeometry/Transport.lean
- DkMath/NumberGeometry/GaugeTransition.lean

The latest NumberGeometry project is context, not an initial dependency.

## A. Audit

Confirm the current Mathlib API around:

- Mathlib.GroupTheory.SpecificGroups.KleinFour
- IsAddKleinFour
- ZMod 2 × ZMod 2

Check whether DkMath already has a production four-state exchange carrier.

Compare:

- ZMod 2 × ZMod 2
- Bool × Bool
- Fin 4

Decision criteria:

- additive exchange law is natural;
- four-state cardinality is easy;
- three nonzero/waiting states are easy;
- theorem statements remain reusable;
- simp behavior is stable.

Expected default: ZMod 2 × ZMod 2 unless repository evidence gives a better
existing owner.

## B. Minimal implementation

Preferred new files:

- DkMath/Tromino/State.lean
- DkMath/Tromino/Exchange.lean
- DkMathTest/Tromino/ExchangeAxiomAudit.lean

Use namespace DkMath.Tromino.

Do not refactor DkMath/Tromino.lean in this checkpoint.

Candidate API:

TrominoState := ZMod 2 × ZMod 2

waitingStates x := Finset.univ.erase x

exchange delta x := x + delta

Target meanings:

1. state space has cardinality four;
2. waiting set has cardinality three;
3. zero exchange is identity;
4. every exchange is self-inverse;
5. exchange composition is addition;
6. exchange operations commute;
7. every target state has a unique exchange delta from a source;
8. a distinct target requires a nonzero delta;
9. the three nonzero deltas are exactly the three nontrivial exchange choices.

Prefer Mathlib algebra over four-case enumeration when practical.

Do not hard-code color names in the mathematical kernel.

## C. CosmicFormula reconnaissance only

Record whether TRM-002 can expose a BodyGapSplit Nat from

DkMath.Polyomino.Tromino.area_block2_eq_area_L_add_area_hole

and whether degree-two x=u=1 can be calibrated as Big=4, Body=3, Gap=1 using
existing owner theorems.

This is the intended exact bridge between geometric 3+1 and
CosmicFormula Body+Gap=Big.

## D. GapCrystal reconnaissance only

Assess whether DkMath.BookOfMagic.GapCrystal / GapFiber is sufficient for the
future semantics: a removed slot remembers what piece can be restored.

Do not duplicate that abstraction yet.

## E. Validation

Run focused builds for every new production/test module and git diff --check.

Scan new files for axiom, sorry, admit, unsafe.

Report #print axioms accurately.

## F. Report

Create:
docs/dev/Tromino-ExchangeCalculus-260924-v0/report-000.md

Report:

- representation decision;
- Mathlib owner API found;
- production declarations added;
- build results;
- axiom audit;
- CosmicFormula bridge feasibility;
- GapCrystal reuse decision;
- dependency/naming issues.

## Stop condition

Stop after TRM-000 / minimal TRM-001 kernel.

Do not proceed to exchange-rescue, macro-cell, boundary graph, optimization,
or planar coloring without review.
