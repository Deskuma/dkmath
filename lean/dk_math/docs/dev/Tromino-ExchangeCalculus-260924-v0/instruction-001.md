
# TRM-002 — Three-way Body/Gap calibration

## Goal

Connect the newly completed four-state exchange kernel to the existing
geometric Tromino and CosmicFormula decomposition without making any of the
three layers own the others.

The central observation is that all three expose the same finite additive
signature:

- state layer: 4 states = 3 waiting + 1 current;
- geometry layer: block2 area 4 = L-tromino area 3 + hole area 1;
- CosmicFormula layer at d=2, x=u=1: Big 4 = Body 3 + Gap 1.

Use DkMath.CosmicFormula.Mass.BodyGapSplit Nat as the neutral record that
stores the additive signature.

## Scope

Implement only this calibration bridge.

Do not start:

- exchange rescue;
- forbidden sets;
- GapCrystal adapters;
- macro-cell recursion;
- BoundaryIR;
- transition graphs;
- residual optimization;
- Four Color claims.

## Existing owners

Reuse without duplication:

- DkMath.Tromino.State
- DkMath.Tromino.Exchange
- DkMath.Polyomino.Tromino.area_block2_eq_area_L_add_area_hole
- DkMath.Polyomino.Tromino.area_block2
- DkMath.Polyomino.Tromino.area_L_tromino
- DkMath.Polyomino.Tromino.area_hole2
- DkMath.CosmicFormula.Mass.BodyGapSplit
- DkMath.CosmicFormula.CoreBeamGap.big_eq_body_add_gap
- DkMath.CosmicFormulaBinom.BodyN

Keep NumberGeometry out of the dependency graph.

## Proposed module

DkMath/Tromino/CosmicBridge.lean

Test/audit:

DkMathTest/Tromino/CosmicBridgeAxiomAudit.lean

## A. State split

Construct a BodyGapSplit Nat representing the exchange state count.

Conceptually:

state big  := Nat.card TrominoState
state body := card (waitingStates x)
state gap  := 1

The stored split should follow from card_state and card_waitingStates.

A current state x is not identified with the algebraic zero state.  The gap
here is the cardinality of the distinguished current slot, not the value zero.

If useful and dependency-clean, define a singleton current-state finset and
use its cardinality instead of a literal 1.  Do not add this merely for
notation if it complicates the API.

Target projections/calibration:

- state split big = 4
- state split body = 3
- state split gap = 1

## B. Geometric split

Construct a BodyGapSplit Nat using the existing geometric area theorem.

Conceptually:

geometric big  := area block2
geometric body := area L_tromino
geometric gap  := area hole2

The split certificate must be the existing
area_block2_eq_area_L_add_area_hole theorem, not a recomputed norm_num proof.

Target projections:

- geometric big = 4
- geometric body = 3
- geometric gap = 1

Do not alter DkMath/Tromino.lean.

## C. Cosmic unit-square split

Construct or expose a BodyGapSplit Nat for:

d = 2
x = 1
u = 1

Use the existing owner theorem big_eq_body_add_gap.

Target values:

- CoreBeamGap.Big 2 1 1 = 4
- CosmicFormulaBinom.BodyN 2 1 1 = 3
- CoreBeamGap.Gap 2 1 = 1

Prefer deriving Body = 3 from the stored Big = Body + Gap theorem plus the
easy Big/Gap evaluations instead of unfolding GN/GTail internals.

This keeps the bridge attached to the public conservation identity.

## D. Three-way calibration theorem

Expose exact equality of the three numeric signatures.

Preferred result shape is either:

1. equality of the three BodyGapSplit packets, if structure extensionality is
   clean; or
2. explicit componentwise equalities for big/body/gap, if packet equality
   creates proof-field noise.

Required semantic content:

state big = geometric big = cosmic big = 4
state body = geometric body = cosmic body = 3
state gap = geometric gap = cosmic gap = 1

Also expose at least one user-facing theorem expressing:

Nat.card TrominoState
  = card (waitingStates x) + 1

and identify this with the geometric/cosmic 3+1 split.

Do not claim that state space, polyomino geometry, and CosmicFormula are
isomorphic objects.  This checkpoint proves an exact shared additive
calibration only.

## E. Important interpretation boundary

The theorem should support the statement:

"The Tromino exchange carrier, the 2x2 L-plus-hole geometry, and the degree-two
unit CosmicFormula all have the same Body/Gap cardinal signature 4 = 3 + 1."

It must not support stronger unstated claims such as:

- geometric equivalence of all three worlds;
- a map-coloring theorem;
- recursive substitution completeness;
- uniqueness of the CosmicFormula interpretation.

## F. Validation

Run focused builds for:

- DkMath.Tromino.CosmicBridge
- DkMathTest.Tromino.CosmicBridgeAxiomAudit

and git diff --check.

Audit substantive bridge theorems with #print axioms.

Scan new/changed files for sorry, admit, unsafe, and new axiom declarations.

## G. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-001.md

Record:

- exact imports;
- definitions added;
- three split constructions;
- public calibration theorem surface;
- whether packet equality or componentwise equality was chosen and why;
- build and axiom-audit results;
- any dependency problem.

## Stop condition

Stop after the exact 4 = 3 + 1 three-way calibration.

TRM-003 will separately decide how GapCrystal should represent typed
restoration.  Do not pull that layer into this checkpoint.
