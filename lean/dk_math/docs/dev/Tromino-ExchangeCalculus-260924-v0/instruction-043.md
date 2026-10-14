# TRM-044 — Face-star cyclic rotation and triangular face dynamics

## Goal

Build the first genuinely geometric/combinatorial layer on top of the now
completed actual-port calibration.

TRM-043 established exact actual-port formulas for:

- crossing;
- local rotation;
- all three concrete port constructors.

TRM-044 must now prove:

1. old-region cyclicity;
2. face-center cyclicity;
3. a full PortRotationSystem;
4. the exact 3-step face-step cycle;
5. primitive face return = 3;
6. every face cell of the local rotation/crossing pair has cardinality 3.

Do not construct the connected PortCombinatorialMap yet.
Do not prove Euler/genus/coloring reduction yet.

This checkpoint is deliberately limited to local/global rotation-orbit
structure and triangular face dynamics.

## Read first

Read only:

- CURRENT_STATE.md;
- this instruction;
- DkMath/Tromino/PortTriangulationReduction.lean;
- DkMath/Tromino/PortRotationSystem.lean;
- DkMath/Tromino/PortFaceOrbit.lean;
- DkMath/Tromino/PortFaceCell.lean or the exact module defining PortFaceCell,
  only as needed.

Do not re-read the full Tromino branch.

## Existing verified base

Reuse as fixed:

- faceStarPortEquiv
- faceStarPortEncode / Decode
- faceStarCrossing
- faceStarLocalRotation
- faceStarCross_oldEdge
- faceStarCross_radialOld
- faceStarCross_radialCenter
- faceStarRotate_radialOld
- faceStarRotate_oldEdge
- faceStarRotate_radialCenter
- original M.rotation.cyclic
- portFaceEquiv / portFaceStep
- portFaceOrbit_* theorems
- faceCellOfPort and PortFaceCell orbit APIs.

## A. Old-region port classification

For a fixed old region r, prove every actual face-star port q with:

    q.1 = oldRegion I r

is exactly one of:

    faceStarOldEdgePort I p
    faceStarRadialOldPort I p

for a unique old port p with p.1 = faceStarVertexToOld r.

A semantic route through faceStarPortDecode is preferred.

Expose a useful eliminator theorem, for example:

    faceStar_port_at_oldRegion_cases

that returns the relevant p and constructor form.

Do not expose dependent cast internals.

## B. Center-region port classification

For a fixed face cell F, prove every actual face-star port q with:

    q.1 = faceCenterRegion I F

is exactly:

    faceStarRadialCenterPort I p

for some p ∈ F.val.

Again prefer semantic decode + source classification.

Expose a reusable theorem:

    faceStar_port_at_centerRegion_cases.

## C. Old-region iterate formulas

Prove the interleaved rotation iterate laws.

Preferred canonical starting point: radialOld.

For p an old port and n : Nat:

    rotate^[2*n] (radialOld p)
      =
    radialOld ((M.localRotation.rotate^[n]) p)

    rotate^[2*n+1] (radialOld p)
      =
    oldEdge ((M.localRotation.rotate^[n]) p)

Equivalent variants are acceptable if cleaner.

Also derive the corresponding oldEdge formulas.

The proof should be induction using the exact TRM-043 rotation formulas.

## D. Old-region cyclicity

Prove:

    faceStar_oldRegion_cyclic

For every old region r and any two local port indices i j in the new network
over oldRegion I r, there exists n such that the face-star rotation reaches
the second from the first.

Recommended proof:

1. classify both endpoints via section A;
2. use original M.rotation.cyclic on the underlying old ports;
3. choose either 2*n or 2*n+1 depending on the source/target constructor
   parity.

Do not finite-enumerate arbitrary arity.

## E. Face-center backward reachability

Let:

    phi := portFaceEquiv M.localRotation M.crossing.

For any p q in the same old face cell F, prove:

    exists n,
      (phi.symm^[n]) p = q.

Use existing face-orbit reachability rather than cardinality-only reasoning.

Suggested route:

- from q ∈ F and p ∈ F obtain same old face orbit;
- use portFaceOrbit_mem_iff_iterate to get forward phi reachability;
- convert to backward reachability using finite periodicity / reverse orbit /
  equivalence inverse iteration.

Package the theorem independently because it is conceptually useful:

    oldFace_backward_reachable.

## F. Center-region cyclicity

Using section B and E, prove:

    faceStar_centerRegion_cyclic.

At a center region, faceStar rotation is exactly phi.symm on radialCenter
ports by TRM-043.

## G. Package PortRotationSystem

Define:

    faceStarRotationSystem
      (M : PortCombinatorialMap P)
      (I : PortFaceStarIndexing M) :
      PortRotationSystem (faceStarNetwork M I)

with:

    toPortLocalRotation := faceStarLocalRotation I

and cyclicity proved by region cases:

- oldRegion -> D;
- faceCenterRegion -> F.

This is mandatory.

## H. Exact face-step formulas

Let:

    newR := (faceStarRotationSystem M I).toPortLocalRotation
    newC := faceStarCrossing I
    phi  := portFaceStep M.localRotation M.crossing.

Prove exact formulas:

    @[simp] theorem faceStarFaceStep_oldEdge :
      portFaceStep newR newC
        (faceStarOldEdgePort I p)
      =
      faceStarRadialOldPort I (phi p).

    @[simp] theorem faceStarFaceStep_radialOld :
      portFaceStep newR newC
        (faceStarRadialOldPort I (phi p))
      =
      faceStarRadialCenterPort I p.

    @[simp] theorem faceStarFaceStep_radialCenter :
      portFaceStep newR newC
        (faceStarRadialCenterPort I p)
      =
      faceStarOldEdgePort I p.

Derive these only from exact crossing/rotation formulas plus the definition
of portFaceStep.

## I. Three-step return

Prove:

    (portFaceStep newR newC)^[3]
      (faceStarOldEdgePort I p)
      =
    faceStarOldEdgePort I p.

Also prove the corresponding 3-step return for radialOld and radialCenter.

## J. No return at step 1 or 2

Use constructor disjointness through faceStarPortDecode / semantic tags:

- oldEdge != radialOld;
- oldEdge != radialCenter;
- radialOld != radialCenter.

Prove for each canonical triangle member that return at step 1 and step 2 is
impossible.

Do not use arithmetic/cardinality shortcuts.

## K. Primitive return = 3

Prove:

    firstPortFaceReturn newR newC
      (faceStarOldEdgePort I p) = 3.

Prefer:

- firstPortFaceReturn_min with the 3-step return;
- primitive/no-return arguments for 1 and 2;
- omega for the final Nat squeeze.

Then derive the same theorem for radialOld and radialCenter, either directly or
using firstPortFaceReturn_eq_of_mem.

## L. Canonical triangle

Define:

    faceStarTriangle M I p : Finset (PortNetworkPort (faceStarNetwork M I))

as:

    {
      faceStarOldEdgePort I p,
      faceStarRadialOldPort I (phi p),
      faceStarRadialCenterPort I p
    }.

Prove:

    faceStarTriangle_card = 3.

Then prove:

    portFaceOrbit newR newC
      (faceStarOldEdgePort I p)
      =
    faceStarTriangle M I p.

Use the first-return=3 theorem and the three exact step formulas.

## M. Orbit equality from all three members

Prove:

    portFaceOrbit ... (radialOld (phi p)) = faceStarTriangle M I p

and:

    portFaceOrbit ... (radialCenter p) = faceStarTriangle M I p.

These should follow via portFaceOrbit_eq_of_mem rather than recomputing.

## N. Every actual port lies in a canonical triangle

Using faceStarPortDecode cases prove:

    forall q : PortNetworkPort (faceStarNetwork M I),
      exists p : PortNetworkPort P,
        q ∈ faceStarTriangle M I p.

Cases:

- oldEdge p -> triangle p;
- radialCenter p -> triangle p;
- radialOld q -> triangle (phi.symm q).

For the radialOld case use:

    phi (phi.symm q) = q.

## O. Every face cell has cardinality 3

Prove the local theorem:

    faceStar_everyFaceCell_card_three :
      forall F : PortFaceCell
        (faceStarRotationSystem M I).toPortLocalRotation
        (faceStarCrossing I),
      F.val.card = 3.

Proof:

1. obtain a representative actual port q for F using the face-cell/orbit API;
2. use section N to place q in some canonical triangle;
3. identify F with that canonical port face orbit;
4. use L/M to conclude card 3.

This theorem must not depend on a PortCombinatorialMap wrapper.

## P. Optional local triangular predicate

If useful, define a local predicate independent of PortCombinatorialMap:

    AllPortFaceCellsCardThree R C : Prop :=
      forall F : PortFaceCell R C, F.val.card = 3.

Then prove it for faceStarRotationSystem/faceStarCrossing.

Do not change existing PortAllFacesTriangular unless necessary.

## Q. Safety / scope

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- new noncomputable production declaration.

No:

- connectivity proof;
- PortCombinatorialMap construction;
- Euler/genus count theorem;
- coloring restriction;
- universal four-color target equivalence.

Those belong to the next checkpoint.

## R. Audit

Create or extend:

    DkMathTest/Tromino/PortFaceStarTriangularAxiomAudit.lean

Audit at least:

1. old-region classification;
2. center-region classification;
3. old-region iterate law;
4. old-region cyclicity;
5. old-face backward reachability;
6. center-region cyclicity;
7. faceStarRotationSystem;
8. three exact face-step formulas;
9. three-step return;
10. no return at step 1;
11. no return at step 2;
12. first return = 3;
13. canonical triangle card = 3;
14. canonical triangle equals face orbit;
15. same orbit from radialOld;
16. same orbit from radialCenter;
17. every actual port lies in some canonical triangle;
18. every face cell has card 3.

Run #print axioms on:

- faceStarRotationSystem;
- one cyclicity theorem;
- faceStarFaceStep_oldEdge;
- firstPortFaceReturn=3 theorem;
- faceStar_everyFaceCell_card_three.

## S. Validation

Build:

- DkMath.Tromino.PortTriangulationReduction
- DkMathTest.Tromino.PortFaceStarTriangularAxiomAudit

Regression-build:

- DkMath.Tromino.PortFaceStarSubdivision
- DkMath.Tromino.PortRotationSystem
- DkMath.Tromino.PortFaceOrbit
- DkMath.Tromino.PortCombinatorialMap

Run:

- git diff --check;
- production forbidden-construct scan;
- #print axioms audit.

## T. Report

Create:

    docs/dev/Tromino-ExchangeCalculus-260924-v0/report-043.md

Record:

- old/center cyclicity strategy;
- backward face-orbit reachability;
- exact face-step 3-cycle;
- primitive return = 3;
- canonical triangle;
- every face-cell-card=3 theorem;
- build/axiom results.

If all mandatory sections A–O are implemented, report:

    Outcome A — face-star rotation/triangular dynamics complete.

## Final acceptance audit

Before reporting completion, re-read this instruction and make an internal
table:

    requirement | theorem/definition | status.

A successful local build is not enough.

If any mandatory item A–O is missing, report Outcome P and identify the exact
missing theorem.

## Stop condition

Stop once the face-star local rotation has been promoted to a
PortRotationSystem and every face cell of the resulting rotation/crossing pair
is kernel-checked to have exactly three ports.

Do not proceed to connectivity, PortCombinatorialMap, Euler/genus,
coloring restriction, or universal targets.
