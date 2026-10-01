# TRM-040 — Face-star subdivision / triangulation reduction

## Goal

Reduce arbitrary connected genus-zero Port combinatorial maps to an
all-triangular genus-zero Port combinatorial map by a purely combinatorial
face-star subdivision.

Do not use geometric planarity or topological realization.

For every old face orbit F:

- add one new center region c_F;
- for every old boundary dart p in F, add one radial edge from source(p) to
  c_F;
- keep every old crossing edge;
- choose the new local rotations so that each old dart p generates one new
  triangular face.

The intended triangle is:

    oldEdge(p)
      -> radialOld(faceStep p)
      -> radialCenter(p)
      -> oldEdge(p).

The key global count is:

    V' = V + F
    D' = 3D
    E' = E + D = 3E
    F' = D = 2E

and therefore:

    chi' = chi.

For genus zero, the subdivided map is again genus zero and all its faces are
triangular.

Finally prove that any proper four-state coloring of the subdivided map
restricts to a proper four-state coloring of the original map.  Therefore the
universal Four-Color target is equivalent to its all-triangular restriction.

This checkpoint is a reduction theorem only.  It does not prove colorability
of the triangular target.

## Production files

Create:

- DkMath/Tromino/PortFaceStarSubdivision.lean
- DkMath/Tromino/PortTriangulationReduction.lean

The first file builds and audits the structural subdivision.
The second file proves genus/coloring/target reduction results.

## A. Explicit indexing package

PortNetwork regions are Fin-indexed, while old face cells are an arbitrary
finite subtype.  Keep production definitions computable by requiring an
explicit indexing package.

Define:

    structure PortFaceStarIndexing (M : PortCombinatorialMap P) where
      faceEquiv :
        PortFaceCell M.localRotation M.crossing ≃ Fin M.faceCount
      facePortEquiv :
        ∀ F : PortFaceCell M.localRotation M.crossing,
          {p : PortNetworkPort P // p ∈ F.val} ≃ Fin F.val.card

The second equivalence gives a computable local index for center-side radial
ports.

Prove an existence theorem:

    Nonempty (PortFaceStarIndexing M).

This theorem may use classical finite equivalences inside the proof.

Do not introduce a noncomputable production definition selecting an indexing.

All subdivision constructors take an explicit indexing argument I.

## B. Semantic port descriptor

Before encoding into dependent Fin arities, define a semantic three-way port
type:

    inductive FaceStarPortDesc (M : PortCombinatorialMap P)
    | oldEdge      (p : PortNetworkPort P)
    | radialOld    (p : PortNetworkPort P)
    | radialCenter (p : PortNetworkPort P)

Interpretation:

- oldEdge p is the old edge dart at source(p);
- radialOld p is the old-region endpoint of the radial edge associated with p;
- radialCenter p is the center-region endpoint of the same radial edge.

Provide Fintype / DecidableEq.

Prove:

    card FaceStarPortDesc = 3 * M.portCount.

This semantic carrier should be used for almost all crossing/rotation proofs.

## C. New regions and arities

For I : PortFaceStarIndexing M define:

    faceStarNetwork M I : PortNetwork

with:

    regionCount = M.vertexCount + M.faceCount.

Regions split into:

1. old regions:
       oldRegion r
   for r : Fin M.vertexCount;

2. face-center regions:
       faceCenterRegion F
   for F : PortFaceCell M.localRotation M.crossing.

Required injectivity/disjointness:

    oldRegion_injective
    faceCenterRegion_injective
    oldRegion_ne_faceCenterRegion.

Arities:

- oldRegion r has arity:
      2 * P.arity r;

- faceCenterRegion F has arity:
      F.val.card.

At an old region, the two local slots associated with old port p are:

    oldEdge p
    radialOld p.

At a face center F, local slots enumerate:

    radialCenter p
    for p ∈ F.val

using I.facePortEquiv F.

Use a stable Mathlib Fin-product/sum equivalence where possible rather than
manual modulo arithmetic.

## D. Descriptor/actual-port equivalence

Construct a computable equivalence:

    faceStarPortEquiv M I :
      PortNetworkPort (faceStarNetwork M I)
        ≃
      FaceStarPortDesc M.

Expose constructors on actual ports:

    faceStarOldEdgePort M I p
    faceStarRadialOldPort M I p
    faceStarRadialCenterPort M I p

and prove the expected inverse/descriptor calibration theorems.

All structural operations should preferably be defined on
FaceStarPortDesc and transported through this equivalence.

## E. Crossing involution

On descriptors define:

    oldEdge p
      <-> oldEdge (M.crossing.cross p)

    radialOld p
      <-> radialCenter p.

Transport this to:

    faceStarCrossing M I :
      PortCrossing (faceStarNetwork M I).

Prove:

- involutive;
- changesRegion;
- exact crossing formulas for all three descriptor constructors.

For the radial case, changesRegion follows from the old-region / face-center
partition, so bridges/repeated face vertices cause no loop problem.

Old-edge crossing retains the original crossing.

## F. Semantic rotation

Let:

    alpha := M.crossing.cross
    rho   := M.localRotation.rotate
    phi   := portFaceStep M.localRotation M.crossing
           = rho ∘ alpha.

Define descriptor rotation:

At old regions:

    radialOld p  -> oldEdge p
    oldEdge p    -> radialOld (rho p).

At face-center regions:

    radialCenter p
      ->
    radialCenter ((portFaceEquiv M.localRotation M.crossing).symm p).

The center rotation is therefore phi^{-1} around the old face orbit.

Transport this to an actual-port equivalence:

    faceStarRotationEquiv M I.

Package:

    faceStarLocalRotation M I : PortLocalRotation ...
    faceStarRotationSystem M I : PortRotationSystem ...

Required theorems:

- rotation preserves each new region;
- old-region rotation is cyclic because the original rho is cyclic;
- center-region rotation is cyclic because a PortFaceCell is one phi-orbit.

No topological orientation claim is needed.

## G. New triangular face step

Prove the three exact face-step formulas.

For every old port p:

1.

    newFaceStep (oldEdge p)
      =
    radialOld (phi p).

2.

    newFaceStep (radialOld (phi p))
      =
    radialCenter p.

3.

    newFaceStep (radialCenter p)
      =
    oldEdge p.

Hence:

    newFaceStep^[3] (oldEdge p) = oldEdge p.

Also prove there is no return at step 1 or 2, so:

    firstPortFaceReturn newR newC (oldEdge p) = 3.

The same primitive period 3 should hold for the other two ports in that
triangle.

## H. Canonical star triangle

Define:

    faceStarTriangle M I p : Finset (new ports)

with exactly:

    oldEdge p,
    radialOld (phi p),
    radialCenter p.

Prove:

- card = 3;
- it is exactly the new port face orbit of oldEdge p;
- the same triangle is obtained from each of its three member ports.

Then prove every new port belongs to one such triangle:

- oldEdge p -> triangle p;
- radialCenter p -> triangle p;
- radialOld q -> triangle (phi^{-1} q).

Hence every new face cell has cardinality 3.

Main structural theorem:

    faceStar_allFacesTriangular :
      PortAllFacesTriangular (faceStarCombinatorialMap M I).

## I. Port-count theorem

Use faceStarPortEquiv to prove:

    (faceStarNetwork M I).portCount = 3 * M.portCount.

Do not count by ad hoc arithmetic on dependent arities if the descriptor
equivalence already gives this directly.

## J. Face-count theorem

Since every old dart p yields one triangle and triangle equality follows
exactly from p equality, prove a bijection:

    PortNetworkPort P
      ≃
    PortFaceCell newR newC.

Preferred map:

    p |-> faceCellOfPort newR newC (oldEdge p).

Prove injectivity using the unique oldEdge member of each canonical triangle.
Prove surjectivity from section H.

Conclude:

    new faceCount = old portCount.

This is:

    F' = D.

## K. Edge-count theorem

Use the general Port identity:

    portCount = 2 * edgeCount

for old and new maps together with:

    D' = 3D

and:

    D = 2E

to derive:

    new edgeCount = 3 * old edgeCount.

Also expose the equivalent form:

    new edgeCount = old edgeCount + old portCount.

Avoid manually enumerating new crossing-edge orbits unless it materially
simplifies the proof.

## L. Vertex-count theorem

By definition:

    new vertexCount = old vertexCount + old faceCount.

Expose this as a theorem.

## M. Euler characteristic preservation

Combine J/K/L to prove:

    faceStar_eulerCharacteristic :
      new.eulerCharacteristic = M.eulerCharacteristic.

Use Int-safe casts explicitly.

The intended arithmetic is:

    V' - E' + F'
      =
    (V + F) - 3E + 2E
      =
    V - E + F.

No topology is involved.

## N. Connectedness

Construct:

    faceStarCombinatorialMap
      (M : PortCombinatorialMap P)
      (I : PortFaceStarIndexing M) :
      PortCombinatorialMap (faceStarNetwork M I).

Connectivity proof:

1. any two old regions are connected using the lifted original PortRegionWalk
   along oldEdge ports;

2. each face center F is connected by one radial edge to an old region:
   choose any p ∈ F.val inside the proof;

3. combine through an old-region base.

Provide helper:

    liftOldPortRegionWalk

mapping each old walk edge p to oldEdge p.

No noncomputable production path selector is needed.

## O. Genus preservation

Define:

    faceStarGenusZero
      (G : PortGenusZeroCombinatorialMap P)
      (I : PortFaceStarIndexing G.map) :
      PortGenusZeroCombinatorialMap (faceStarNetwork G.map I).

Proof:

- faceStarCombinatorialMap;
- Euler characteristic preservation;
- reuse G.genusZero.

Thus every genus-zero map has a genus-zero all-triangular face-star
subdivision.

## P. Old-region embedding in the new region graph

For every original crossing port p prove:

    the new oldEdge port for p crosses from
      oldRegion p.1
    to
      oldRegion (C.cross p).1.

Hence any old adjacency is also an adjacency between embedded old regions in
the subdivided region graph.

Expose:

    faceStar_old_adj

or an equivalent theorem in terms of portRegionSimpleGraph adjacency.

## Q. Restriction of a coloring

Given:

    K :
      (portRegionSimpleGraph (faceStarCrossing M I)).Coloring TrominoState

define:

    restrictFaceStarColoring M I K :
      (portRegionSimpleGraph M.crossing).Coloring TrominoState

by:

    r |-> K (oldRegion r).

Prove properness using section P.

Then:

    faceStar_colorable_imp_original :
      PortFourStateColorable (faceStarCrossing M I)
        ->
      PortFourStateColorable M.crossing.

Important:

Do NOT prove or claim the converse for a fixed M.
An arbitrary original 4-coloring need not extend to the added face centers.

The reduction only needs subdivided-colorable -> original-colorable.

## R. Existential subdivision without a fixed indexing

Prove:

    exists_faceStarGenusZeroTriangulation
      (G : PortGenusZeroCombinatorialMap P) :
      exists P' (G' : PortGenusZeroCombinatorialMap P'),
        PortAllFacesTriangular G'.map /\
        (PortFourStateColorable G'.map.crossing ->
          PortFourStateColorable G.map.crossing).

Inside the proof choose:

    I : PortFaceStarIndexing G.map

from section A.

This theorem is the clean indexing-free public reduction surface.

## S. Universal all-triangular target

Define:

    PortGenusZeroTriangularFourColorTarget : Prop :=
      forall (P : PortNetwork) (G : PortGenusZeroCombinatorialMap P),
        PortAllFacesTriangular G.map ->
        PortFourStateColorable G.map.crossing.

Prove:

    portGenusZeroTriangularFourColorTarget_iff_fourColorTarget :
      PortGenusZeroTriangularFourColorTarget
        <->
      PortGenusZeroFourColorTarget.

Directions:

- general target -> triangular target is immediate;
- triangular target -> general target:
  use the face-star subdivision G',
  apply the triangular target to G',
  restrict its coloring to G.

This is a genuine reduction theorem, not a Four Color proof.

## T. Universal tetrahedral target

Define:

    PortGenusZeroTriangularTetrahedralTarget : Prop :=
      forall (P : PortNetwork) (G : PortGenusZeroCombinatorialMap P),
        PortAllFacesTriangular G.map ->
        HasTetrahedralFaceAssignment G.map.

Using TRM-039 and section S prove:

    PortGenusZeroTriangularTetrahedralTarget
      <->
    PortGenusZeroFourColorTarget.

Therefore the remaining universal problem can be stated entirely on
all-triangular genus-zero maps:

    every triangular face must receive A/B/C exactly once.

Do not prove this target.

## U. Count regression

Audit the general formulas on existing fixtures.

### trianglePortMap

Old:

    V=3, E=3, F=2, D=6.

Face-star expected:

    V'=5
    E'=9
    F'=6
    D'=18
    chi'=2

and all six new faces triangular.

### triangleDualMap

Old:

    V=2, E=3, F=3, D=6.

Expected:

    V'=5
    E'=9
    F'=6
    D'=18
    chi'=2.

These two different old maps intentionally land on equal count vectors; do
not infer map isomorphism from counts.

## V. Relation to tetrahedral rolling

Record the following interpretation but do not add rigid-body geometry.

Each new triangular face of faceStar subdivision is a local three-edge cell.
Under a future tetrahedral assignment, its three edge labels must be exactly:

    deltaA, deltaB, deltaC.

Thus face-star subdivision turns every old face, regardless of its original
length, into a necklace/fan of tetrahedral A/B/C local junctions.

This is the structural board normalization for the future game:

    arbitrary board
      -> face-star triangular board
      -> tetrahedral roll/stamp local rule.

Do not claim an original coloring extends to the star board.

## W. Outcome boundary

Full GREEN requires:

- an actual PortCombinatorialMap face-star construction;
- all-faces-triangular theorem;
- Euler/genus preservation;
- coloring restriction;
- universal triangular target equivalence.

If dependent-Fin encoding becomes the only blocker, do not fake the map.
Report Outcome P and isolate the exact missing port equivalence/indexing API.

The semantic FaceStarPortDesc layer and count proofs may still be retained.

## X. Axiom / computability policy

Subdivision constructors are computable relative to explicit
PortFaceStarIndexing.

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- new noncomputable production declaration.

Classical choice is allowed only inside existence proofs such as the indexing
existence theorem and indexing-free reduction theorem.

## Y. Audit

Create:

DkMathTest/Tromino/PortFaceStarSubdivisionAxiomAudit.lean

Audit at least:

1. indexing package existence;
2. descriptor card = 3D;
3. old/center region disjointness;
4. descriptor/actual-port equivalence;
5. crossing formulas and involutivity;
6. old rotation formulas;
7. center inverse-face-step rotation formula;
8. rotation cyclicity;
9. all three new face-step formulas;
10. primitive face period = 3;
11. canonical triangle card = 3;
12. canonical triangle = new face orbit;
13. every new face triangular;
14. new portCount = 3D;
15. new faceCount = D;
16. new edgeCount = 3E = E+D;
17. new vertexCount = V+F;
18. Euler characteristic preservation;
19. connectivity;
20. genus-zero preservation;
21. old adjacency embedding;
22. coloring restriction;
23. indexing-free triangulation existence;
24. universal triangular target iff four-color target;
25. universal triangular tetrahedral target iff four-color target;
26. triangle fixture count regression;
27. triangle-dual fixture count regression.

Run #print axioms on the principal construction/reduction endpoint theorems.

## Z. Validation

Build:

- DkMath.Tromino.PortFaceStarSubdivision
- DkMath.Tromino.PortTriangulationReduction
- DkMathTest/Tromino/PortFaceStarSubdivisionAxiomAudit

Regression-build:

- DkMath.Tromino.PortTriangularTetrahedral
- DkMath.Tromino.PortGenusZeroHolonomy
- DkMath.Tromino.PortF2Exactness
- DkMath.Tromino.PortCombinatorialMap
- DkMath.Tromino.PortRotationSystem

Run:

- git diff --check;
- production forbidden-construct scan;
- #print axioms audit.

## Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-039.md

Record:

- semantic three-way star-port carrier;
- explicit indexing design;
- face-star crossing and rotation;
- exact triangular 3-cycle formula;
- V'/E'/F'/D' counts;
- Euler/genus preservation;
- coloring restriction theorem;
- universal triangular reduction equivalence;
- universal triangular tetrahedral target equivalence;
- fixture counts;
- relation to tetrahedral rolling/game normalization;
- exact remaining gap after reduction:
    universal A/B/C assignment existence on all-triangular genus-zero maps.

## Stop condition

Stop once arbitrary genus-zero Port maps are reduced, in kernel-checked
combinatorial form, to all-triangular genus-zero Port maps for the purpose of
four-state colorability.

Do not prove the triangular tetrahedral assignment target, a general dual
PortNetwork constructor, topological realization, rigid tetrahedron
orientation, or the Four Color theorem without review.
