# TRM-041 — Face-star crossing/rotation completion and triangulation theorem

## Goal

Complete the partial TRM-040 carrier implementation by turning the existing
face-star network into an actual connected strong Port combinatorial map and
then proving the intended triangulation-reduction theorems.

TRM-040 already established:

- PortFaceStarIndexing and its existence theorem;
- FaceStarPortDesc = oldEdge / radialOld / radialCenter;
- card FaceStarPortDesc = 3 * old port count;
- old-region / face-center region split;
- actual constructors for old-edge, radial-old and radial-center ports.

TRM-041 must complete the missing structural layer:

1. actual-port <-> semantic-descriptor equivalence;
2. crossing involution;
3. cyclic local rotation;
4. exact 3-step triangular face dynamics;
5. PortCombinatorialMap construction and connectivity;
6. V/E/F/D count formulas;
7. Euler/genus preservation;
8. coloring restriction;
9. universal all-triangular reduction equivalence.

Do not change the already verified carrier model unless a genuine defect is
found.

## Production

Continue:

- DkMath/Tromino/PortFaceStarSubdivision.lean
- DkMath/Tromino/PortTriangulationReduction.lean

Extend:

- DkMathTest/Tromino/PortFaceStarSubdivisionAxiomAudit.lean

Create report:

- docs/dev/Tromino-ExchangeCalculus-260924-v0/report-040.md

## A. Decode actual face-star ports

Construct a computable inverse to the already implemented actual-port
constructors.

For an actual port q of faceStarNetwork M I:

1. decode q.1 with finSumFinEquiv.symm;
2. old-region case:
   - cast q.2 back to Fin (2 * P.arity r);
   - decode by finProdFinEquiv.symm;
   - bit 0 -> FaceStarPortDesc.oldEdge p;
   - bit 1 -> FaceStarPortDesc.radialOld p;
3. face-center case:
   - recover F := I.faceEquiv.symm centerIndex;
   - cast q.2 to Fin F.val.card;
   - decode by (I.facePortEquiv F).symm;
   - return FaceStarPortDesc.radialCenter p.

Define:

    faceStarPortDecode M I :
      PortNetworkPort (faceStarNetwork M I) ->
      FaceStarPortDesc M

and semantic encoding:

    faceStarPortEncode M I :
      FaceStarPortDesc M ->
      PortNetworkPort (faceStarNetwork M I)

using the three existing constructors.

Prove:

    faceStarPortDecode_encode
    faceStarPortEncode_decode.

Package:

    faceStarPortEquiv M I :
      PortNetworkPort (faceStarNetwork M I)
        ≃
      FaceStarPortDesc M.

Required simp theorems:

    faceStarPortEquiv_oldEdge
    faceStarPortEquiv_radialOld
    faceStarPortEquiv_radialCenter.

This equivalence is the central missing API.  Do not define crossing/rotation
directly by brittle dependent-Fin arithmetic if the semantic carrier can avoid
it.

## B. Semantic crossing

On FaceStarPortDesc define:

    faceStarCrossDesc :

      oldEdge p
        -> oldEdge (M.crossing.cross p)

      radialOld p
        -> radialCenter p

      radialCenter p
        -> radialOld p.

Prove:

    Function.Involutive faceStarCrossDesc.

Prove the semantic source-region change in descriptor form:

- oldEdge p and oldEdge (cross p) lie in distinct old regions by
  M.crossing.changesRegion;
- radialOld p and radialCenter p lie in the old/center disjoint parts.

Transport through faceStarPortEquiv and define:

    faceStarCrossing M I :
      PortCrossing (faceStarNetwork M I).

Required actual-port formulas:

    faceStarCross_oldEdge
    faceStarCross_radialOld
    faceStarCross_radialCenter.

## C. Semantic rotation

Use the old data:

    rho := M.localRotation.rotate
    phi := portFaceEquiv M.localRotation M.crossing

where phi is the old face-step permutation.

Define semantic rotation:

    faceStarRotateDesc :

      radialOld p
        -> oldEdge p

      oldEdge p
        -> radialOld (rho p)

      radialCenter p
        -> radialCenter (phi.symm p).

The inverse must be explicit:

      oldEdge p
        -> radialOld p

      radialOld p
        -> oldEdge (rho.symm p)

      radialCenter p
        -> radialCenter (phi p).

Package a semantic equivalence:

    faceStarRotateDescEquiv :
      FaceStarPortDesc M ≃ FaceStarPortDesc M.

Prove left/right inverse by old rho and phi equivalence laws.

## D. Transported local rotation

Transport faceStarRotateDescEquiv through faceStarPortEquiv and define:

    faceStarRotateEquiv M I :
      PortNetworkPort (faceStarNetwork M I)
        ≃
      PortNetworkPort (faceStarNetwork M I).

Package:

    faceStarLocalRotation M I :
      PortLocalRotation (faceStarNetwork M I).

Prove preservesRegion for all three descriptor cases.

Required formulas:

    faceStarRotate_radialOld
    faceStarRotate_oldEdge
    faceStarRotate_radialCenter.

## E. Old-region cyclicity

For an old region r, prove the interleaved rotation cycle is transitive.

Useful iterate formulas, for p in old region:

    rotate^[2*n] (radialOld p)
      =
    radialOld (rho^[n] p)

    rotate^[2*n+1] (radialOld p)
      =
    oldEdge (rho^[n] p)

    rotate^[2*n] (oldEdge p)
      =
    oldEdge (rho^[n] p)

    rotate^[2*n+1] (oldEdge p)
      =
    radialOld (rho^[n+1] p).

Exact indexing variants may be adjusted to fit Lean simplification.

Use M.rotation.cyclic to prove every old-region port reaches every other
old-region port.

Do not finite-case over arbitrary arity.

## F. Face-center cyclicity

At a face-center F, rotation is phi^{-1} on the old face orbit F.

Prove:

for any p,q in F.val,

    exists n,
      (phi.symm^[n]) p = q.

Recommended route:

- from q ∈ old face orbit of p, use existing
      portFaceOrbit_mem_iff_iterate;
- use finite periodicity / reversed orbit membership to convert forward phi
  reachability to backward phi^{-1} reachability.

Then prove the center region rotation is cyclic.

Package:

    faceStarRotationSystem M I :
      PortRotationSystem (faceStarNetwork M I).

## G. Exact new face-step formulas

Let:

    newR := (faceStarRotationSystem M I).toPortLocalRotation
    newC := faceStarCrossing M I
    phi  := portFaceStep M.localRotation M.crossing.

For every old port p prove exactly:

    portFaceStep newR newC (faceStarOldEdgePort I p)
      =
    faceStarRadialOldPort I (phi p).

Then:

    portFaceStep newR newC (faceStarRadialOldPort I (phi p))
      =
    faceStarRadialCenterPort I p.

Then:

    portFaceStep newR newC (faceStarRadialCenterPort I p)
      =
    faceStarOldEdgePort I p.

These three formulas are mandatory and should become simp-friendly.

## H. Primitive period 3

Using descriptor disjointness, prove for oldEdge p:

    firstPortFaceReturn newR newC (faceStarOldEdgePort I p) = 3.

Proof obligations:

- step 1 is radialOld, hence not oldEdge;
- step 2 is radialCenter, hence not oldEdge;
- step 3 returns.

Do the same, preferably via orbit invariance, for radialOld and radialCenter.

No brute-force finite enumeration.

## I. Canonical triangle

Define:

    faceStarTriangle M I p : Finset (new ports) :=
      {
        faceStarOldEdgePort I p,
        faceStarRadialOldPort I (phi p),
        faceStarRadialCenterPort I p
      }.

Prove:

    (faceStarTriangle M I p).card = 3.

Then:

    portFaceOrbit newR newC (faceStarOldEdgePort I p)
      =
    faceStarTriangle M I p.

Also show the same face orbit is obtained when starting from either of the
other two members.

## J. Every new port belongs to one canonical triangle

By semantic descriptor cases:

- oldEdge p -> triangle p;
- radialCenter p -> triangle p;
- radialOld q -> triangle (phi.symm q).

Prove:

    forall q : new port,
      exists p,
        q ∈ faceStarTriangle M I p.

Then prove every new face cell has cardinality 3.

This should be stated first at the local rotation/crossing level and then
reused after packaging the combinatorial map.

## K. Lift old region walks

Define:

    liftFaceStarOldWalk

mapping each old walk edge p to faceStarOldEdgePort I p.

Prove validity:

    PortRegionWalk M.crossing r s
      ->
    PortRegionWalk (faceStarCrossing M I)
      (oldRegion I r)
      (oldRegion I s).

Expose nil/singleton/append calibration if convenient.

## L. Face-center attachment

For every old face cell F prove existence of a boundary port p ∈ F.val.

Use the face-cell orbit witness only inside the proof.

Then one radial crossing connects:

    oldRegion I p.1
      <->
    faceCenterRegion I F.

Package a reachability theorem between every face center and at least one old
region.

## M. Connected combinatorial map

Use:

- original M.connected;
- lifted old walks;
- center attachment;

to prove:

    PortRegionConnected (faceStarCrossing M I).

Package the completed map:

    faceStarCombinatorialMap
      (M : PortCombinatorialMap P)
      (I : PortFaceStarIndexing M) :
      PortCombinatorialMap (faceStarNetwork M I).

This theorem/definition is mandatory for GREEN.

## N. All faces triangular

For the completed map prove:

    faceStar_allFacesTriangular
      (M : PortCombinatorialMap P)
      (I : PortFaceStarIndexing M) :
      PortAllFacesTriangular (faceStarCombinatorialMap M I).

Use sections H–J, not cardinality heuristics.

## O. Port count

Use faceStarPortEquiv and FaceStarPortDesc.card:

    faceStar_portCount :
      (faceStarCombinatorialMap M I).portCount
        =
      3 * M.portCount.

This is D' = 3D.

## P. New-face / old-dart bijection

Define:

    oldPortToFaceCell :
      PortNetworkPort P ->
      PortFaceCell
        (faceStarCombinatorialMap M I).localRotation
        (faceStarCombinatorialMap M I).crossing

by:

    p |-> faceCellOfPort ... (faceStarOldEdgePort I p).

Prove injectivity.

Key observation:

each canonical new triangle contains exactly one oldEdge descriptor, so if two
face cells coincide, their unique oldEdge members coincide and therefore the
old ports coincide.

Prove surjectivity from section J.

Package an equivalence:

    faceStarFaceCellEquiv :
      PortNetworkPort P ≃ PortFaceCell newR newC.

Hence:

    faceStar_faceCount :
      new.faceCount = M.portCount.

This is F' = D.

## Q. Edge count

Use the existing general structural identity between port count and crossing
2-orbits.  If the exact theorem name is awkward, add one small reusable theorem
to PortEulerCount rather than re-proving orbit pairing ad hoc.

Derive:

    faceStar_edgeCount :
      new.edgeCount = 3 * M.edgeCount.

Also:

    new.edgeCount = M.edgeCount + M.portCount.

The second form follows from M.portCount = 2 * M.edgeCount.

## R. Vertex count

From the existing carrier theorem:

    faceStar_vertexCount :
      new.vertexCount = M.vertexCount + M.faceCount.

## S. Euler preservation

Prove:

    faceStar_eulerCharacteristic :
      new.eulerCharacteristic = M.eulerCharacteristic.

Use the count formulas:

    V' = V + F
    E' = 3E
    F' = 2E.

Keep Nat/Int casts explicit and discharge only the arithmetic with omega/ring.

## T. Genus-zero preservation

Define:

    faceStarGenusZero
      (G : PortGenusZeroCombinatorialMap P)
      (I : PortFaceStarIndexing G.map) :
      PortGenusZeroCombinatorialMap (faceStarNetwork G.map I).

Reuse Euler preservation.

## U. Original adjacency embeds

For every old crossing p prove the old-edge crossing formula implies:

    the new region graph has adjacency
      oldRegion I p.1
      oldRegion I (M.crossing.cross p).1.

Then prove a graph-level theorem:

    original adjacency r s
      ->
    new adjacency (oldRegion I r) (oldRegion I s).

Use the existing portRegionSimpleGraph API.

## V. Coloring restriction

For:

    K :
      (portRegionSimpleGraph new.crossing).Coloring TrominoState

define:

    restrictFaceStarColoring M I K

by:

    r |-> K (oldRegion I r).

Prove properness through section U.

Then prove:

    faceStar_colorable_imp_original :
      PortFourStateColorable new.crossing
        ->
      PortFourStateColorable M.crossing.

Do not claim extension of an arbitrary old coloring to new face centers.

## W. Indexing-free triangulation reduction

Using exists_portFaceStarIndexing prove:

    exists_faceStarGenusZeroTriangulation
      (G : PortGenusZeroCombinatorialMap P) :
      exists P' (G' : PortGenusZeroCombinatorialMap P'),
        PortAllFacesTriangular G'.map /\
        (PortFourStateColorable G'.map.crossing ->
          PortFourStateColorable G.map.crossing).

This is the clean public reduction theorem.

## X. Universal triangular target

Define if not already present:

    PortGenusZeroTriangularFourColorTarget : Prop :=
      forall (P : PortNetwork) (G : PortGenusZeroCombinatorialMap P),
        PortAllFacesTriangular G.map ->
        PortFourStateColorable G.map.crossing.

Prove:

    portGenusZeroTriangularFourColorTarget_iff_fourColorTarget :
      PortGenusZeroTriangularFourColorTarget
        <->
      PortGenusZeroFourColorTarget.

The nontrivial direction must use face-star reduction and coloring
restriction.

## Y. Universal tetrahedral target

Define:

    PortGenusZeroTriangularTetrahedralTarget : Prop :=
      forall (P : PortNetwork) (G : PortGenusZeroCombinatorialMap P),
        PortAllFacesTriangular G.map ->
        HasTetrahedralFaceAssignment G.map.

Using TRM-039 prove:

    portGenusZeroTriangularTetrahedralTarget_iff_fourColorTarget :
      PortGenusZeroTriangularTetrahedralTarget
        <->
      PortGenusZeroFourColorTarget.

Do not prove either universal target.

## Z. Fixture counts

For trianglePortMap audit:

    old  V=3 E=3 F=2 D=6
    new  V=5 E=9 F=6 D=18
    chi=2.

For triangleDualMap:

    old  V=2 E=3 F=3 D=6
    new  V=5 E=9 F=6 D=18
    chi=2.

Also audit all new faces triangular.

Do not infer map isomorphism from equal count vectors.

## Outcome policy

TRM-041 is the completion of the partial TRM-040 attempt.

GREEN requires:

- faceStarPortEquiv;
- crossing;
- rotation system;
- actual PortCombinatorialMap;
- all-faces-triangular theorem;
- Euler/genus preservation;
- coloring restriction;
- universal triangular target equivalence.

If semantic->actual dependent Fin transport blocks one of these, report
Outcome P at the exact failed bridge. Do not replace the missing theorem with
an axiom/hypothesis merely to reach the target.

## Axiom / computability policy

All constructors remain computable relative to explicit
PortFaceStarIndexing.

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- new noncomputable production declaration.

Classical choice is allowed only inside theorem proofs / indexing existence.

## Audit

Extend:

    DkMathTest/Tromino/PortFaceStarSubdivisionAxiomAudit.lean

Audit at least:

1. port encode/decode round trips;
2. port equivalence on all 3 descriptor constructors;
3. crossing formulas;
4. crossing involutive / changes region;
5. rotation descriptor inverse laws;
6. actual rotation formulas;
7. old-region cyclicity;
8. center-region cyclicity;
9. the 3 exact face-step formulas;
10. first face return = 3;
11. canonical triangle face orbit;
12. every new face triangular;
13. lifted old walk;
14. connectedness;
15. completed faceStarCombinatorialMap;
16. D'=3D;
17. F'=D;
18. E'=3E=E+D;
19. V'=V+F;
20. Euler preservation;
21. genus-zero preservation;
22. original adjacency embedding;
23. coloring restriction;
24. indexing-free reduction theorem;
25. universal triangular target equivalence;
26. universal triangular tetrahedral target equivalence;
27. triangle fixture count vector;
28. triangle-dual fixture count vector.

Run #print axioms on the completed map, genus preservation, coloring
restriction and universal reduction endpoints.

## Validation

Build:

- DkMath.Tromino.PortFaceStarSubdivision
- DkMath.Tromino.PortTriangulationReduction
- DkMathTest/Tromino/PortFaceStarSubdivisionAxiomAudit

Regression-build:

- DkMath.Tromino.PortTriangularTetrahedral
- DkMath.Tromino.PortGenusZeroHolonomy
- DkMath.Tromino.PortCombinatorialMap
- DkMath.Tromino.PortFaceOrbit
- DkMath.Tromino.PortRotationSystem

Run:

- git diff --check;
- production forbidden-construct scan;
- #print axioms audit.

## Report

Create:

    docs/dev/Tromino-ExchangeCalculus-260924-v0/report-040.md

Record:

- that TRM-040 was carrier-level partial;
- actual-port semantic equivalence;
- crossing/rotation construction;
- three-step face cycle;
- completed combinatorial map;
- count formulas;
- Euler/genus preservation;
- coloring restriction;
- universal triangulation reduction;
- universal tetrahedral target reduction;
- exact remaining Four-Color-strength gap:
      A/B/C assignment existence on all-triangular genus-zero maps.

## Stop condition

Stop once the partial face-star carrier is promoted to a fully verified
all-triangular genus-zero reduction for four-state colorability.

Do not prove universal tetrahedral assignment existence, a general dual
PortNetwork constructor, topological realization, rigid tetrahedron
orientation, or the Four Color theorem without review.
