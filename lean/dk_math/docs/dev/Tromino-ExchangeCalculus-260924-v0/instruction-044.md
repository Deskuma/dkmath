# TRM-045 — Face-star connectivity and combinatorial-map packaging

## Goal

Promote the already verified face-star crossing/rotation/triangular dynamics
to an actual connected PortCombinatorialMap.

TRM-044 already proved:

- faceStarCrossing;
- faceStarRotationSystem;
- exact 3-step face dynamics;
- every local face cell has cardinality 3.

TRM-045 must prove only:

1. old walks lift to the face-star map;
2. every face-center region is attached to an old region by one radial edge;
3. every new region can reach some old region;
4. the face-star crossing is globally region-connected;
5. the completed faceStarCombinatorialMap exists;
6. the completed map still has every face cell of cardinality 3.

Do not prove V/E/F/D formulas, Euler/genus preservation, coloring restriction,
or universal targets in this checkpoint.

## Production

Create a new module to keep the now-large triangulation file bounded:

    DkMath/Tromino/PortFaceStarMap.lean

Import:

    DkMath.Tromino.PortTriangulationReduction

Create audit:

    DkMathTest/Tromino/PortFaceStarMapAxiomAudit.lean

Report:

    docs/dev/Tromino-ExchangeCalculus-260924-v0/report-044.md

Do not move or rewrite the already verified TRM-040..044 code.

## Read first

Read only:

- CURRENT_STATE.md;
- this instruction;
- DkMath/Tromino/PortTriangulationReduction.lean;
- DkMath/Tromino/PortRegionWalk.lean;
- DkMath/Tromino/PortCombinatorialMap.lean.

Consult PortF2Chains only for exact face-cell witness APIs if needed.

## A. New-region classification

Prove every region of faceStarNetwork is either an embedded old region or a
face-center region.

Recommended theorem shape:

    theorem faceStar_region_cases
        (I : PortFaceStarIndexing M)
        (x : Fin (faceStarNetwork M I).regionCount) :
      (∃ r : Fin M.vertexCount, x = oldRegion I r) ∨
      (∃ F : PortFaceCell M.localRotation M.crossing,
          x = faceCenterRegion I F).

Use:

    (faceStarRegionEquiv M I).symm x

and cases on the Sum.

For the center case take:

    F := I.faceEquiv.symm f.

This theorem should contain all region-index dependent transport needed by
the later connectivity proof.

## B. Lift validity of old walks

Define a helper on edge lists or directly prove:

    faceStar_oldWalk_valid

mapping every old port p to:

    faceStarOldEdgePort I p.

For:

    PortRegionWalk.Valid M.crossing r s xs

prove:

    PortRegionWalk.Valid (faceStarCrossing I)
      (oldRegion I r)
      (oldRegion I s)
      (xs.map (faceStarOldEdgePort I)).

Use induction on xs and the exact theorem:

    faceStarCross_oldEdge.

Do not unfold the actual codec or dependent Fin layer.

## C. Lift old PortRegionWalk

Define:

    def liftFaceStarOldWalk
        (I : PortFaceStarIndexing M)
        {r s : Fin P.regionCount}
        (W : PortRegionWalk M.crossing r s) :
      PortRegionWalk (faceStarCrossing I)
        (oldRegion I r)
        (oldRegion I s)

with:

    edges := W.edges.map (faceStarOldEdgePort I).

If M.vertexCount versus P.regionCount requires casts, isolate them in one
small theorem/abbrev. Do not spread Fin.cast through the walk proofs.

Calibration:

    liftFaceStarOldWalk_edges

and, if cheap:

    lift_nil
    lift_append
    lift_reverse.

Only the edges theorem is mandatory.

## D. Lift old reachability

Prove:

    faceStar_oldRegion_reachable
      (h : PortRegionReachable M.crossing r s) :
      PortRegionReachable (faceStarCrossing I)
        (oldRegion I r)
        (oldRegion I s).

Then specialize original map connectivity:

    faceStar_oldRegions_connected :
      ∀ r s,
        PortRegionReachable (faceStarCrossing I)
          (oldRegion I r)
          (oldRegion I s).

Use M.connected.

## E. Every old face cell has a boundary port

Prove:

    faceStar_faceCell_nonempty
      (F : PortFaceCell M.localRotation M.crossing) :
      ∃ p : PortNetworkPort P, p ∈ F.val.

Recommended route:

- F.property says F.val ∈ portFaceOrbits;
- use portFaceOrbits_mem_iff to obtain representative p and
      F.val = portFaceOrbit ... p;
- use portFaceOrbit_contains.

Do not use Classical.choose in a production definition. This is a theorem
witness only.

## F. Face-cell representative calibration

For p ∈ F.val prove:

    faceCellOfPort M.localRotation M.crossing p = F.

Use the existing faceCellOfPort_eq_iff or orbit-membership theorem if
available; otherwise prove via Subtype.ext and portFaceOrbit_eq_of_mem.

This theorem may be private if only needed for center attachment.

## G. One radial edge attaches each center

For every old face cell F prove existence of an old boundary port p and a
one-edge face-star walk from its old region to the center:

    theorem faceStar_center_attachment :
      ∀ F,
        ∃ p : PortNetworkPort P,
          p ∈ F.val ∧
          PortRegionReachable (faceStarCrossing I)
            (oldRegion I p.1)
            (faceCenterRegion I F).

Preferred proof:

1. choose p from section E;
2. use:
       PortRegionWalk.singleton
         (faceStarCrossing I)
         (faceStarRadialOldPort I p);
3. rewrite its target with:
       faceStarCross_radialOld;
4. identify:
       faceCellOfPort ... p = F
   using section F.

Also expose the reverse reachability center -> old via
portRegionReachable_symm, either as a separate theorem or inline later.

## H. Every new region reaches an old region

Prove:

    theorem faceStar_region_reaches_old :
      ∀ x : Fin (faceStarNetwork M I).regionCount,
        ∃ r : Fin M.vertexCount,
          PortRegionReachable (faceStarCrossing I)
            x (oldRegion I r).

Use faceStar_region_cases.

Cases:

- oldRegion r:
    reflexive reachability;

- faceCenterRegion F:
    take p from faceStar_center_attachment and reverse that reachability;
    choose the corresponding old region p.1.

Keep all old-index cast normalization local.

## I. Global connectedness

Prove:

    theorem faceStar_regionConnected :
      PortRegionConnected (faceStarCrossing I).

For arbitrary x y:

1. obtain:
       x -> oldRegion r
       y -> oldRegion s
   from section H;

2. use:
       oldRegion r -> oldRegion s
   from faceStar_oldRegions_connected;

3. reverse the y-to-old path to get:
       oldRegion s -> y;

4. compose with portRegionReachable_trans.

This theorem is the main endpoint of this checkpoint.

## J. Nonempty regions

Prove:

    faceStar_nonemptyRegions :
      0 < (faceStarNetwork M I).regionCount.

Use:

    (faceStarNetwork M I).regionCount
      = M.vertexCount + M.faceCount

and M.nonemptyRegions / M.vertexCount = P.regionCount.

Do not derive nonemptiness from face existence.

## K. Package the map

Define:

    def faceStarCombinatorialMap
        (M : PortCombinatorialMap P)
        (I : PortFaceStarIndexing M) :
      PortCombinatorialMap (faceStarNetwork M I)

with:

    crossing := faceStarCrossing I
    rotation := faceStarRotationSystem I
    nonemptyRegions := faceStar_nonemptyRegions ...
    connected := faceStar_regionConnected ...

This definition is mandatory.

## L. Calibration of packaged fields

Prove simp/calibration theorems:

    faceStarCombinatorialMap_crossing
    faceStarCombinatorialMap_rotation
    faceStarCombinatorialMap_localRotation

at least extensionally or by rfl where possible.

The later Euler/coloring checkpoint must not need to unfold the whole
structure.

## M. Triangular face-cell theorem on the packaged map

Prove:

    theorem faceStarCombinatorialMap_everyFaceCell_card_three :
      ∀ F : PortFaceCell
          (faceStarCombinatorialMap M I).localRotation
          (faceStarCombinatorialMap M I).crossing,
        F.val.card = 3.

This should be a thin transport of:

    faceStar_everyFaceCell_card_three.

No new face-orbit proof.

Optionally expose a local predicate such as:

    FaceCellsAllCardThree M

only if it reduces duplication later.

Do not import PortTriangularTetrahedral merely to name
PortAllFacesTriangular in this checkpoint if doing so risks dependency
cycles.  The next reduction module can translate this card-3 theorem into
that predicate.

## N. Safety / scope

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- new noncomputable production declaration.

No:

- edge/face/vertex count formulas;
- Euler characteristic calculation;
- genus-zero wrapper;
- coloring restriction;
- universal triangular target;
- Eisenstein realization.

## O. Audit

Create:

    DkMathTest/Tromino/PortFaceStarMapAxiomAudit.lean

Audit at least:

1. faceStar_region_cases;
2. old-walk validity lift;
3. liftFaceStarOldWalk;
4. liftFaceStarOldWalk_edges;
5. old reachability lift;
6. old-region connectedness;
7. face-cell nonempty witness;
8. center attachment;
9. every new region reaches old;
10. global region connectedness;
11. nonempty regions;
12. faceStarCombinatorialMap;
13. packaged crossing calibration;
14. packaged rotation calibration;
15. packaged localRotation calibration;
16. packaged every-face-card-three theorem.

Run #print axioms on:

- liftFaceStarOldWalk;
- faceStar_center_attachment;
- faceStar_regionConnected;
- faceStarCombinatorialMap;
- faceStarCombinatorialMap_everyFaceCell_card_three.

Expected logical dependencies may remain the existing:

    propext
    Classical.choice
    Quot.sound

No new axiom.

## P. Validation

Build:

- DkMath.Tromino.PortFaceStarMap
- DkMathTest/Tromino/PortFaceStarMapAxiomAudit

Regression-build:

- DkMath.Tromino.PortTriangulationReduction
- DkMath.Tromino.PortRegionWalk
- DkMath.Tromino.PortCombinatorialMap
- DkMath.Tromino.PortFaceOrbit

Run:

- git diff --check;
- production forbidden-construct scan;
- #print axioms audit.

## Q. Report

Create:

    docs/dev/Tromino-ExchangeCalculus-260924-v0/report-044.md

Record:

- region classification;
- old-walk lifting;
- face-center radial attachment;
- global connectivity argument;
- nonempty-regions proof;
- completed faceStarCombinatorialMap;
- packaged triangular face-cell theorem;
- build/axiom results.

If A–M are complete, report:

    Outcome A — face-star connected combinatorial map complete.

## Final acceptance audit

Before reporting completion, re-read this instruction and internally map:

    requirement | theorem/definition | status.

A successful build alone is not GREEN.

If any mandatory A–M item is missing, report Outcome P with the exact
missing theorem.

## Stop condition

Stop once the face-star network is packaged as a connected
PortCombinatorialMap and the packaged map is kernel-checked to have every
face cell of cardinality 3.

Do not proceed to V/E/F/D counts, Euler/genus preservation, coloring
restriction, universal targets, or Eisenstein realization.
