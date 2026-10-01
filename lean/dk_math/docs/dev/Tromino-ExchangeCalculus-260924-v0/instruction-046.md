
# TRM-047 — Packaged triangulation and coloring restriction

## Goal

Turn the completed face-star genus-zero map into the exact one-way reduction
needed for Four-Color work, but stop before universal target equivalence.

TRM-046 already provides faceStarGenusZero G I with:
- connected PortCombinatorialMap;
- every face cell cardinality 3;
- Euler/genus-zero preservation.

TRM-047 must prove:
1. the packaged face-star map satisfies PortAllFacesTriangular;
2. original adjacency embeds through oldRegion;
3. any face-star four-state coloring restricts to an original-map coloring;
4. therefore face-star colorability implies original colorability;
5. a tetrahedral assignment on the face-star map implies original colorability.

Do not define universal target propositions yet.
Do not begin Eisenstein realization.

## Production

Create:
    DkMath/Tromino/PortFaceStarColorReduction.lean

Imports:
    DkMath.Tromino.PortFaceStarEuler
    DkMath.Tromino.PortTriangularTetrahedral

Create audit:
    DkMathTest/Tromino/PortFaceStarColorReductionAxiomAudit.lean

Create report:
    docs/dev/Tromino-ExchangeCalculus-260924-v0/report-046.md

## Read first

Read only:
- CURRENT_STATE.md;
- this instruction;
- DkMath/Tromino/PortFaceStarEuler.lean;
- DkMath/Tromino/PortTriangularTetrahedral.lean;
- DkMath/Tromino/PortTensionColoring.lean.

Do not re-read the full branch unless a named theorem lookup is necessary.

## A. Packaged all-triangular theorem

Prove:

    theorem faceStar_allFacesTriangular
        {P : PortNetwork}
        (M : PortCombinatorialMap P)
        (I : PortFaceStarIndexing M) :
      PortAllFacesTriangular (faceStarCombinatorialMap M I).

This should be a thin wrapper around:
    faceStarCombinatorialMap_everyFaceCell_card_three.

Then prove:

    theorem faceStarGenusZero_allFacesTriangular
        (G : PortGenusZeroCombinatorialMap P)
        (I : PortFaceStarIndexing G.map) :
      PortAllFacesTriangular (faceStarGenusZero G I).map.

## B. Old-edge source/target calibration

Reuse existing source theorems. Add only if needed:

    theorem faceStar_oldEdge_source :
      (faceStarOldEdgePort I p).1 = oldRegion I p.1.

    theorem faceStar_oldEdge_target :
      ((faceStarCombinatorialMap M I).crossing.cross
        (faceStarOldEdgePort I p)).1
      =
      oldRegion I (M.crossing.cross p).1.

The target theorem should use faceStarCross_oldEdge.
Do not unfold dependent-Fin codecs.

## C. Original adjacency embeds

Prove:

    theorem faceStar_oldAdjacency
        {r s : Fin P.regionCount}
        (h : (portRegionSimpleGraph M.crossing).Adj r s) :
      (portRegionSimpleGraph
        (faceStarCombinatorialMap M I).crossing).Adj
        (oldRegion I r)
        (oldRegion I s).

Recommended proof:
1. extract old port p from portRegionSimpleGraph_adj_iff;
2. use faceStarOldEdgePort I p as new adjacency witness;
3. source is oldRegion I r;
4. target follows from faceStarCross_oldEdge.

Also prove if convenient:

    faceStar_oldAdjacency_of_port :
      Adj
        (oldRegion I p.1)
        (oldRegion I (M.crossing.cross p).1).

## D. oldRegion embedding helper

Reuse oldRegion_injective I.

If type noise appears, define:

    def faceStarOldRegionEmbedding
        (I : PortFaceStarIndexing M) :
      Fin P.regionCount -> Fin (faceStarNetwork M I).regionCount :=
      oldRegion I

and prove injectivity from oldRegion_injective.

No equivalence is required.

## E. Restrict one face-star coloring

Define:

    def faceStarRestrictColoring
        {P : PortNetwork}
        (M : PortCombinatorialMap P)
        (I : PortFaceStarIndexing M)
        (K :
          (portRegionSimpleGraph
            (faceStarCombinatorialMap M I).crossing).Coloring
            TrominoState) :
      (portRegionSimpleGraph M.crossing).Coloring TrominoState

with color function:
    r |-> K (oldRegion I r).

Validity:
- for old adjacency h : Adj r s;
- obtain faceStar_oldAdjacency I h;
- apply K.valid.

Do not reconstruct a V4 assignment.
Do not invoke zero-holonomy.
This is pure graph-coloring pullback.

## F. Coloring application calibration

Prove:

    theorem faceStarRestrictColoring_apply
        (K : ...)
        (r : Fin P.regionCount) :
      faceStarRestrictColoring M I K r
        =
      K (oldRegion I r).

Prefer rfl.

## G. Optional edge distinction corollary

If useful prove:

    theorem faceStarRestrictColoring_edge_ne
        (K : ...)
        (p : PortNetworkPort P) :
      faceStarRestrictColoring M I K p.1
        !=
      faceStarRestrictColoring M I K (M.crossing.cross p).1.

Derive from coloring validity; do not re-prove adjacency.

## H. Colorability implication

Prove:

    theorem faceStar_colorable_imp_original
        {P : PortNetwork}
        (M : PortCombinatorialMap P)
        (I : PortFaceStarIndexing M) :
      PortFourStateColorable
          (faceStarCombinatorialMap M I).crossing
        ->
      PortFourStateColorable M.crossing.

Proof:
    <K> |-> <faceStarRestrictColoring M I K>.

Then prove:

    theorem faceStarGenusZero_colorable_imp_original
        (G : PortGenusZeroCombinatorialMap P)
        (I : PortFaceStarIndexing G.map) :
      PortFourStateColorable (faceStarGenusZero G I).map.crossing
        ->
      PortFourStateColorable G.map.crossing.

Prefer direct reuse of the previous theorem.

## I. Tetrahedral consequence on the face-star map

Using faceStarGenusZero_allFacesTriangular and existing TRM-039 theorem
hasTetrahedralFaceAssignment_iff_fourStateColorable, prove:

    theorem faceStar_tetrahedral_iff_colorable
        (G : PortGenusZeroCombinatorialMap P)
        (I : PortFaceStarIndexing G.map) :
      HasTetrahedralFaceAssignment (faceStarGenusZero G I).map
        <->
      PortFourStateColorable (faceStarGenusZero G I).map.crossing.

Then prove:

    theorem faceStar_tetrahedral_imp_original_colorable
        (G : PortGenusZeroCombinatorialMap P)
        (I : PortFaceStarIndexing G.map) :
      HasTetrahedralFaceAssignment (faceStarGenusZero G I).map
        ->
      PortFourStateColorable G.map.crossing.

This is:
    tetrahedral
      -> face-star colorable
      -> original colorable.

This is NOT a universal existence theorem.

## J. No extension theorem

Do NOT prove or claim:
    original coloring -> face-star coloring.

The face-center colors are not shown to admit arbitrary extension from an
arbitrary old coloring.  The reduction only requires:
    face-star colorable -> original colorable.

## K. No universal target yet

Do NOT define:
    PortGenusZeroTriangularFourColorTarget
    PortGenusZeroTriangularTetrahedralTarget

Those belong to TRM-048 where indexing existence and universal
quantification will be handled in a final small layer.

## L. Safety / scope

No:
- sorry;
- admit;
- unsafe;
- new axiom;
- new noncomputable production declaration.

No:
- Four Color theorem existence claim;
- universal target proof;
- Eisenstein lattice realization;
- rigid tetrahedron orientation realization;
- topological Euclidean triangular-lattice embedding.

## M. Audit

Create:
    DkMathTest/Tromino/PortFaceStarColorReductionAxiomAudit.lean

Audit at least:
1. faceStar_allFacesTriangular;
2. faceStarGenusZero_allFacesTriangular;
3. old-edge source calibration if added;
4. old-edge target calibration if added;
5. faceStar_oldAdjacency;
6. faceStarOldRegionEmbedding if added;
7. faceStarRestrictColoring;
8. faceStarRestrictColoring_apply;
9. edge-ne corollary if added;
10. faceStar_colorable_imp_original;
11. faceStarGenusZero_colorable_imp_original;
12. faceStar_tetrahedral_iff_colorable;
13. faceStar_tetrahedral_imp_original_colorable.

Run #print axioms on:
- faceStar_allFacesTriangular;
- faceStar_oldAdjacency;
- faceStarRestrictColoring;
- faceStar_colorable_imp_original;
- faceStar_tetrahedral_imp_original_colorable.

Expected existing dependencies may include:
    propext
    Classical.choice
    Quot.sound.

No new axiom.

## N. Validation

Build:
- DkMath.Tromino.PortFaceStarColorReduction
- DkMathTest/Tromino/PortFaceStarColorReductionAxiomAudit

Regression-build:
- DkMath.Tromino.PortFaceStarEuler
- DkMath.Tromino.PortTriangularTetrahedral
- DkMath.Tromino.PortTensionColoring
- DkMath.Tromino.PortFaceStarMap

Run:
- git diff --check;
- production forbidden-construct scan;
- #print axioms audit.

## O. Report

Create:
    docs/dev/Tromino-ExchangeCalculus-260924-v0/report-046.md

Record:
- packaged all-triangular theorem;
- old adjacency embedding;
- coloring pullback construction;
- one-way colorability reduction;
- local tetrahedral/coloring equivalence on the face-star map;
- tetrahedral -> original-colorable reduction;
- explicit statement that coloring extension in the opposite direction is
  NOT claimed;
- build/axiom results.

If A-I are complete, report:

    Outcome A — packaged triangular coloring restriction complete.

## Final acceptance audit

Before reporting completion, re-read this instruction and internally map:

    requirement | theorem/definition | status.

A successful build alone is not GREEN.

If any mandatory A-I item is missing, report Outcome P with the exact
missing theorem.

## Stop condition

Stop once the completed genus-zero face-star map is formally known to be
all-triangular and any four-state coloring/tetrahedral assignment on it can
be restricted to a proper coloring of the original map.

Do not proceed to universal target equivalence or Eisenstein realization.
