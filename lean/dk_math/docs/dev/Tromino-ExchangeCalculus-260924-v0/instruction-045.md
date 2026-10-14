# TRM-046 — Face-star count identities / Euler and genus-zero preservation

## Goal

Prove the exact counting identities for the completed connected face-star
combinatorial map and use them to establish Euler-characteristic and
genus-zero preservation.

TRM-045 already provides:

    faceStarCombinatorialMap M I

with every packaged face cell of cardinality 3.

TRM-046 must establish:

    D' = 3D
    F' = D
    E' = 3E = E + D
    V' = V + F
    chi' = chi

and then package the genus-zero face-star map.

Do not prove coloring restriction or universal Four-Color target equivalence
in this checkpoint.

## Production

Create:

    DkMath/Tromino/PortFaceStarEuler.lean

Import:

    DkMath.Tromino.PortFaceStarMap

Create audit:

    DkMathTest/Tromino/PortFaceStarEulerAxiomAudit.lean

Create report:

    docs/dev/Tromino-ExchangeCalculus-260924-v0/report-045.md

Keep PortFaceStarMap.lean unchanged unless a genuinely missing reusable API
is discovered.

## Read first

Read only:

- CURRENT_STATE.md;
- this instruction;
- DkMath/Tromino/PortFaceStarMap.lean;
- DkMath/Tromino/PortEulerCount.lean;
- DkMath/Tromino/PortF2Chains.lean;
- DkMath/Tromino/PortCombinatorialMap.lean.

Do not re-read the full Tromino history.

## Notation

Throughout, let:

    N := faceStarNetwork M I
    M' := faceStarCombinatorialMap M I

Interpret:

    D  := M.portCount
    E  := M.edgeCount
    F  := M.faceCount
    V  := M.vertexCount

    D' := M'.portCount
    E' := M'.edgeCount
    F' := M'.faceCount
    V' := M'.vertexCount.

## A. Port-count identity

Prove:

    theorem faceStar_portCount :
      (faceStarCombinatorialMap M I).portCount
        =
      3 * M.portCount.

Preferred proof:

- use Fintype.card_congr faceStarPortEquiv;
- use FaceStarPortDesc.card / faceStar_descriptor_card.

Do not count the dependent Sigma carrier by hand.

This is:

    D' = 3D.

## B. Old-port to new-face-cell map

Define:

    def faceStarOldPortToFaceCell
        (I : PortFaceStarIndexing M)
        (p : PortNetworkPort P) :
      PortFaceCell
        (faceStarCombinatorialMap M I).localRotation
        (faceStarCombinatorialMap M I).crossing :=
      faceCellOfPort _ _
        (faceStarOldEdgePort I p).

Calibration:

    faceStarOldPortToFaceCell_val :
      (faceStarOldPortToFaceCell I p).val
        =
      faceStarTriangle M I p.

Use the already verified:

    faceStarTriangle_eq_oldEdge_orbit.

## C. Unique old-edge member of a canonical triangle

Prove:

    faceStarTriangle_oldEdge_mem :
      faceStarOldEdgePort I p ∈ faceStarTriangle M I p.

Then prove uniqueness:

    theorem faceStarTriangle_oldEdge_unique :
      faceStarOldEdgePort I q ∈ faceStarTriangle M I p
        ->
      q = p.

Recommended proof:

- expand the 3-element triangle;
- use semantic constructor disjointness to rule out radialOld/radialCenter;
- use injectivity of faceStarOldEdgePort for the remaining case.

If constructor injectivity is not already public, derive it through
faceStarPortDecode:

    oldEdge q = oldEdge p -> q = p.

Do not use cardinality to infer uniqueness.

## D. Injectivity of old-port -> new-face-cell

Prove:

    theorem faceStarOldPortToFaceCell_injective :
      Function.Injective (faceStarOldPortToFaceCell I).

If:

    faceStarOldPortToFaceCell I p
      =
    faceStarOldPortToFaceCell I q

then their values / canonical triangles coincide.  Since the q-oldEdge member
lies in q's triangle, transport membership into p's triangle and apply
section C.

## E. Surjectivity onto every new face cell

Prove:

    theorem faceStarOldPortToFaceCell_surjective :
      Function.Surjective (faceStarOldPortToFaceCell I).

Recommended proof:

1. take arbitrary new face cell F;
2. obtain q with:
       F = faceCellOfPort _ _ q
   from the face-orbit witness API;
3. use:
       faceStarTriangle_coverage I q
   to obtain old p with q ∈ faceStarTriangle M I p;
4. rewrite that triangle as the oldEdge face orbit;
5. use faceCellOfPort_eq_of_mem / Subtype.ext to identify F with
       faceStarOldPortToFaceCell I p.

Do not choose representatives in a production definition.

## F. Package face-cell equivalence

Define:

    def faceStarFaceCellEquiv
        (I : PortFaceStarIndexing M) :
      PortNetworkPort P ≃
      PortFaceCell
        (faceStarCombinatorialMap M I).localRotation
        (faceStarCombinatorialMap M I).crossing

using B, D, E.

This equivalence is a useful public structural theorem.

## G. Face-count identity

Prove:

    theorem faceStar_faceCount :
      (faceStarCombinatorialMap M I).faceCount
        =
      M.portCount.

Preferred proof:

- rewrite map faceCount through PortFaceCell_card;
- use Fintype.card_congr (faceStarFaceCellEquiv I).

This is:

    F' = D.

Do not derive it only from 3*F' = 3*D unless the equivalence route proves
unexpectedly difficult.

## H. Vertex-count identity

Prove:

    theorem faceStar_vertexCount :
      (faceStarCombinatorialMap M I).vertexCount
        =
      M.vertexCount + M.faceCount.

Reuse:

    faceStarNetwork_regionCount
    faceStar_regionCount_eq.

This is:

    V' = V + F.

## I. Old and new port-edge identities

Record/reuse:

    2 * M.edgeCount = M.portCount

and:

    2 * M'.edgeCount = M'.portCount.

Do not re-prove crossing-orbit pairing.

Use:

    two_mul_portCrossingEdgeCount

or:

    portCrossingEdgeCount_mul_two.

Package small map-level helper theorem only if it substantially cleans later
arithmetic:

    two_mul_edgeCount_eq_portCount
      (M : PortCombinatorialMap P) :
      2 * M.edgeCount = M.portCount.

If this helper is generally useful, place it in PortEulerCount or
PortCombinatorialMap with minimal change. Otherwise keep it local.

## J. Edge-count identity

Using A and I prove:

    theorem faceStar_edgeCount :
      (faceStarCombinatorialMap M I).edgeCount
        =
      3 * M.edgeCount.

This is:

    E' = 3E.

Use Nat arithmetic / omega after rewriting the port-count identities.

Do not manually enumerate edge cells.

## K. Alternate edge identity

Prove:

    theorem faceStar_edgeCount_eq_add_portCount :
      (faceStarCombinatorialMap M I).edgeCount
        =
      M.edgeCount + M.portCount.

Use:

    M.portCount = 2 * M.edgeCount

and J.

This is the combinatorial face-star formula:

    E' = E + D.

## L. Euler characteristic expansion

Expose a map-level theorem if not already convenient:

    M.eulerCharacteristic
      =
    (M.vertexCount : Int)
      - (M.edgeCount : Int)
      + (M.faceCount : Int).

Likewise for M'.

This should unfold existing definitions only; no topology.

## M. Euler preservation

Prove:

    theorem faceStar_eulerCharacteristic :
      (faceStarCombinatorialMap M I).eulerCharacteristic
        =
      M.eulerCharacteristic.

Use exactly:

    V' = V + F
    E' = 3E
    F' = D
    D  = 2E.

After rewriting Nat equalities, cast explicitly to Int and finish with omega
or ring.

This theorem is the central endpoint.

## N. Genus preservation for arbitrary stated genus

Prove a slightly stronger theorem:

    theorem faceStar_preserves_combinatorial_genus
        {g : Nat}
        (hg : PortHasCombinatorialGenus M g) :
      PortHasCombinatorialGenus
        (faceStarCombinatorialMap M I) g.

This should be immediate from M.

Optionally prove the iff:

    PortHasCombinatorialGenus (faceStarCombinatorialMap M I) g
      <->
    PortHasCombinatorialGenus M g.

Prefer the iff if trivial from Euler equality.

## O. Genus-zero packaging

Define:

    def faceStarGenusZero
        (G : PortGenusZeroCombinatorialMap P)
        (I : PortFaceStarIndexing G.map) :
      PortGenusZeroCombinatorialMap (faceStarNetwork G.map I)

with:

    map := faceStarCombinatorialMap G.map I
    genusZero := faceStar_preserves_combinatorial_genus I G.genusZero.

This is mandatory.

## P. Genus-zero calibration

Prove:

    @[simp] theorem faceStarGenusZero_map :
      (faceStarGenusZero G I).map =
        faceStarCombinatorialMap G.map I := rfl

and count/Euler corollaries if they are one-line consequences:

    faceStarGenusZero_vertexCount
    faceStarGenusZero_edgeCount
    faceStarGenusZero_faceCount
    faceStarGenusZero_portCount
    faceStarGenusZero_eulerCharacteristic.

These corollaries are recommended but not mandatory if they duplicate exact
existing theorems without improving later proofs.

## Q. Fixture regressions

If existing fixture names are available without importing broad test-only
modules, audit the count vector for:

trianglePortMap:

    old:
      V=3 E=3 F=2 D=6
    face-star:
      V'=5 E'=9 F'=6 D'=18
      chi'=2.

triangleDualMap:

    old:
      V=2 E=3 F=3 D=6
    face-star:
      V'=5 E'=9 F'=6 D'=18
      chi'=2.

Do not force these fixture imports into production.

If the fixture names live only in tests, put the regressions only in the
audit file.

Do not infer isomorphism from equal count vectors.

## R. Safety / scope

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- new noncomputable production declaration.

No:

- coloring restriction;
- universal all-triangular target;
- tetrahedral assignment existence;
- Eisenstein lattice realization;
- Four Color theorem claim.

## S. Audit

Create:

    DkMathTest/Tromino/PortFaceStarEulerAxiomAudit.lean

Audit at least:

1. faceStar_portCount;
2. faceStarOldPortToFaceCell;
3. faceStarOldPortToFaceCell_val;
4. unique old-edge member;
5. injectivity;
6. surjectivity;
7. faceStarFaceCellEquiv;
8. faceStar_faceCount;
9. faceStar_vertexCount;
10. faceStar_edgeCount;
11. faceStar_edgeCount_eq_add_portCount;
12. faceStar_eulerCharacteristic;
13. genus-preservation theorem / iff;
14. faceStarGenusZero;
15. optional genus-zero count corollaries;
16. fixture regressions if available.

Run #print axioms on:

- faceStarFaceCellEquiv;
- faceStar_faceCount;
- faceStar_edgeCount;
- faceStar_eulerCharacteristic;
- faceStarGenusZero.

Expected existing dependencies may include:

    propext
    Classical.choice
    Quot.sound.

No new axiom.

## T. Validation

Build:

- DkMath.Tromino.PortFaceStarEuler
- DkMathTest/Tromino/PortFaceStarEulerAxiomAudit

Regression-build:

- DkMath.Tromino.PortFaceStarMap
- DkMath.Tromino.PortTriangulationReduction
- DkMath.Tromino.PortEulerCount
- DkMath.Tromino.PortCombinatorialMap

Run:

- git diff --check;
- production forbidden-construct scan;
- #print axioms audit.

## U. Report

Create:

    docs/dev/Tromino-ExchangeCalculus-260924-v0/report-045.md

Record:

- D'/D proof;
- old-port/new-face equivalence;
- F'=D proof;
- E'=3E and E'=E+D;
- V'=V+F;
- Euler-preservation arithmetic;
- genus preservation;
- faceStarGenusZero packaging;
- fixture count regressions if run;
- build/axiom results.

If A–P are complete, report:

    Outcome A — face-star count/Euler/genus preservation complete.

## Final acceptance audit

Before reporting completion, re-read this instruction and internally map:

    requirement | theorem/definition | status.

A successful build alone is not GREEN.

If any mandatory item A–P is missing, report Outcome P with the exact
missing theorem.

## Stop condition

Stop once the count identities, Euler preservation, and genus-zero face-star
wrapper are kernel-checked.

Do not proceed to coloring restriction, universal target equivalence, or
Eisenstein realization.
