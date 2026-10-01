
# TRM-039 — Tetrahedral local closure / triangular-face normal form

## Goal

After TRM-038, the remaining Four-Color-strength gap is no longer
integrability:

    genus zero + face conservation
      <-> zero holonomy
      <-> proper four-state coloring.

The remaining gap is existence of a nowhere-zero V4 assignment satisfying
face conservation.

TRM-039 must not attempt that universal existence theorem directly.
Instead, formalize the newly identified tetrahedral local closure:

- four face colors = the four elements of V4;
- six tetrahedron edges = unordered pairs of distinct face colors;
- each edge carries the nonzero relative delta between its two faces;
- the six edges split into three opposite pairs, one pair for each
  deltaA/deltaB/deltaC;
- once one face color is fixed, the other three faces are exactly the three
  nonzero V4 translates;
- on a triangular Port face, three nonzero edge labels have zero sum iff they
  are exactly deltaA/deltaB/deltaC once each.

Then connect this local tetrahedral normal form to
IsDualFaceKirchhoff on triangular Port maps.

This checkpoint should expose the next global existence problem in a sharper
"Tait/tetrahedral three-direction" form, while also providing the formal
kernel for the future rolling-stamp puzzle/game.

Do not prove the Four Color theorem or a universal tetrahedral assignment.

## Production files

Create:

- DkMath/Tromino/TetrahedralClosure.lean
- DkMath/Tromino/PortTriangularTetrahedral.lean

The first file is finite/local and independent of Port combinatorial maps.
The second file connects it to the existing Port face-conservation stack.

## A. Tetrahedron faces are the four V4 states

Use:

    abbrev TetraFace := TrominoState

The canonical face coloring is identity.

Expose:

    tetraFaceColor : TetraFace -> TrominoState := id

and prove:

    Fintype.card TetraFace = 4.

The four faces are therefore:

    0, deltaA, deltaB, deltaC.

No new four-color carrier should be invented.

## B. Six unoriented tetrahedron edges

Define an unoriented edge as a two-element face subset:

    abbrev TetraEdge :=
      {E : Finset TetraFace // E.card = 2}

Provide Fintype and DecidableEq instances if not inferred automatically.

Define:

    tetraEdgeBetween (a b : TetraFace) (h : a != b) : TetraEdge

with underlying set {a,b}.

Prove:

    Fintype.card TetraEdge = 6.

This is the exact finite theorem behind "four faces -> six edges".

## C. Edge delta

Define:

    tetraEdgeDelta (E : TetraEdge) : TrominoState :=
      sum c in E.val, c.

For a generated edge prove:

    tetraEdgeDelta (tetraEdgeBetween a b h) = a + b.

Because a != b in V4, prove:

    tetraEdgeDelta_ne_zero (E : TetraEdge) :
      tetraEdgeDelta E != 0.

Hence every tetrahedron edge has one of exactly:

    deltaA, deltaB, deltaC.

Prove the image theorem:

    Finset.univ.image tetraEdgeDelta
      = {deltaA, deltaB, deltaC}.

## D. Six edges split into three opposite delta pairs

For d : TrominoState define:

    tetraEdgesWithDelta d :=
      Finset.univ.filter (fun E : TetraEdge => tetraEdgeDelta E = d).

Prove:

    card (tetraEdgesWithDelta deltaA) = 2
    card (tetraEdgesWithDelta deltaB) = 2
    card (tetraEdgesWithDelta deltaC) = 2.

Also prove every edge belongs to exactly one of these three fibers.

Strongly preferred:

    if E != F and tetraEdgeDelta E = tetraEdgeDelta F,
    then Disjoint E.val F.val.

Thus equal-delta pairs are exactly opposite tetrahedron edges.

This is the formal theorem:

    6 edges = 2 A + 2 B + 2 C.

If the generic disjointness proof becomes disproportionately expensive, the
three explicit opposite-pair calibrations are acceptable for GREEN.

## E. One fixed face determines the three other colors

Define:

    TetraDirection := {d : TrominoState // d != 0}

Prove:

    Fintype.card TetraDirection = 3.

For base face c define:

    tetraOtherFace (c : TetraFace) (d : TetraDirection) : TetraFace :=
      c + d.1.

Prove:

- tetraOtherFace c d != c;
- every face q != c is tetraOtherFace c d for a unique d;
- the map
      d |-> tetraOtherFace c d
  is an equivalence between TetraDirection and {q : TetraFace // q != c}.

At the set level:

    image of the three directions from c
      = univ.erase c.

This is the exact "one face is fixed -> the remaining three colors are
determined as the three alternatives" theorem.

## F. Incident-edge normal form

Define:

    tetraIncidentEdges (c : TetraFace) : Finset TetraEdge :=
      Finset.univ.filter (fun E => c ∈ E.val).

Prove:

    card (tetraIncidentEdges c) = 3.

Prove the delta-image theorem:

    (tetraIncidentEdges c).image tetraEdgeDelta
      = {deltaA, deltaB, deltaC}.

Stronger preferred theorem:

For every nonzero d, there is exactly one incident edge at c with delta d,
namely:

    tetraEdgeBetween c (c + d) ...

Thus each fixed face sees exactly three distinct exit/roll directions.

## G. Bottom-face roll kernel

Define only the color-level rolling kernel, not full 3D tetrahedron
orientation.

    def tetraRollBottom
      (c : TetraFace) (d : TetraDirection) : TetraFace :=
      c + d.1

Prove:

- roll changes the bottom face;
- rolling twice through the same direction returns:
      tetraRollBottom (tetraRollBottom c d) d = c;
- the three legal rolls from c land on exactly the other three faces;
- tetraRollBottom c d = exchange d.1 c.

Define an oriented color-level roll step if useful:

    structure TetraRollStep where
      bottom : TetraFace
      direction : TetraDirection

Prove:

    Fintype.card TetraRollStep = 12.

Important terminology boundary:

12 color-level oriented roll choices are NOT yet identified with the 12
geometric orientation states of a rigid tetrahedron. Do not claim such an
orientation equivalence in this checkpoint.

## H. Roll edge

Define the underlying edge crossed by a roll:

    tetraRollEdge (c : TetraFace) (d : TetraDirection) : TetraEdge :=
      tetraEdgeBetween c (c + d.1) ...

Prove:

    tetraEdgeDelta (tetraRollEdge c d) = d.1.

Reverse calibration:

    tetraRollEdge (c + d.1) d = tetraRollEdge c d.

Thus each unoriented edge corresponds to the same roll in the two travel
directions.

If convenient, prove each TetraEdge has exactly two oriented roll
representations.

## I. Three-nonzero V4 closure theorem

Prove the central finite V4 theorem.

For a b c : TrominoState with:

    ha : a != 0
    hb : b != 0
    hc : c != 0

prove equivalent forms:

    a + b + c = 0

iff

    a, b, c are pairwise distinct

iff

    ({a,b,c} : Finset TrominoState)
      = {deltaA, deltaB, deltaC}.

It is acceptable to expose this as two or three theorems rather than one large
Iff chain.

A finite-case proof is acceptable and expected.

Also prove:

    deltaA + deltaB + deltaC = 0

by reusing the existing theorem rather than duplicating arithmetic.

This is the algebraic core of tetrahedral closure.

## J. Triangular Port face predicate

In PortTriangularTetrahedral.lean define:

    def IsTriangularPortFace
      (F : PortFaceCell R C) : Prop :=
      F.val.card = 3

and:

    def PortAllFacesTriangular
      (M : PortCombinatorialMap P) : Prop :=
      forall F : PortFaceCell M.localRotation M.crossing,
        IsTriangularPortFace F.

Keep this combinatorial: no geometric/topological triangle claim.

## K. Face label image

For:

    A : V4FlowAssignment C
    F : PortFaceCell R C

define:

    facePortLabelSet A F : Finset TrominoState :=
      F.val.image A.label.

Prove:

    facePortLabelSet A F ⊆ {deltaA,deltaB,deltaC}

from A.nonzero and the four-state classification.

For a triangular face, if:

    faceCellLabelSum A R F = 0

prove:

    facePortLabelSet A F = {deltaA,deltaB,deltaC}.

Use:

- F.val.card = 3;
- all A.label q are nonzero;
- the face-cell sum agrees with the sum of labels over the face orbit;
- section I.

Conversely, for triangular F, prove that exact three-label image plus
cardinality 3 implies:

    faceCellLabelSum A R F = 0.

Hence obtain the local normal form:

    IsTriangularPortFace F ->
      (faceCellLabelSum A R F = 0
        <->
       facePortLabelSet A F = {deltaA,deltaB,deltaC}).

## L. No dual loop on a conserved triangular face

Prove:

If F is triangular and faceCellLabelSum A R F = 0, then no crossing pair is
contained entirely in F:

    forall p,
      p ∈ F.val ->
      C.cross p ∉ F.val.

Reason:

- p and C.cross p have the same nonzero label;
- a triangular face would then contain two equal labels;
- section K says a conserved triangular face must have all three distinct
  nonzero labels.

This gives a local theorem that conserved triangular faces are automatically
dual-loop-free.

For a map with all faces triangular and IsDualFaceKirchhoff, derive:

    DualLoopFree M.localRotation M.crossing.

This is important because it recovers the usual loop-free cubic-dual picture
without building a general dual PortNetwork.

## M. Tetrahedral face pattern

Define:

    def IsTetrahedralFacePattern
      (A : V4FlowAssignment C)
      (F : PortFaceCell R C) : Prop :=
      IsTriangularPortFace F /\
      facePortLabelSet A F = {deltaA,deltaB,deltaC}.

Then for a map with PortAllFacesTriangular prove:

    IsDualFaceKirchhoff A M.localRotation
      <->
    forall F, IsTetrahedralFacePattern A F.

Use TRM-038's cell-level/dual-face conservation equivalence.

This theorem is the precise local reformulation:

    every dual vertex is a three-direction A/B/C tetrahedral junction.

## N. Existence predicate for triangular maps

Define:

    def HasTetrahedralFaceAssignment
      (M : PortCombinatorialMap P) : Prop :=
      exists A : V4FlowAssignment M.crossing,
        forall F : PortFaceCell M.localRotation M.crossing,
          IsTetrahedralFacePattern A F.

For a genus-zero map G satisfying PortAllFacesTriangular G.map, prove:

    HasTetrahedralFaceAssignment G.map
      <->
    HasDualFaceKirchhoffV4Assignment G.map.

Then combine TRM-038:

    HasTetrahedralFaceAssignment G.map
      <->
    PortFourStateColorable G.map.crossing.

This is an equivalence of existence problems only.

Do not prove HasTetrahedralFaceAssignment universally.

## O. Tait-style local normal form boundary

Document, but do not overclaim:

For all-triangular Port maps, a face-conservative nowhere-zero V4 assignment
is locally exactly a 3-edge labeling in which each face sees A/B/C once.

This is structurally the same local normal form that appears in Tait-style
reformulations through a cubic dual.

However:

- no general dual PortNetwork is constructed here;
- no theorem identifying this development with a published Tait theorem is
  required;
- no universal 3-edge-colorability theorem is claimed.

Use "Tait-style local normal form" rather than asserting a full Tait
equivalence beyond what is formalized.

## P. Tetrahedron / Port calibration

Construct finite audits showing that the tetrahedron edge-delta rules and a
conserved triangular Port face use the same three labels.

At minimum:

- one fixed tetrahedron face has incident deltas A/B/C;
- triangleColoringAssignment on trianglePortMap has each face label set
  {A,B,C};
- triangleAllDeltaA fails IsTetrahedralFacePattern;
- existing dualFaceKirchhoff theorem for triangleColoringAssignment supplies
  the conservation side.

Do not build a new tetrahedron PortCombinatorialMap unless it is genuinely
useful and cheap.

## Q. Rolling/stamp transport interpretation

Add a small finite transport layer suitable for later game work.

For a list of TetraDirection, define:

    tetraRollBottomList :
      TetraFace -> List TetraDirection -> TetraFace

by repeated tetraRollBottom.

Prove:

    tetraRollBottomList c ds
      =
    c + (ds.map (fun d => d.1)).sum.

Consequences:

- empty route keeps the bottom color;
- concatenation composes by V4 addition;
- a direction sequence with XOR 0 returns the bottom color.

Then connect only at theorem level to existing V4 walk transport:

For a FlowRegionWalk W, the stamped bottom color after following W from
initial color c is:

    c + regionWalkXor W.

Define a simple observer if useful:

    tetraStampColor c W := c + regionWalkXor W.

Prove:

- append law;
- closed W with zero holonomy returns c;
- under a RegionPotential, this agrees with the recovered region color up to
  the expected global gauge/base translation, if a clean existing theorem
  makes this cheap.

Do not model rigid-body orientation yet.

## R. Game-design boundary

The report should explicitly preserve the future puzzle rule:

    "Roll the tetrahedron and stamp every area with a valid color."

Formalized in TRM-039:

- four possible bottom-face colors;
- three legal nontrivial roll directions from every bottom color;
- six underlying tetrahedral edges paired into A/B/C opposite pairs;
- roll color transport is V4 exchange;
- zero-XOR route returns the bottom color.

Not yet formalized:

- 3D orientation state;
- board geometry / embedding;
- physical edge chosen on screen;
- Hamiltonian/one-stroke constraints;
- move minimization;
- UI/game implementation.

## S. Remaining proof gap after TRM-039

The report must end with the exact next fork.

For all-triangular genus-zero maps the remaining existence problem becomes:

    does there always exist a nowhere-zero V4 assignment
    whose three labels around every face are exactly A/B/C?

Two possible next research routes:

1. **Triangulation reduction**
   - reduce arbitrary genus-zero Port maps to an all-triangular carrier while
     preserving/reflecting four-state colorability;

2. **Tetrahedral assignment existence**
   - attack the A/B/C-on-every-triangle existence problem directly, possibly
     using rolling/local exchange constraints.

Do not choose or prove either route in TRM-039.

## T. Axiom / computability policy

All tetrahedral finite objects, roll operations, label-set observers and
triangular predicates must be computable.

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- new noncomputable production declaration.

Classical reasoning inside proofs is allowed when needed for finite orbit
witnesses.

## U. Audit

Create:

- DkMathTest/Tromino/TetrahedralClosureAxiomAudit.lean
- DkMathTest/Tromino/PortTriangularTetrahedralAxiomAudit.lean

Audit at least:

1. TetraFace card = 4;
2. TetraEdge card = 6;
3. all edge deltas nonzero;
4. edge-delta image = {A,B,C};
5. each delta fiber has card 2;
6. opposite-pair/disjoint calibration;
7. TetraDirection card = 3;
8. fixed face -> exactly three other faces;
9. incident edges card = 3;
10. incident delta image = {A,B,C};
11. roll changes bottom face;
12. same-direction double roll returns;
13. TetraRollStep card = 12;
14. roll edge has the requested delta;
15. three-nonzero sum-zero iff A/B/C exactly once;
16. triangular conserved face label set = {A,B,C};
17. converse local normal form;
18. conserved triangular face excludes dual loop;
19. all-triangular + dualFaceKirchhoff -> DualLoopFree;
20. all-triangular dualFaceKirchhoff iff all tetrahedral face patterns;
21. genus-zero HasTetrahedralFaceAssignment iff colorable;
22. triangle coloring fixture has tetrahedral face patterns;
23. triangleAllDeltaA fails the pattern;
24. roll-list XOR formula;
25. zero-XOR roll list returns bottom color.

Run #print axioms on the principal local-normal-form and existence-equivalence
theorems.

## V. Validation

Build:

- DkMath.Tromino.TetrahedralClosure
- DkMath.Tromino.PortTriangularTetrahedral
- DkMathTest.Tromino.TetrahedralClosureAxiomAudit
- DkMathTest.Tromino.PortTriangularTetrahedralAxiomAudit

Regression-build:

- DkMath.Tromino.PortGenusZeroHolonomy
- DkMath.Tromino.PortF2Exactness
- DkMath.Tromino.PortDualityKernel
- DkMath.Tromino.PortTensionColoring
- DkMath.Tromino.LocalFrameEquiv

Run:

- git diff --check
- production forbidden-construct scan
- #print axioms audit.

## W. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-038.md

Record:

- tetrahedron 4-face / 6-edge carrier;
- 6 = 2+2+2 edge-delta pairing;
- fixed-face three-direction theorem;
- bottom-face roll kernel;
- three-nonzero V4 closure theorem;
- triangular Port face normal form;
- automatic local dual-loop exclusion;
- all-triangular face-conservation <-> tetrahedral A/B/C pattern;
- existence equivalence with four-state colorability on genus-zero triangular
  maps;
- triangle fixture calibration;
- rolling/stamp game interpretation;
- exact remaining fork: triangulation reduction vs tetrahedral assignment
  existence.

## Stop condition

Stop once the tetrahedral finite closure and the triangular-face A/B/C normal
form are kernel-checked and connected to the existing genus-zero
face-conservation/coloring equivalence.

Do not prove universal tetrahedral assignment existence, arbitrary-map
triangulation reduction, a general dual PortNetwork, rigid tetrahedron
orientation, topological realization, or the Four Color theorem without
review.
