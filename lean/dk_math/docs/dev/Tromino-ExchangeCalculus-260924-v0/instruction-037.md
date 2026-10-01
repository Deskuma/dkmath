
# TRM-038 — Genus-zero face conservation / zero-holonomy closure

## Goal

Use the genus-zero F2 exactness theorem from TRM-037 to close the converse
direction left open since TRM-033:

    zero holonomy
      -> face-boundary V4 conservation

was already proved generally as:

    tension_implies_dualFaceKirchhoff.

TRM-038 must prove, for connected strong genus-zero Port combinatorial maps:

    face-boundary V4 conservation
      -> zero holonomy.

Hence, for every fixed nowhere-zero V4 assignment A on a genus-zero map:

    IsDualFaceKirchhoff A G.map.localRotation
      <->
    IsZeroHolonomyV4Tension A.

Then reconnect this to TRM-031 and obtain a fixed-assignment coloring
reconstruction theorem and an existential equivalence:

    exists face-conservative nowhere-zero V4 assignment
      <->
    proper four-state coloring.

This checkpoint does NOT prove the existential left-hand side for all
genus-zero maps.  Therefore it does not prove the Four Color theorem.

## Production

Create:

DkMath/Tromino/PortGenusZeroHolonomy.lean

Import:

- DkMath.Tromino.PortF2Exactness
- DkMath.Tromino.PortDualityKernel
- DkMath.Tromino.PortTensionColoring
- DkMath.Tromino.PortV4Chains

The proof should reuse the scalar F2 exactness theorem rather than duplicate
the rank argument.

## A. Canonical computable edge label from a V4 assignment

The F2 chain basis is PortEdgeCell, while V4FlowAssignment labels ports.
Construct a representative-free, computable edge label without Classical.choice.

For:

    A : V4FlowAssignment C
    E : PortEdgeCell C

define:

    assignmentEdgeLabel A E : TrominoState

by summing over the two ports of E and selecting the unique port whose source
region index is smaller than its crossed target:

    sum p in E.val,
      if p.1 < (C.cross p).1 then A.label p else 0.

This works because PortCrossing.changesRegion gives unequal endpoint regions,
so exactly one of p and C.cross p satisfies the strict order.

Required theorem:

    assignmentEdgeLabel_edgeCellOfPort
      (A : V4FlowAssignment C) (p : PortNetworkPort P) :
      assignmentEdgeLabel A (edgeCellOfPort C p) = A.label p.

The proof must use:

- edgeCellOfPort is the crossing pair {p, C.cross p};
- C.involutive;
- C.changesRegion;
- A.cross_sameLabel.

Also prove:

    assignmentEdgeLabel_edgeCellOfPort_cross

as a calibration, preferably by rewriting edgeCellOfPort_cross.

Do not introduce a noncomputable edge representative.

## B. Linear evaluation of scalar edge chains in V4

Define:

    portEdgeLabelEval (A : V4FlowAssignment C) :
      PortEdgeChain C ->ₗ[PortF2] TrominoState

by:

    portEdgeLabelEval A x
      :=
    sum E, x E • assignmentEdgeLabel A E.

Required linearity theorems are inherited from the LinearMap structure.

Expose:

    portEdgeLabelEval_apply.

For the edge basis associated to p prove:

    portEdgeLabelEval A
      (fun E => if edgeCellOfPort C p = E then 1 else 0)
      =
    A.label p.

Then combine with portWalkEdgeChain_singleton:

    portEdgeLabelEval_singleton.

## C. Evaluation of arbitrary structural walks

Prove a list-level helper, preferably without requiring walk validity:

    portEdgeLabelEval_walkEdgeCoeff
      (A : V4FlowAssignment C)
      (xs : List (PortNetworkPort P)) :
      portEdgeLabelEval A
        (fun E => walkEdgeCoeff C E xs)
      =
      (xs.map A.label).sum.

Prove by induction on xs:

- cons decomposes the edge-parity chain into one singleton indicator plus the
  tail;
- linearity of portEdgeLabelEval;
- section B evaluates the singleton;
- repeated traversals automatically cancel modulo 2.

Then for every structural walk:

    portEdgeLabelEval_portWalkEdgeChain
      (A : V4FlowAssignment C)
      (W : PortRegionWalk C r s) :
      portEdgeLabelEval A (portWalkEdgeChain W)
      =
      regionWalkXor (W.toFlowRegionWalk A).

This theorem is the main bridge from F2 cycle chains back to V4 transport.

Also prove the Flow->Port round-trip form:

    portEdgeLabelEval_flowWalk
      (W : FlowRegionWalk A.toFlowCrossing r s) :
      portEdgeLabelEval A
        (portWalkEdgeChain W.toPortRegionWalk)
      =
      regionWalkXor W.

Use the existing walk round-trip theorem rather than reproving validity.

## D. Face-cell V4 evaluation

Define:

    faceCellLabelSum
      (A : V4FlowAssignment C)
      (R : PortLocalRotation P)
      (F : PortFaceCell R C) : TrominoState :=
    portEdgeLabelEval A (faceBoundaryEdgeChain F).

This is representative-free.

For every port p prove:

    faceCellLabelSum A R (faceCellOfPort R C p)
      =
    faceBoundaryLabelSum A R p.

Preferred proof chain:

    faceBoundaryEdgeChain_eq_walk
    -> portEdgeLabelEval_portWalkEdgeChain
    -> faceBoundaryWalk_xor_eq_labelSum.

Then prove representative invariance as a corollary.

## E. Cell-level face conservation

Define:

    IsFaceCellKirchhoff
      (A : V4FlowAssignment C)
      (R : PortLocalRotation P) : Prop :=
    forall F : PortFaceCell R C,
      faceCellLabelSum A R F = 0.

Prove:

    isFaceCellKirchhoff_iff_dualFaceKirchhoff :
      IsFaceCellKirchhoff A R
        <->
      IsDualFaceKirchhoff A R.

For the direction from IsDualFaceKirchhoff to cells, choose a face-orbit
representative only inside the proof using the face-cell witness.

No noncomputable production definition is needed.

This theorem reconciles the orbit-cell language of TRM-037 with the
port-representative language of TRM-033.

## F. Boundary2/evaluation adjunction formula

Prove the key linear identity:

    portEdgeLabelEval A (portBoundary2 R C y)
      =
    sum F : PortFaceCell R C,
      y F • faceCellLabelSum A R F.

Preferred proof:

- rewrite portBoundary2_as_sum_basis;
- apply linearity of portEdgeLabelEval;
- unfold faceCellLabelSum.

Then prove:

    portEdgeLabelEval_boundary2_eq_zero_of_faceKirchhoff
      (hface : IsFaceCellKirchhoff A R) :
      forall y,
        portEdgeLabelEval A (portBoundary2 R C y) = 0.

Equivalent theorem using IsDualFaceKirchhoff is also required.

Interpretation:

    face-conservative assignments annihilate the whole F2 face-boundary space.

## G. Genus-zero exactness kills every closed-walk XOR

For:

    G : PortGenusZeroCombinatorialMap P
    A : V4FlowAssignment G.map.crossing
    hface : IsDualFaceKirchhoff A G.map.localRotation

and a closed structural walk:

    W : PortRegionWalk G.map.crossing r r

prove:

    regionWalkXor (W.toFlowRegionWalk A) = 0.

Proof route:

1. TRM-037:
       portWalkEdgeChain W ∈ PortFaceBoundarySpace ...
2. unpack range membership:
       exists y, portBoundary2 y = portWalkEdgeChain W;
3. evaluate both sides with portEdgeLabelEval A;
4. section F kills the boundary2 side;
5. section C identifies the walk side with regionWalkXor.

Package this theorem with a clear name such as:

    portGenusZero_closedWalk_xor_eq_zero_of_dualFaceKirchhoff.

## H. Flow closed-walk zero holonomy

Lift section G to arbitrary FlowRegionWalks on A.toFlowCrossing.

For:

    W : ClosedRegionWalk A.toFlowCrossing r

use:

    W.toPortRegionWalk

and the exact Flow/Port round-trip theorems.

Prove the principal converse:

    portGenusZero_zeroHolonomy_of_dualFaceKirchhoff
      (G : PortGenusZeroCombinatorialMap P)
      (A : V4FlowAssignment G.map.crossing)
      (hface : IsDualFaceKirchhoff A G.map.localRotation) :
      IsZeroHolonomyV4Tension A.

This theorem is the first main endpoint of TRM-038.

## I. Fixed-assignment equivalence

The forward direction already exists for every map:

    tension_implies_dualFaceKirchhoff.

Combine it with section H and prove:

    portGenusZero_dualFaceKirchhoff_iff_zeroHolonomy
      (G : PortGenusZeroCombinatorialMap P)
      (A : V4FlowAssignment G.map.crossing) :
      IsDualFaceKirchhoff A G.map.localRotation
        <->
      IsZeroHolonomyV4Tension A.

This should be a short theorem reusing the two directions.

This is the principal conceptual theorem:

    on genus zero,
    local face conservation is equivalent to global path integrability.

## J. Coloring reconstruction from face conservation

Use TRM-031's:

    exists_portColoring_of_zeroHolonomyV4Tension

and section H to prove:

    exists_portColoring_of_dualFaceKirchhoff
      (G : PortGenusZeroCombinatorialMap P)
      (A : V4FlowAssignment G.map.crossing)
      (hface : IsDualFaceKirchhoff A G.map.localRotation) :
      exists K : (portRegionSimpleGraph G.map.crossing).Coloring TrominoState,
        forall p,
          (coloringToV4Assignment K).label p = A.label p.

Thus the recovered proper coloring reproduces the supplied V4 edge labels
exactly.

Also provide the weaker existence-only corollary:

    PortFourStateColorable G.map.crossing.

## K. Existential dual-face Kirchhoff target

Define for any strong map:

    def HasDualFaceKirchhoffV4Assignment
      (M : PortCombinatorialMap P) : Prop :=
      exists A : V4FlowAssignment M.crossing,
        IsDualFaceKirchhoff A M.localRotation.

The name must make clear this is an assignment on the primal Port carrier
with conservation on primal face orbits, i.e. at would-be dual vertices.

Do NOT call it HasKirchhoffV4Flow on an actual dual PortNetwork, because no
general dual PortNetwork has been constructed.

For genus zero prove:

    PortGenusZeroCombinatorialMap.dualFaceKirchhoff_iff_colorable :
      HasDualFaceKirchhoffV4Assignment G.map
        <->
      PortFourStateColorable G.map.crossing.

Proof:

- left -> section J;
- right -> coloringToV4Assignment_isZeroHolonomy followed by
  tension_implies_dualFaceKirchhoff.

This is an equivalence of existence problems, not an existence theorem.

## L. Universal target equivalence

Define:

    PortGenusZeroDualFaceKirchhoffTarget : Prop :=
      forall (P : PortNetwork) (G : PortGenusZeroCombinatorialMap P),
        HasDualFaceKirchhoffV4Assignment G.map.

Reuse the existing:

    PortGenusZeroFourColorTarget.

Prove:

    portGenusZeroDualFaceKirchhoffTarget_iff_fourColorTarget :
      PortGenusZeroDualFaceKirchhoffTarget
        <->
      PortGenusZeroFourColorTarget.

Do NOT prove either side.

This theorem should isolate the remaining global problem as:

    existence of a nowhere-zero V4 assignment
    satisfying face-orbit Kirchhoff conservation.

## M. Relation to primal Kirchhoff flow

Keep terminology separated.

For the same assignment A there are now three predicates:

1. IsKirchhoffV4Flow A
     local conservation at primal vertices;

2. IsDualFaceKirchhoff A R
     local conservation at primal faces / dual vertices;

3. IsZeroHolonomyV4Tension A
     global closed-walk integrability on the primal graph.

On genus zero, TRM-038 proves (2) <-> (3).

It does NOT prove (1) <-> (2).

Add documentation and at least one fixture audit preserving this distinction.

Recommended audit:

- triangleAllDeltaA from TRM-032 is primal Kirchhoff;
- it is not zero holonomy;
- therefore by section I it is not dual-face Kirchhoff on the genus-zero
  triangle map.

This is a valuable no-confusion theorem.

## N. Triangle coloring calibration

For the proper triangle coloring assignment:

    coloringToV4Assignment triangleColoring

audit:

- zero holonomy;
- dual-face Kirchhoff;
- face-cell conservation;
- coloring reconstruction theorem can recover a coloring with the same labels.

Use existing triangle fixtures rather than rebuilding them.

## O. Optional V4/F2 coordinate calibration

If clean, prove that portEdgeLabelEval decomposes coordinatewise under:

    TrominoState = PortF2 × PortF2.

For example define scalar evaluation maps:

    portEdgeLabelEvalFst A
    portEdgeLabelEvalSnd A

and prove:

    (portEdgeLabelEval A x).1 = portEdgeLabelEvalFst A x
    (portEdgeLabelEval A x).2 = portEdgeLabelEvalSnd A x.

This is optional; do not make GREEN depend on it.

The main proof should remain assignment/evaluation based.

## P. Tetrahedral rolling interpretation

Do not implement TetraRoll in this checkpoint.

Record the following now-formal interpretation in the report:

- one tetrahedron roll across an area boundary contributes one nonzero V4
  edge delta;
- a rolling route is a RegionWalk;
- the stamped bottom-face color is a RegionPotential state;
- IsDualFaceKirchhoff says every elementary face boundary has zero accumulated
  V4 delta;
- TRM-037 + TRM-038 say that on genus zero this forces every closed rolling
  route to have zero color holonomy;
- hence a face-conservative roll system admits a globally consistent
  four-state coloring.

Full tetrahedron orientation has more state than bottom-face color, so
orientation holonomy is explicitly stronger and remains outside this theorem.

This interpretation is suitable for the future puzzle/game track:

    "roll the tetrahedron and stamp every area with a valid color."

## Q. Four Color boundary

The report and module docstring must explicitly state:

TRM-038 does NOT prove that every genus-zero Port combinatorial map admits a
face-conservative V4 assignment.

It proves only:

    such an assignment exists
      <->
    the map is four-state colorable.

Therefore the remaining theorem-strength gap is exactly:

    PortGenusZeroDualFaceKirchhoffTarget.

Do not state or imply that this target has been proved.

Likewise do not claim topological planarity/sphere realization beyond the
existing combinatorial genus-zero certificate.

## R. Computability / axioms

Core definitions:

- assignmentEdgeLabel;
- portEdgeLabelEval;
- faceCellLabelSum;
- IsFaceCellKirchhoff;
- HasDualFaceKirchhoffV4Assignment

must be computable.

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- new noncomputable production declaration.

Classical reasoning may be used inside proofs for face-orbit witnesses.

## S. Audit

Create:

DkMathTest/Tromino/PortGenusZeroHolonomyAxiomAudit.lean

Audit at least:

1. assignmentEdgeLabel generated-edge theorem;
2. crossing orientation gives the same edge label;
3. edge-basis evaluation = A.label p;
4. list/walk evaluation theorem;
5. Flow/Port walk evaluation theorem;
6. faceCellLabelSum representative theorem;
7. IsFaceCellKirchhoff iff IsDualFaceKirchhoff;
8. boundary2/evaluation adjunction;
9. face conservation annihilates the face-boundary space;
10. genus-zero closed structural walk XOR = 0;
11. dualFaceKirchhoff -> zero holonomy;
12. genus-zero dualFaceKirchhoff iff zero holonomy;
13. coloring reconstruction with exact label recovery;
14. HasDualFaceKirchhoffV4Assignment iff PortFourStateColorable;
15. universal target iff existing four-color target;
16. triangle proper-coloring assignment is dual-face Kirchhoff;
17. triangle all-deltaA is primal Kirchhoff but not dual-face Kirchhoff;
18. no theorem proving PortGenusZeroDualFaceKirchhoffTarget itself.

Run #print axioms on the principal converse, equivalence, reconstruction and
target-equivalence theorems.

## T. Validation

Build:

- DkMath.Tromino.PortGenusZeroHolonomy
- DkMathTest/Tromino/PortGenusZeroHolonomyAxiomAudit

Regression-build:

- DkMath.Tromino.PortF2Exactness
- DkMath.Tromino.PortDualityKernel
- DkMath.Tromino.PortTensionColoring
- DkMath.Tromino.PortKirchhoffFlow
- DkMath.Tromino.PortV4Chains
- DkMath.Tromino.IntegralMod2Bridge

Run:

- git diff --check
- production forbidden-construct scan
- #print axioms audit.

## U. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-037.md

Record:

- canonical computable edge-label extraction;
- F2 edge-chain -> V4 evaluation;
- structural-walk evaluation = regionWalkXor;
- face-cell label sum and representative independence;
- face-conservation annihilation of im ∂2;
- use of TRM-037 exactness;
- genus-zero dualFaceKirchhoff -> zero holonomy;
- fixed-assignment equivalence;
- coloring reconstruction with label recovery;
- existential and universal target equivalences;
- explicit distinction from primal Kirchhoff flow;
- tetrahedral rolling/stamp interpretation;
- exact remaining gap: existence of a face-conservative nowhere-zero V4
  assignment for every genus-zero map.

## Stop condition

Stop once the genus-zero equivalence

    IsDualFaceKirchhoff A G.map.localRotation
      <->
    IsZeroHolonomyV4Tension A

and its coloring/target corollaries are kernel-checked.

Do not prove the universal existence target, a Four Color theorem endpoint,
a general dual PortNetwork constructor, topological realization, or full
tetrahedral rolling mechanics without review.
