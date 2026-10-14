
# TRM-032 — Kirchhoff V4 flow kernel / tension separation

## Goal

Introduce the **true Kirchhoff-style nowhere-zero V4 flow condition** on the
label-free PortNetwork layer, and formally separate it from the zero-holonomy
V4 tension of TRM-031.

TRM-031 established:

    zero-holonomy nowhere-zero V4 tension
      <-> proper TrominoState coloring.

TRM-032 must not reuse the word "flow" for that condition.

A Kirchhoff V4 flow is an edge assignment whose incident labels sum to zero
at every vertex/region.

Because TrominoState = ZMod 2 x ZMod 2 has characteristic two, orientation
signs disappear:

    -x = x.

Therefore the existing V4FlowAssignment reversal law

    label(cross p) = label(p)

is compatible with an undirected V4 flow.  The new ingredient is local vertex
conservation.

Do not implement planar duality yet.
Do not prove any universal genus-zero flow existence statement.

## Production

Create:

DkMath/Tromino/PortKirchhoffFlow.lean

Import:

- PortCombinatorialMap;
- PortTensionColoring as needed for explicit separation theorems / fixtures.

## A. Vertex Kirchhoff sum

For P : PortNetwork, C : PortCrossing P, and
A : V4FlowAssignment C define:

    vertexKirchhoffSum A r
      :=
    sum over i : Fin (P.arity r) of A.label <r,i>.

Use Finset.univ.

Required theorem/readability API:

- explicit sum formula;
- the sum depends only on incident port labels;
- crossing orientation does not enter the vertex sum.

## B. Kirchhoff flow predicate

Define:

    IsKirchhoffV4Flow A : Prop :=
      forall r, vertexKirchhoffSum A r = 0.

For a strong map define:

    HasKirchhoffV4Flow M : Prop :=
      exists A : V4FlowAssignment M.crossing,
        IsKirchhoffV4Flow A.

Document carefully:

- nowhere-zero is already part of V4FlowAssignment;
- cross_sameLabel is the characteristic-two reversal law;
- IsKirchhoffV4Flow is the vertex conservation law.

This is distinct from IsZeroHolonomyV4Tension.

## C. Local FlowSignature calibration

If clean, define the local signature induced by A at region r:

    assignmentFlowSignature A r : FlowSignature

with:

- arity := P.arity r;
- label i := A.label <r,i>;
- nonzero from A.nonzero.

Prove:

    vertexKirchhoffSum A r
      =
    flowSum (assignmentFlowSignature A r).

Hence:

    IsKirchhoffV4Flow A
      iff
    forall r, FlowConserved (assignmentFlowSignature A r).

This reuses the existing V4 parity algebra without conflating global
zero-holonomy with local conservation.

## D. Parity characterization

Using FlowSignature results where practical, prove for every region r:

    vertexKirchhoffSum A r = 0

iff the parity condition on the deltaA/deltaB/deltaC counts holds.

Preferred readable form:

    countA % 2 = countC % 2
    and
    countB % 2 = countC % 2.

If a direct wrapper around flowConserved_iff_parity is easy, use it.

This is useful later for local flow construction.

## E. Structural invariance

Kirchhoff flow is a property of:

    PortNetwork + PortCrossing + V4FlowAssignment

and does not require:

- rotation;
- faces;
- genus;
- holonomy.

Expose a theorem/remark that changing PortLocalRotation on the same P,C,A
cannot affect IsKirchhoffV4Flow.

No substantial API is needed if this is definitionally obvious.

## F. Triangle structural fixture

Create a pure Port fixture representing a 3-cycle:

- 3 regions;
- arity 2 at every region;
- three crossing edge pairs:
    0--1,
    1--2,
    2--0;
- local rotation swaps the two ports at each region.

Suggested port indexing:

- region 0 port 0 <-> region 1 port 0;
- region 1 port 1 <-> region 2 port 0;
- region 2 port 1 <-> region 0 port 1.

Construct:

- trianglePortNetwork;
- trianglePortCrossing;
- trianglePortRotationSystem;
- trianglePortCombinatorialMap.

Kernel-check:

- connectedness;
- V = 3;
- E = 3;
- D = 6;
- faceStep has two 3-cycles;
- F = 2;
- chi = 2;
- PortHasCombinatorialGenus 0;
- PortHasSphereCharacteristic.

This is a valid strong genus-zero combinatorial calibration.

## G. Triangle all-deltaA: Kirchhoff but not tension

Define:

    triangleAllDeltaA : V4FlowAssignment trianglePortCrossing

with every edge/port label deltaA.

Prove:

At each degree-2 vertex,

    deltaA + deltaA = 0,

hence:

    IsKirchhoffV4Flow triangleAllDeltaA.

Then construct the closed triangle PortRegionWalk / lifted FlowRegionWalk:

    0 -> 1 -> 2 -> 0

using one port from each edge.

Prove its XOR is:

    deltaA + deltaA + deltaA = deltaA != 0.

Therefore:

    not IsZeroHolonomyV4Tension triangleAllDeltaA.

This establishes:

    Kirchhoff flow does not imply tension.

Do not use a generic non-implication axiom; use the explicit fixture.

## H. Existing 2x3 all-deltaA: tension but not Kirchhoff

On the existing 2-region x 3-parallel-edge structural map, define or reuse an
all-deltaA assignment.

Prove it is a zero-holonomy tension via the explicit proper coloring from
TRM-031.

At either degree-3 region:

    deltaA + deltaA + deltaA = deltaA != 0.

Therefore it is not a Kirchhoff flow.

This establishes:

    tension does not imply Kirchhoff flow.

Again use the explicit fixture.

## I. Formal incomparability theorem package

Expose theorem-level examples such as:

    exists A,
      IsKirchhoffV4Flow A
      and not IsZeroHolonomyV4Tension A

and:

    exists A,
      IsZeroHolonomyV4Tension A
      and not IsKirchhoffV4Flow A.

These may be fixture-specific theorems rather than fully existentially
packaged if dependent types make the latter awkward.

The report must state clearly:

    tension and Kirchhoff flow are incomparable on the same primal graph.

## J. Balanced three-label flow on the 2x3 map

Define a useful assignment on the 2x3 parallel-edge map with edge labels:

    deltaA, deltaB, deltaC

on the three crossing edge pairs.

Use the identity:

    deltaA + deltaB + deltaC = 0.

Prove:

    IsKirchhoffV4Flow balancedThreeLabelAssignment.

This fixture is important because it previews planar duality:

- triangle proper coloring can induce edge differences deltaA/deltaB/deltaC;
- the corresponding three labels on the 2-vertex, 3-parallel-edge graph obey
  Kirchhoff conservation.

Do not yet formalize the dual-map correspondence in production.

## K. Triangle proper coloring and tension preview

Construct an explicit proper coloring of the triangle, for example:

    vertex 0 -> 0
    vertex 1 -> deltaA
    vertex 2 -> deltaB

Then the three primal tension edge labels are:

- edge 0--1: deltaA;
- edge 1--2: deltaC;
- edge 2--0: deltaB.

Audit these values.

Record that the same multiset {deltaA,deltaB,deltaC} is exactly the balanced
Kirchhoff assignment on the 2x3 parallel-edge graph.

This is an audit-level preview only, not a duality theorem.

## L. No false implication from genus zero

The triangle all-deltaA example is genus-zero but its Kirchhoff flow is not a
tension.

Therefore do not define or prove any theorem suggesting:

    genus zero + Kirchhoff flow
      -> coloring

on the same primal graph.

The coloring relation is expected to arise only after planar/combinatorial
duality.

## M. Bridge / loop warning for future duality

The report must flag an important structural issue.

PortCrossing currently requires:

    (cross p).1 != p.1.

Thus PortNetwork cannot represent loop edges.

Under planar duality, a bridge in the primal graph becomes a loop in the dual.

Therefore a future general dual-map construction must either:

1. restrict to a bridge-free class where the dual has no loops; or
2. generalize the structural carrier/crossing API to allow dual loops.

Do not solve this in TRM-032.

This warning is mandatory before dual-map work begins.

## N. Mathlib terminology

Record:

- current Mathlib survey did not identify a ready-made nowhere-zero
  graph-flow/tension API;
- DkMath therefore defines the V4 Kirchhoff law explicitly.

Use "Kirchhoff V4 flow" for the local conservation object.
Use "V4 tension" for the zero-holonomy/coboundary object.

## O. Computability / axioms

All new definitions should be computable.

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- new noncomputable production declaration.

## P. Audit

Create:

DkMathTest/Tromino/PortKirchhoffFlowAxiomAudit.lean

Audit at least:

1. vertexKirchhoffSum formula;
2. local FlowSignature calibration;
3. local parity characterization;
4. triangle strong-map counts V/E/F/D/chi;
5. triangle genus zero / sphere characteristic;
6. triangle all-deltaA is Kirchhoff;
7. triangle all-deltaA is not zero-holonomy tension;
8. 2x3 all-deltaA is tension;
9. 2x3 all-deltaA is not Kirchhoff;
10. balanced deltaA/deltaB/deltaC assignment on 2x3 is Kirchhoff;
11. explicit triangle coloring gives edge tensions deltaA/deltaC/deltaB;
12. no theorem derives same-primal coloring from Kirchhoff flow.

## Q. Validation

Build:

- DkMath.Tromino.PortKirchhoffFlow
- DkMathTest/Tromino.PortKirchhoffFlowAxiomAudit

Regression-build:

- DkMath.Tromino.PortTensionColoring
- DkMathTest/Tromino.PortTensionColoringAxiomAudit
- DkMath.Tromino.PortCombinatorialMap
- DkMathTest/Tromino.PortCombinatorialMapAxiomAudit

Run git diff --check, forbidden-construct scan, and #print axioms.

## R. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-031.md

Record:

- Kirchhoff V4 flow definition;
- characteristic-two orientation convention;
- local parity theorem;
- tension vs flow incomparability;
- triangle genus-zero fixture;
- 2x3 parallel-edge fixture;
- balanced three-label flow;
- triangle-coloring / 2x3-flow duality preview;
- bridge -> dual-loop structural warning;
- recommended next checkpoint for dual-map architecture.

## Stop condition

Stop once true Kirchhoff V4 flow is formally distinct from zero-holonomy V4
tension, with explicit examples in both non-implication directions.

Do not implement combinatorial duality, bridge reduction, loop-capable maps,
universal flow existence, topological realization, or Four-Color theorem
results without review.
