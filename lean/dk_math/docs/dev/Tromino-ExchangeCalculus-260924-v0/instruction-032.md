
# TRM-033 — Face-boundary duality kernel / triangle dual calibration

## Goal

Build the first genuine combinatorial-duality layer without yet constructing a
general dual PortNetwork.

TRM-032 separated:

- primal V4 tension / coboundary;
- primal Kirchhoff V4 flow.

TRM-033 should formalize the permutation-level duality already present in a
rotation system:

    alpha := crossing involution
    rho   := local vertex rotation
    phi   := rho ∘ alpha = primal face step.

The dual map should use:

    alpha* := alpha
    rho*   := phi.

Then the raw dual face step is:

    phi* = rho* ∘ alpha*
         = (rho ∘ alpha) ∘ alpha
         = rho.

Thus:

- primal faces become dual vertices;
- primal vertices become dual faces;
- edges are unchanged.

This checkpoint should formalize that orbit-level duality and the induced
face-boundary conservation law.

Do not yet construct a general dual PortNetwork indexed by Fin.
Do not prove universal flow existence or Four Color.

## Production

Create:

DkMath/Tromino/PortDualityKernel.lean

Import:

- PortKirchhoffFlow;
- PortFaceOrbit;
- PortEulerCount;
- PortRegionWalk.

## A. Raw dual rotation permutation

For P : PortNetwork, R : PortLocalRotation P, C : PortCrossing P define:

    dualRotationEquiv R C := portFaceEquiv R C.

This is an equivalence of the same dart/port carrier.

Provide:

    dualRotationStep R C p = portFaceStep R C p.

Do not package it as PortLocalRotation on the original PortNetwork, because it
does not preserve primal regions; it preserves primal face-orbit classes.

## B. Raw dual face-step identity

Define the raw dual face-step on the same port carrier:

    dualFaceStepRaw R C p :=
      dualRotationEquiv R C (C.cross p).

Prove the central identity:

    dualFaceStepRaw R C p = R.rotate p.

Also package an Equiv if useful and prove the iterate identity:

    (dualFaceStepRaw R C)^[n] p = (R.rotate^[n]) p.

This is the permutation-level heart of duality.

## C. Dual vertex relation = primal face relation

Define:

    SameDualVertex R C p q :=
      SamePortFaceOrbit R C p q.

Use portFaceOrbitSetoid as the dual-vertex equivalence relation.

Prove:

- dualRotationEquiv preserves each SameDualVertex class;
- every q in the same primal face orbit is reached by an iterate of the dual
  rotation;
- dual vertex class size equals primal face length.

No Fin-indexed dual vertex type is needed yet.

## D. Dual face relation = primal vertex relation

For a strong PortRotationSystem R define:

    SameDualFace R p q :=
      p.1 = q.1.

Using dualFaceStepRaw = R.rotate and R.cyclic, prove:

    p and q lie in the same dual-face orbit
      iff
    p.1 = q.1.

If a dedicated orbit definition for dualFaceStepRaw is cumbersome, prove the
two reachability directions directly.

Interpretation:

    dual faces are exactly primal vertex/region rotation cycles.

## E. Orbit-count swap

For M : PortCombinatorialMap P define arithmetic observers:

    dualVertexCount M := M.faceCount
    dualEdgeCount   M := M.edgeCount
    dualFaceCount   M := M.vertexCount
    dualPortCount   M := M.portCount

and:

    dualEulerCharacteristic M :=
      dualVertexCount M - dualEdgeCount M + dualFaceCount M.

Prove:

    dualEulerCharacteristic M = M.eulerCharacteristic.

This is an orbit-count identity only; no topological realization is claimed.

## F. Face-boundary walk

For R : PortLocalRotation P, C : PortCrossing P, and p : PortNetworkPort P,
construct a closed structural walk following one primitive face orbit:

    portFaceBoundaryWalk R C p :
      PortRegionWalk C p.1 p.1.

Its ordered edges should be:

    p,
    phi p,
    phi^2 p,
    ...
    phi^(n-1) p

where n = firstPortFaceReturn R C p.

Prove:

- length = firstPortFaceReturn R C p;
- every listed port belongs to portFaceOrbit R C p;
- its underlying set/Finset of ports is exactly portFaceOrbit R C p if a
  clean theorem is practical.

The validity proof should use:

    source(phi q) = target(q)

and the primitive return at the final edge.

## G. Face-boundary label sum

For A : V4FlowAssignment C define:

    faceBoundaryLabelSum A R C p :=
      sum q in portFaceOrbit R C p, A.label q.

Lift portFaceBoundaryWalk through A and prove:

    regionWalkXor (lifted face-boundary walk)
      =
    faceBoundaryLabelSum A R C p.

The proof should use distinctness of the primitive orbit so each dart is
counted once.

## H. Tension implies dual vertex Kirchhoff conservation

Define the orbit-level dual conservation predicate:

    IsDualFaceKirchhoff A R C : Prop :=
      forall p, faceBoundaryLabelSum A R C p = 0.

Then prove:

    IsZeroHolonomyV4Tension A
      ->
    IsDualFaceKirchhoff A R C.

This theorem is fundamental.

Interpretation:

    primal tension
      ->
    Kirchhoff conservation at every dual vertex (primal face).

This direction does not require genus zero.

Do not prove the converse yet.

## I. Dual-loop structural predicate

Define:

    IsDualLoopPort R C p : Prop :=
      SamePortFaceOrbit R C p (C.cross p).

Equivalently, the two darts of one primal edge lie in the same primal face
orbit, so that edge would become a loop at one dual vertex.

Define:

    DualLoopFree R C : Prop :=
      forall p, not IsDualLoopPort R C p.

Prove:

- the property is invariant under crossing p -> C.cross p;
- if IsDualLoopPort holds, both ports of crossingEdgePair C p lie in the same
  face orbit;
- the edge-pair label sum is zero for any V4FlowAssignment because the two
  labels agree and characteristic two cancels.

Do not claim IsDualLoopPort iff primal bridge yet.

The report may say it is the exact combinatorial obstruction to representing
the dual again with the current loop-forbidding PortCrossing type.

## J. Triangle dual-loop-free calibration

For the TRM-032 triangle map prove:

    DualLoopFree trianglePortRotation trianglePortCrossing.

Its two primal faces are distinct across every edge.

## K. Concrete triangle dual Port map

Build a **fixture-specific** dual PortNetwork for the triangle.

This is not yet a general dual constructor.

Use:

- 2 dual regions = the two triangle face orbits;
- arity 3 at each dual region;
- 3 crossing edge pairs;
- local rotation induced by the primal face-step order.

A convenient indexing is:

dual region 0:
    index 0 <-> t00
    index 1 <-> t20
    index 2 <-> t10

dual region 1:
    index 0 <-> t01
    index 1 <-> t11
    index 2 <-> t21

Crossing must follow the primal alpha pairings:

    t00 <-> t21
    t20 <-> t11
    t10 <-> t01

so the dual crossing pairs indices:

    0 <-> 2
    1 <-> 1
    2 <-> 0

across the two dual regions.

Local dual rotation should cycle:

    0 -> 1 -> 2 -> 0

at each dual region.

Package a strong PortCombinatorialMap and kernel-check:

    V* = 2
    E* = 3
    F* = 3
    D* = 6
    chi* = 2.

This is the actual combinatorial dual calibration of the triangle.

## L. Distinguish from the old 2x3 genus-1 fixture

Explicitly audit/document:

- the old portThreeMap has the same underlying vertex/edge multiplicities
  (2 regions, 3 parallel edges);
- but its crossing/rotation permutation data differ;
- old portThreeMap has F = 1 and chi = 0;
- triangleDualMap has F = 3 and chi = 2.

Therefore "same multigraph shape" does not determine the combinatorial
embedding/dual structure.

This distinction is mandatory.

## M. Triangle coloring -> dual balanced Kirchhoff flow

Take the explicit triangle coloring from TRM-032.

Its primal tension labels on the three edge pairs are deltaA/deltaB/deltaC
(up to the established edge order).

Transport those labels to the concrete triangle dual fixture using the fixed
port correspondence.

Define a V4FlowAssignment on triangleDualMap.crossing and prove:

    IsKirchhoffV4Flow dualAssignment.

At each dual degree-3 vertex the incident labels are exactly:

    deltaA, deltaB, deltaC

and:

    deltaA + deltaB + deltaC = 0.

This is the first kernel-checked concrete instance of:

    primal coloring/tension -> dual Kirchhoff flow.

Do not generalize it to all maps in this checkpoint.

## N. Double-dual permutation identity

At the raw permutation level, prove that dualizing twice restores the primal
rotation:

    rho** = rho.

Concretely, since:

    rho* = rho ∘ alpha
    phi* = rho
    rho** = phi*,

derive the pointwise identity.

A small theorem on Equiv composition is sufficient.

This does not require constructing a second PortNetwork.

## O. Converse boundary

Do not prove:

    IsDualFaceKirchhoff -> IsZeroHolonomyV4Tension.

That converse is expected to require a genus-zero / cycle-space generation
argument: face boundaries must generate all closed cycles.

Record this as the next mathematical gap.

Likewise do not prove a general dual PortNetwork constructor.

## P. Bridge / loop boundary

The current PortCrossing forbids same-region edge pairs.

The raw duality kernel handles would-be dual loops at the orbit level via
IsDualLoopPort, including characteristic-two cancellation.

A later general dual-map constructor must either:

1. assume DualLoopFree; or
2. introduce a loop-capable structural carrier.

TRM-033 should not choose between these architectures yet.

## Q. Computability / axioms

All raw permutation, boundary-walk, and sum definitions should be computable.

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- new noncomputable production declaration.

Fixture-specific dual indexing should be explicit and computable.

## R. Audit

Create:

DkMathTest/Tromino/PortDualityKernelAxiomAudit.lean

Audit at least:

1. dualRotation = primal faceEquiv;
2. raw dual face-step = primal rotation;
3. dual vertex relation = primal face orbit;
4. dual face reachability = primal same-region rotation orbit;
5. dual V/E/F/D count swap and chi preservation;
6. faceBoundaryWalk closure and length;
7. face-boundary XOR = faceBoundaryLabelSum;
8. tension -> IsDualFaceKirchhoff;
9. triangle DualLoopFree;
10. concrete triangle dual map V=2,E=3,F=3,D=6,chi=2;
11. old 2x3 map differs: F=1,chi=0;
12. triangle coloring labels transport to dual balanced Kirchhoff flow;
13. double-dual permutation restores primal rotation;
14. no converse face-conservation -> tension theorem is introduced.

## S. Validation

Build:

- DkMath.Tromino.PortDualityKernel
- DkMathTest/Tromino.PortDualityKernelAxiomAudit

Regression-build:

- DkMath.Tromino.PortKirchhoffFlow
- DkMathTest/Tromino.PortKirchhoffFlowAxiomAudit
- DkMath.Tromino.PortTensionColoring
- DkMathTest/Tromino.PortTensionColoringAxiomAudit
- DkMath.Tromino.PortCombinatorialMap
- DkMathTest/Tromino.PortCombinatorialMapAxiomAudit

Run git diff --check, forbidden-construct scan, and #print axioms.

## T. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-032.md

Record:

- alpha/rho/phi dual permutation convention;
- dual vertex = primal face orbit;
- dual face = primal vertex orbit;
- count swap and chi preservation;
- face-boundary walk and label sum;
- tension -> dual-face Kirchhoff theorem;
- DualLoopFree and would-be dual-loop semantics;
- concrete triangle dual map;
- distinction from old genus-1 2x3 map;
- triangle coloring -> dual balanced Kirchhoff flow;
- double-dual identity;
- exact converse gap: genus-zero face-boundary generation of all cycles.

## Stop condition

Stop once permutation-level duality, face-boundary conservation, and the
concrete triangle dual calibration are kernel-checked.

Do not construct a general dual PortNetwork, prove the converse dual-flow to
tension theorem, introduce loop-capable maps, prove universal flow existence,
topological realization, or Four Color theorem results without review.
