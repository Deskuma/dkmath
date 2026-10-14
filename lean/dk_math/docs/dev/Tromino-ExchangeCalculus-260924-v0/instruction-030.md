
# TRM-031 — V4 tension / proper 4-coloring equivalence and no-circularity boundary

## Goal

Formalize the exact relationship between:

1. a nowhere-zero V4 edge assignment on an unlabeled Port combinatorial map;
2. zero holonomy around every closed region walk;
3. a region-state potential;
4. a proper four-state Mathlib coloring.

This checkpoint is a boundary audit, not a Four-Color proof.

The central purpose is to determine the logical strength of the proposed target:

    genus-zero map
      -> exists nowhere-zero V4 assignment with zero holonomy

Expected result for every connected PortCombinatorialMap:

    zero-holonomy nowhere-zero V4 assignment
      <-> proper TrominoState coloring.

Thus the remaining genus-zero existence arrow is the four-coloring problem in
tension/coboundary language unless a genuinely different intermediate
structure is introduced.

Do not prove the universal genus-zero existence statement.

## Terminology warning

Keep the historical production type name V4FlowAssignment for compatibility.

However document that the additional closed-walk XOR = 0 condition is standard
graph-theoretic tension / coboundary / exact 1-cochain behavior, not Kirchhoff
flow conservation.

A true nowhere-zero graph flow instead has a vertex conservation law.

## Production

Create:

DkMath/Tromino/PortTensionColoring.lean

Import PortCombinatorialMap, RegionPotential, and GraphColoringBridge as needed.

## A. Unlabeled region SimpleGraph

Define portRegionCrossingRel from PortCrossing by existence of a port from r
to s, and define portRegionSimpleGraph using SimpleGraph.fromRel.

Prove:

    (portRegionSimpleGraph C).Adj r s
      iff
    exists p, p.1 = r and (C.cross p).1 = s.

Also prove every port induces adjacency and loops are impossible.

## B. Calibration with existing Flow graph

For any A : V4FlowAssignment C prove:

    portRegionSimpleGraph C
      =
    regionSimpleGraph A.toFlowCrossing.

For an existing FlowCrossing C prove the erasure analogue:

    portRegionSimpleGraph C.toPortCrossing
      =
    regionSimpleGraph C.

This establishes that TRM-021 graph structure is label-independent.

## C. Port four-state coloring predicate

Define:

    PortFourStateColorable C :=
      Nonempty ((portRegionSimpleGraph C).Coloring TrominoState).

Prove:

    PortFourStateColorable C
      ->
    (portRegionSimpleGraph C).Colorable 4

using card_state.

The converse is optional if Mathlib Colorable.toColoring makes it clean.

## D. Coloring -> V4 assignment

Given a proper coloring K, define:

    coloringToV4Assignment K

with

    label(p) := K(p.source) + K(p.target).

Prove:

- the label is nonzero because K is proper;
- crossing reversal preserves the label by involution and commutativity;
- the exact endpoint-XOR label formula.

Do not use genus or rotation.

## E. Standard tension property

Define:

    IsZeroHolonomyV4Tension A :=
      RegionZeroHolonomy A.toFlowCrossing.

For a strong Port map define:

    HasZeroHolonomyV4Tension M :=
      exists A : V4FlowAssignment M.crossing,
        IsZeroHolonomyV4Tension A.

Document that nonzero comes from V4FlowAssignment and zero holonomy is the
closed-walk tension condition.

## F. Coloring-derived assignment has zero holonomy

Given K, construct a RegionPotential on the lifted Flow data of
coloringToV4Assignment K with state exactly K.

The edge law should reduce to characteristic-two arithmetic:

    K(target)
      =
    K(source) + (K(source) + K(target)).

Then prove:

    IsZeroHolonomyV4Tension (coloringToV4Assignment K)

using regionPotential_regionZeroHolonomy.

This direction requires neither connectedness nor genus.

## G. Zero-holonomy assignment -> Port coloring

For:

- M : PortCombinatorialMap P;
- A : V4FlowAssignment M.crossing;
- hzero : IsZeroHolonomyV4Tension A;

recover RegionPotential using the existing TRM-020 theorem.

Use:

- base region 0 from M.nonemptyRegions;
- M.connected;
- the PortRegionReachable <-> Flow RegionReachable lift equivalence.

Convert the recovered potential directly into a coloring of
portRegionSimpleGraph M.crossing.

Prove existence:

    exists_portColoring_of_zeroHolonomyV4Tension.

## H. Main equivalence theorem

Prove for every M : PortCombinatorialMap P:

    HasZeroHolonomyV4Tension M
      iff
    PortFourStateColorable M.crossing.

This is the central checkpoint theorem.

Its proof must not use genus, sphere characteristic, or planarity.

## I. Exact label round trip

Given A with zero holonomy, recover a potential/coloring K and prove pointwise:

    (coloringToV4Assignment K).label p = A.label p.

Use RegionPotential edge-label recovery.

A full structure equality is optional.

This confirms that zero-holonomy assignments are exactly color differences.

## J. Gauge interpretation — optional

If cheap, prove globally translated colorings

    K'(r) = K(r) + gamma

produce the same endpoint-XOR assignment.

Do not build a large gauge API.

## K. Genus-zero specialization

For G : PortGenusZeroCombinatorialMap P prove:

    HasZeroHolonomyV4Tension G.map
      iff
    PortFourStateColorable G.map.crossing.

The proof should simply reuse the general strong-map equivalence.
The genus-zero witness should be unused.

This is the no-circularity boundary.

## L. Universal target propositions

Define, but do not prove:

    PortGenusZeroTensionTarget :=
      forall P G, HasZeroHolonomyV4Tension G.map.

    PortGenusZeroFourColorTarget :=
      forall P G, PortFourStateColorable G.map.crossing.

with the appropriate dependent types.

Then prove:

    PortGenusZeroTensionTarget
      iff
    PortGenusZeroFourColorTarget.

Do not add either target as an axiom or theorem.

## M. Standard graph-theory interpretation

The report must state:

- V4FlowAssignment is a historical DkMath name;
- with zero holonomy it is tension/coboundary-like;
- nowhere-zero tension is directly equivalent to a proper coloring by its
  potential;
- therefore zero-holonomy tension existence is not by itself a route around
  Four Color.

Record a distinct future direction:

    true nowhere-zero V4 flow
      = Kirchhoff conservation at vertices,

and investigate later the planar/spherical duality between primal
coloring/tension and dual nowhere-zero flow.

Do not implement dual-flow theory in TRM-031.

## N. Fixtures

Audit the 2x2 strong Port map with an explicit proper coloring:

- region 0 -> 0;
- region 1 -> deltaA.

Check:

- coloring validity;
- coloringToV4Assignment labels are deltaA;
- zero holonomy;
- HasZeroHolonomyV4Tension;
- PortFourStateColorable;
- main equivalence.

For the existing all-deltaA assignment, recover a coloring and check the
induced labels are deltaA.

Also apply the general equivalence to the 2x3 genus-1 strong Port map and show
an explicit proper coloring exists there. This confirms the equivalence itself
is not a genus theorem.

## O. Scope audit

Do not attempt to construct a genus-zero non-4-colorable example.

Do not assert:

- PortGenusZeroTensionTarget;
- PortGenusZeroFourColorTarget;
- topological planarity;
- sphere realization.

The universal genus-zero target remains open.

## P. Mathlib survey boundary

Record that the repository survey used for this checkpoint did not identify a
ready-made Mathlib API for graph tensions / nowhere-zero flows.

Use existing SimpleGraph.Coloring APIs where available.

## Q. Computability / axioms

Definitions should be computable where possible, especially:

- portRegionSimpleGraph;
- coloringToV4Assignment.

The reconstruction from zero holonomy may inherit Classical.choice through the
existing RegionPotential existence theorem.

No sorry, admit, unsafe, new axiom, or new noncomputable production declaration.

## R. Audit

Create:

DkMathTest/Tromino/PortTensionColoringAxiomAudit.lean

Audit at least:

1. Port adjacency iff port witness;
2. Port graph = lifted Flow graph;
3. explicit 2x2 proper coloring;
4. coloring -> nonzero assignment;
5. crossing label preservation;
6. coloring-derived zero holonomy;
7. zero-holonomy assignment -> Port coloring;
8. main tension iff coloring theorem;
9. label round trip;
10. genus-zero specialization;
11. universal target iff theorem;
12. genus-1 2x3 fixture also satisfies the per-map equivalence;
13. no universal genus-zero existence theorem is introduced.

## S. Validation

Build:

- DkMath.Tromino.PortTensionColoring
- DkMathTest/Tromino/PortTensionColoringAxiomAudit

Regression-build:

- DkMath.Tromino.PortCombinatorialMap
- DkMathTest/Tromino.PortCombinatorialMapAxiomAudit
- DkMath.Tromino.RegionPotential
- DkMathTest/Tromino.RegionPotentialAxiomAudit
- DkMath.Tromino.GraphColoringBridge
- DkMathTest/Tromino.GraphColoringBridgeAxiomAudit

Run git diff --check, forbidden-construct scan, and #print axioms.

## T. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-030.md

Record:

- portRegionSimpleGraph;
- coloring -> V4 assignment;
- zero-holonomy tension terminology;
- coloring -> zero holonomy proof;
- zero holonomy -> potential -> coloring proof;
- main iff theorem;
- exact label round trip;
- genus-zero specialization;
- universal target iff theorem;
- why this prevents circular Four-Color reasoning;
- future distinction between tension and true Kirchhoff flow / planar duality.

## Stop condition

Stop once zero-holonomy nowhere-zero V4 assignment existence is proved
equivalent to proper TrominoState coloring on every connected strong Port map,
and the universal genus-zero tension target is proved equivalent to the
universal genus-zero four-color target.

Do not attempt the universal genus-zero existence proof, planar duality,
topological realization, or Four-Color theorem without review.
