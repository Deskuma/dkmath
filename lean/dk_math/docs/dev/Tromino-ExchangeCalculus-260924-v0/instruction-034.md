
# TRM-035 — Gaussian/Eisenstein local V4 frame and global V4-chain bridge

## Goal

Connect the original local Tromino/Gaussian/Eisenstein exchange picture to the
global F2 chain scaffold completed in TRM-034.

The conceptual source is:

    Gaussian realization
         ↓
    TrominoExchangeFrame
         ↑
    Eisenstein realization

where the common structure is not a ring isomorphism, but a local 3+1 frame
with V4 exchange dynamics.

TRM-035 should make that statement precise and then lift the same V4 carrier
into the Port F2 chain complex.

The central structural identity is:

    TrominoState = (ZMod 2) × (ZMod 2) = F2².

Therefore a V4-valued chain is equivalent to two scalar F2 chains.

Do not prove genus-zero exactness or Four Color.
Do not claim Z[i] ≅ Z[ω] as rings.

## Production files

Create:

- DkMath/Tromino/LocalFrameEquiv.lean
- DkMath/Tromino/PortV4Chains.lean

Small calibration lemmas may also be added to PortF2Chains.lean.

## A. Recover the remaining TRM-034 calibrations

Before the new bridge, close the structural leftovers that are useful below.

Add to PortF2Chains.lean:

1. face-cell representative invariance:

       q ∈ portFaceOrbit R C p
         ->
       faceCellOfPort R C q = faceCellOfPort R C p.

2. walk edge-chain reversal invariance:

       portWalkEdgeChain (W.reverse) = portWalkEdgeChain W.

3. explicit triangle face-boundary vector calibration.

   For trianglePortMap, prove that each of the two face cells has the
   all-three-edge vector over F2.

4. explicit triangle-dual face-boundary vectors.

   For triangleDualMap, prove each face boundary is the two-edge vector
   expected from the concrete fixture, and at least two face-boundary vectors
   are distinct/nonzero.

The all-face dependency

       portBoundary2 R C (fun _ => 1) = 0

remains strongly preferred but is not required for GREEN if the generic proof
is disproportionately expensive. Record its status.

## B. Abstract local 3+1 V4 frame

Define a finite local frame whose four panels are coordinatized by V4.

A suggested shape is:

    structure TrominoExchangeFrame where
      Panel : Type
      instFintype : Fintype Panel
      instDecidableEq : DecidableEq Panel
      colorEquiv : Panel ≃ TrominoState
      gap : Panel

Install scoped/local instances as needed.

Derived definitions:

    frameColor F p := F.colorEquiv p

    frameBody F := Finset.univ.erase F.gap

    frameDelta F p :=
      frameColor F F.gap + frameColor F p.

Prove:

- Panel has cardinality 4;
- body has cardinality 3;
- gap is not in body;
- p in body iff frameDelta F p != 0;
- the frameDelta image of body is exactly the three nonzero TrominoState
  elements;
- therefore every body panel gives exactly one of deltaA, deltaB, deltaC.

The frame should encode the source document's local "3+1" structure directly.

## C. Frame equivalence preserving relative exchange deltas

Define a strong local frame equivalence:

    structure TrominoExchangeFrameEquiv (G E : TrominoExchangeFrame) where
      panelEquiv : G.Panel ≃ E.Panel
      map_gap : panelEquiv G.gap = E.gap
      map_delta :
        forall p,
          E.frameDelta (panelEquiv p) = G.frameDelta p

Absolute colors need not be preserved.

This is important: a global V4 translation/gauge may change all absolute
states while preserving every relative exchange delta.

Prove:

- body membership is transported;
- deltaA/deltaB/deltaC classification is transported;
- relative exchange choice is conjugate through panelEquiv.

Do not require ring multiplication.

## D. Gaussian local realization

Use the actual 2x2 Tromino geometry.

Define:

    GaussianPanel :=
      {c : Cell // c ∈ block2}.

Use atomicColor from FourColorCell as its V4 coordinate.

Construct:

    gaussianExchangeFrame : TrominoExchangeFrame

with:

- Panel = GaussianPanel;
- gap = the subtype corresponding to (1,1);
- colorEquiv induced by atomicColor restricted to block2.

Prove the canonical coordinates:

    (0,0) -> 0
    (1,0) -> deltaA
    (0,1) -> deltaB
    (1,1) -> deltaC

or the exact existing atomicColor coordinate order.

Then prove the three relative directions from the Gaussian gap are exactly:

    deltaA, deltaB, deltaC

in some explicit order.

Interpret these as the local mod-2 Gaussian directions corresponding to:

    1, i, 1+i.

This is a coordinate/frame interpretation only.
Do not define an isomorphism of Gaussian and Eisenstein integer rings.

## E. Eisenstein local direction realization

Define a four-panel Eisenstein direction frame at the purely local mod-2
level.

Recommended minimal carrier:

    abbrev EisensteinPanel := TrominoState

with:

- gap = 0;
- colorEquiv = Equiv.refl TrominoState.

Then the body panels are exactly:

    deltaA, deltaB, deltaC.

Name/interpret them as the three undirected Eisenstein directions:

    1, omega, 1+omega

up to the chosen coordinate naming.

Construct:

    eisensteinExchangeFrame : TrominoExchangeFrame.

Prove its three body directions are exactly the three nonzero V4 states.

This checkpoint deliberately uses the mod-2 local direction frame, not the
full integral TraceOneInt (-1) ring.

## F. Gaussian -> Eisenstein frame equivalence

Construct:

    gaussianEisensteinFrameEquiv :
      TrominoExchangeFrameEquiv
        gaussianExchangeFrame
        eisensteinExchangeFrame.

The natural map should send a Gaussian panel p to its relative delta from the
Gaussian gap:

    p |-> gaussianExchangeFrame.frameDelta p.

Hence:

- Gaussian gap maps to Eisenstein gap 0;
- the three Gaussian body panels map bijectively to deltaA/deltaB/deltaC;
- relative deltas are preserved.

This should formalize the exact source claim:

    3 Gaussian Body directions
      <->
    3 Eisenstein undirected directions.

## G. Local exchange transport theorem

Define the relative state exchange attached to one body panel:

    localExchange F p x :=
      exchange (F.frameDelta p) x.

Prove the conjugacy statement under any TrominoExchangeFrameEquiv:

    localExchange E (phi.panelEquiv p) x
      =
    localExchange G p x.

Equivalently, both use the same preserved V4 delta.

If a transported absolute-color version is useful, prove it only up to the
natural global translation/gauge.

Do not implement the full two-panel configuration PanelSwap yet unless it is
trivial. The source document's larger PanelSwap/GapWalk layer remains future
work.

## H. V4 chain spaces

In PortV4Chains.lean define:

    abbrev PortV4VertexChain P :=
      Fin P.regionCount -> TrominoState

    abbrev PortV4EdgeChain C :=
      PortEdgeCell C -> TrominoState

    abbrev PortV4FaceChain R C :=
      PortFaceCell R C -> TrominoState.

Use scalar field/ring:

    PortF2 = ZMod 2.

TrominoState already carries the natural PortF2-module structure
coordinatewise.

## I. Coordinate splitting equivalences

Define linear equivalences:

    v4VertexChainEquiv :
      PortV4VertexChain P
        ≃ₗ[PortF2]
      PortVertexChain P × PortVertexChain P

    v4EdgeChainEquiv :
      PortV4EdgeChain C
        ≃ₗ[PortF2]
      PortEdgeChain C × PortEdgeChain C

    v4FaceChainEquiv :
      PortV4FaceChain R C
        ≃ₗ[PortF2]
      PortFaceChain R C × PortFaceChain R C.

The two coordinates are fst and snd.

Required pointwise theorems:

    (v4EdgeChainEquiv x).1 E = (x E).1
    (v4EdgeChainEquiv x).2 E = (x E).2

and analogous C0/C2 results.

This is the global form of:

    V4 = F2².

## J. V4 boundary maps

Define V4-valued analogues:

    portV4Boundary1 C :
      PortV4EdgeChain C ->ₗ[PortF2] PortV4VertexChain P

    portV4Boundary2 R C :
      PortV4FaceChain R C ->ₗ[PortF2] PortV4EdgeChain C

using the same F2 incidence coefficients from TRM-034.

Prove coordinate compatibility:

    fst(portV4Boundary1 x)
      =
    portBoundary1 (fst-coordinate x)

    snd(portV4Boundary1 x)
      =
    portBoundary1 (snd-coordinate x)

and similarly for boundary2.

Then prove:

    portV4Boundary1 C ∘ portV4Boundary2 R C = 0.

Prefer deriving this from the scalar TRM-034 theorem.

## K. V4 cycle-space decomposition

Define:

    PortV4CycleSpace C :=
      LinearMap.ker (portV4Boundary1 C).

Prove:

    x ∈ PortV4CycleSpace C
      iff
    fstChain x ∈ PortCycleSpace C
      and
    sndChain x ∈ PortCycleSpace C.

Likewise define the V4 face-boundary space as range(portV4Boundary2) and prove
its inclusion in PortV4CycleSpace.

This is the exact bridge between the V4 exchange layer and the F2 chain layer.

## L. Three nonzero directions as F2 coordinate patterns

Prove explicitly under the chain coordinate interpretation:

    deltaA = (1,0)
    deltaB = (0,1)
    deltaC = (1,1)

and therefore:

    deltaA + deltaB = deltaC

    deltaA + deltaB + deltaC = 0.

Explain in the report that these same three vectors are simultaneously:

- Tromino exchange choices;
- local Gaussian 1/i/(1+i) mod-2 directions;
- local Eisenstein 1/omega/(1+omega) undirected directions;
- nonzero coefficient values in V4-valued chains.

This is the conceptual center of TRM-035.

## M. Kirchhoff flow coordinate reading

Do not yet force a canonical computable edge-orbit representative for every
V4FlowAssignment.

Instead prove a representative-free statement at the local vertex level:

For each region r, the Kirchhoff sum A at r is zero iff both scalar coordinates
of that sum are zero.

Then connect those coordinate sums to the existing parity theorem from
PortKirchhoffFlow / FlowSignature.

If a clean existence/uniqueness theorem can descend A.label to an
edge-orbit-indexed PortV4EdgeChain without adding a noncomputable production
definition, it may be added.

Do not make GREEN depend on such a global descent.

## N. Triangle / dual wave calibration

For the triangle and its concrete dual:

1. express the balanced labels deltaA, deltaB, deltaC in F2² coordinates;
2. show the dual degree-3 Kirchhoff identity is coordinatewise:

       first coordinate: 1 + 0 + 1 = 0
       second coordinate: 0 + 1 + 1 = 0;

3. identify the same three coefficients with the Eisenstein local direction
   frame;
4. identify the primal triangle coloring differences with the Gaussian local
   relative directions, up to the explicit frame equivalence.

This is the concrete "wave" theorem family:

    Gaussian local 3+1 frame
      -> V4 relative deltas
      -> F2² coefficients
      -> dual Eisenstein three-direction Kirchhoff closure.

Keep the claim finite and explicit.

## O. Source-interpretation boundary

The report must distinguish three levels.

### Source-supported local statement

The source design asserts:

    Gaussian local frame
      ≃
    Eisenstein local frame

through a common 3+1 V4 exchange frame, not through a ring isomorphism.

### TRM-035 formal statement

TRM-035 formalizes that claim at the mod-2 local coordinate level and lifts V4
as F2² into the global chain complex.

### Not yet formalized

Do not claim:

- Z[i]/(2) ≅ TraceOneInt(-1)/(2) as rings;
- full integral Gaussian/Eisenstein lattice equivalence;
- geometric planar equivalence;
- genus-zero exactness;
- Four Color theorem.

A later checkpoint may connect the local Eisenstein direction frame to the
existing integral TraceOneInt (-1) / eisensteinCoord API modulo 2.

## P. Axiom / computability policy

Core local frame and chain definitions should be computable.

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- new noncomputable production declaration.

Proofs may use classical reasoning where needed.

## Q. Audit

Create:

- DkMathTest/Tromino/LocalFrameEquivAxiomAudit.lean
- DkMathTest/Tromino/PortV4ChainsAxiomAudit.lean

Audit at least:

1. Gaussian frame has 4 panels / 3 body panels;
2. Gaussian gap is (1,1);
3. Gaussian relative body deltas are exactly deltaA/B/C;
4. Eisenstein frame body is exactly deltaA/B/C;
5. GaussianEisenstein frame equivalence maps gap to gap;
6. it preserves all relative deltas;
7. local exchange conjugacy;
8. V4 C0/C1/C2 coordinate-splitting linear equivalences;
9. V4 boundary1 coordinate compatibility;
10. V4 boundary2 coordinate compatibility;
11. V4 boundary1 ∘ boundary2 = 0;
12. V4 cycle iff two F2 coordinate cycles;
13. V4 face-boundary space <= V4 cycle space;
14. deltaA/B/C coordinate identities;
15. triangle/dual balanced three-direction closure coordinatewise;
16. recovered TRM-034 reverse/face-representative/vector calibrations.

## R. Validation

Build:

- DkMath.Tromino.LocalFrameEquiv
- DkMath.Tromino.PortV4Chains
- DkMathTest/Tromino/LocalFrameEquivAxiomAudit
- DkMathTest/Tromino/PortV4ChainsAxiomAudit

Regression-build:

- DkMath.Tromino.PortF2Chains
- DkMathTest/Tromino.PortF2ChainsAxiomAudit
- DkMath.Tromino.PortDualityKernel
- DkMathTest/Tromino.PortDualityKernelAxiomAudit
- DkMath.Tromino.PortKirchhoffFlow
- DkMath.Tromino.FourColorCell

Run git diff --check, forbidden-construct scan, and #print axioms.

## S. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-034.md

Record:

- recovered TRM-034 calibrations;
- TrominoExchangeFrame abstraction;
- actual Gaussian 2x2/hole realization;
- Eisenstein three-direction local realization;
- Gaussian/Eisenstein frame equivalence;
- local exchange conjugacy;
- V4 = F2² chain splitting;
- V4 boundary maps and chain condition;
- V4 cycle-space coordinate decomposition;
- triangle/dual three-direction wave calibration;
- exact distinction between local frame equivalence and ring equivalence;
- recommended next step between:
    (a) integral Gaussian/Eisenstein mod-2 realization bridge, or
    (b) genus-zero exactness im ∂2 = ker ∂1.

## Stop condition

Stop once the original Gaussian/Tromino/Eisenstein local frame picture is
kernel-connected to the global V4/F2² chain complex.

Do not prove genus-zero exactness, full ring quotient equivalence, general
dual-map construction, universal flow existence, topological realization, or
Four Color theorem results without review.
