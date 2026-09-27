# TRM-042 — Actual Port Codec / Semantic Transport Bridge

## Goal

Complete the exact bridge currently blocking TRM-041:

    PortNetworkPort (faceStarNetwork M I)
      ≃
    FaceStarPortDesc M.

This checkpoint is intentionally narrow.

It must:

1. construct a computable actual-port codec;
2. prove both round trips;
3. package the equivalence;
4. transport the already verified semantic crossing;
5. transport the already verified semantic rotation;
6. expose exact formulas on oldEdge / radialOld / radialCenter;
7. prove the transported crossing changes regions;
8. prove the transported rotation preserves regions.

Do NOT continue to cyclicity, triangular face orbits, Euler/genus,
coloring restriction, or universal targets in this checkpoint.

The purpose is to cross the dependent-Fin boundary cleanly before any larger
construction resumes.

## Read first

Read only:

- this instruction;
- CURRENT_STATE.md;
- DkMath/Tromino/PortFaceStarSubdivision.lean;
- DkMath/Tromino/PortTriangulationReduction.lean;
- DkMath/Tromino/PortNetwork.lean;
- only the exact Mathlib equivalence APIs needed for Sigma/Fin transport.

Do not re-read the whole Tromino branch unless a concrete theorem lookup
requires it.

## Existing verified base

Reuse without redesign:

- PortFaceStarIndexing;
- faceStarNetwork;
- oldRegion;
- faceCenterRegion;
- faceStarOldEdgePort;
- faceStarRadialOldPort;
- faceStarRadialCenterPort;
- FaceStarPortDesc;
- faceStarCrossDesc;
- faceStarCrossDesc_involutive;
- faceStarRotateDesc;
- faceStarRotateDescEquiv.

Do not replace these with a second encoding.

## A. Prefer equivalence composition over ad hoc decoding

The preferred route is to construct the codec by composing standard finite
equivalences, rather than manually proving a large q-dependent decoder.

Target decomposition:

    Σ r : Fin (V + F), Fin (arity' r)

into:

    (Σ r : Fin V, Fin (2 * oldArity r))
      ⊕
    (Σ f : Fin F, Fin (faceCard (faceEquiv.symm f))).

Then transform:

old part:

    Σ r, Fin (2 * oldArity r)
      ≃
    Fin 2 × (Σ r, Fin (oldArity r))

using finProdFinEquiv fiberwise and Sigma congruence.

center part:

    Σ f : Fin F, Fin (faceCard (faceEquiv.symm f))
      ≃
    Σ F : PortFaceCell ..., {p : oldPort // p ∈ F.val}

using I.faceEquiv and I.facePortEquiv.

Finally collapse the center sigma:

    Σ F, {p // p ∈ F.val}
      ≃
    oldPort

because each old port belongs to exactly one face cell, namely:

    faceCellOfPort M.localRotation M.crossing p.

Then identify:

    Fin 2 × oldPort  ⊕ oldPort

with:

    FaceStarPortDesc M

where:

    bit 0 -> oldEdge
    bit 1 -> radialOld
    center -> radialCenter.

If this fully compositional route becomes awkward, a direct decoder is
allowed, but the final round-trip proofs must still be clean and local.

## B. Sigma/equality policy

When dependent Sigma equality is needed:

- prefer Sigma.ext_iff / Sigma.ext;
- use Subtype.ext for Fin/subtype value equality;
- isolate casts in small named lemmas;
- avoid large proof terms containing nested Eq.rec / cast chains.

Create small cast lemmas such as:

    oldPortFin_cast_roundtrip
    centerPortFin_cast_roundtrip

if they materially simplify the codec proof.

Do not expose raw cast proofs as part of the public API.

## C. Encoder

Define:

    faceStarPortEncode
      (M : PortCombinatorialMap P)
      (I : PortFaceStarIndexing M) :
      FaceStarPortDesc M ->
      PortNetworkPort (faceStarNetwork M I)

by cases:

    oldEdge p      -> faceStarOldEdgePort I p
    radialOld p    -> faceStarRadialOldPort I p
    radialCenter p -> faceStarRadialCenterPort I p.

Required simp theorems for all three cases.

## D. Decoder

Define a computable:

    faceStarPortDecode M I :
      PortNetworkPort (faceStarNetwork M I)
        ->
      FaceStarPortDesc M.

The implementation may be:

- equivalence-composition based; or
- explicit finSumFinEquiv / finProdFinEquiv / facePortEquiv decoding.

No noncomputable selector.

Required theorem:

    faceStarPortDecode_encode :
      faceStarPortDecode M I (faceStarPortEncode M I d) = d.

Prove by cases on d.

## E. Reverse round trip

Prove:

    faceStarPortEncode_decode :
      faceStarPortEncode M I (faceStarPortDecode M I q) = q.

This is the current blocking theorem.

Do not weaken it to equality of region/source only.
Do not replace it with injectivity/cardinality.

This exact Sigma equality is mandatory.

## F. Package equivalence

Define:

    faceStarPortEquiv M I :
      PortNetworkPort (faceStarNetwork M I)
        ≃
      FaceStarPortDesc M

with:

    toFun   := faceStarPortDecode
    invFun  := faceStarPortEncode

or the orientation best suited to transport.

Expose both directions clearly.

Required simp/calibration theorems:

    faceStarPortEquiv_oldEdge
    faceStarPortEquiv_radialOld
    faceStarPortEquiv_radialCenter

and inverse forms if needed.

## G. Descriptor source classifier

Define a semantic source classifier:

    faceStarDescSource M I :
      FaceStarPortDesc M ->
      Fin (faceStarNetwork M I).regionCount

by:

    oldEdge p      -> oldRegion I p.1
    radialOld p    -> oldRegion I p.1
    radialCenter p ->
      faceCenterRegion I
        (faceCellOfPort M.localRotation M.crossing p).

Prove:

    (faceStarPortEncode M I d).1
      =
    faceStarDescSource M I d.

Then derive the corresponding theorem for faceStarPortEquiv/decode.

This keeps region arguments semantic.

## H. Transport semantic crossing

Define:

    faceStarCrossing M I :
      PortCrossing (faceStarNetwork M I)

by transporting faceStarCrossDesc through faceStarPortEquiv.

Conceptually:

    actual
      -> decode
      -> semantic cross
      -> encode.

Prove involutive by:

- codec round trips;
- faceStarCrossDesc_involutive.

Do not re-prove crossing algebra on dependent Fin coordinates.

## I. Crossing region-change proof

Prove changesRegion semantically by descriptor cases.

Cases:

1. oldEdge p:
   source oldRegion p.1,
   target oldRegion (M.crossing.cross p).1,
   distinct by M.crossing.changesRegion + oldRegion_injective;

2. radialOld p:
   oldRegion p.1 vs faceCenterRegion (faceCellOfPort ... p),
   distinct by oldRegion_ne_faceCenterRegion;

3. radialCenter p:
   same two region classes reversed.

This theorem is mandatory.

## J. Exact crossing formulas

Prove:

    faceStarCross_oldEdge :
      faceStarCrossing M I
        (faceStarOldEdgePort I p)
      =
      faceStarOldEdgePort I (M.crossing.cross p).

    faceStarCross_radialOld :
      faceStarCrossing M I
        (faceStarRadialOldPort I p)
      =
      faceStarRadialCenterPort I p.

    faceStarCross_radialCenter :
      faceStarCrossing M I
        (faceStarRadialCenterPort I p)
      =
      faceStarRadialOldPort I p.

These should reduce through the codec, not through Fin arithmetic.

## K. Transport semantic rotation

Define:

    faceStarRotateEquiv M I :
      PortNetworkPort (faceStarNetwork M I)
        ≃
      PortNetworkPort (faceStarNetwork M I)

by conjugating faceStarRotateDescEquiv through faceStarPortEquiv.

Then define:

    faceStarLocalRotation M I :
      PortLocalRotation (faceStarNetwork M I).

## L. Rotation preserves region

Prove preservesRegion semantically.

Cases:

1. radialOld p -> oldEdge p:
   both source oldRegion p.1;

2. oldEdge p -> radialOld (rho p):
   use M.localRotation.preservesRegion p;

3. radialCenter p -> radialCenter (phi.symm p):
   prove
       faceCellOfPort oldR oldC (phi.symm p)
         =
       faceCellOfPort oldR oldC p
   because phi.symm p lies in the same old face orbit.

Use existing face-orbit invariance theorems; do not introduce a new
face-equivalence axiom.

## M. Exact rotation formulas

Prove:

    faceStarRotate_radialOld :
      faceStarLocalRotation M I
        (faceStarRadialOldPort I p)
      =
      faceStarOldEdgePort I p.

    faceStarRotate_oldEdge :
      faceStarLocalRotation M I
        (faceStarOldEdgePort I p)
      =
      faceStarRadialOldPort I (M.localRotation.rotate p).

    faceStarRotate_radialCenter :
      faceStarLocalRotation M I
        (faceStarRadialCenterPort I p)
      =
      faceStarRadialCenterPort I
        ((portFaceEquiv M.localRotation M.crossing).symm p).

## N. No cyclicity yet

Do NOT build PortRotationSystem in this checkpoint.

TRM-042 stops at a verified PortLocalRotation plus PortCrossing.

The next checkpoint will use these exact formulas to prove:

- old-region cyclicity;
- face-center cyclicity;
- 3-step face dynamics;
- PortCombinatorialMap.

This separation is deliberate to avoid context compaction failure.

## O. Computability / safety

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- new noncomputable production declaration.

Classical reasoning inside theorem proofs is allowed only if required for
finite equality facts; the codec itself must remain computable.

## P. Audit

Extend:

    DkMathTest/Tromino/PortFaceStarSubdivisionAxiomAudit.lean

Audit at least:

1. encode oldEdge;
2. encode radialOld;
3. encode radialCenter;
4. decode_encode for all descriptors;
5. encode_decode for arbitrary actual q;
6. faceStarPortEquiv left/right inverse;
7. descriptor source theorem;
8. transported crossing involutive;
9. transported crossing changesRegion;
10. all three exact crossing formulas;
11. transported rotation inverse laws;
12. rotation preservesRegion;
13. all three exact rotation formulas.

Run #print axioms on:

- faceStarPortEncode_decode;
- faceStarCrossing;
- faceStarLocalRotation.

## Q. Validation

Build:

- DkMath.Tromino.PortFaceStarSubdivision
- DkMath.Tromino.PortTriangulationReduction
- DkMathTest/Tromino/PortFaceStarSubdivisionAxiomAudit

Regression-build:

- DkMath.Tromino.PortCombinatorialMap
- DkMath.Tromino.PortFaceOrbit
- DkMath.Tromino.PortRotationSystem

Run:

- git diff --check;
- production forbidden-construct scan;
- #print axioms audit.

## R. Report

Create:

    docs/dev/Tromino-ExchangeCalculus-260924-v0/report-041.md

Record:

- chosen codec construction strategy;
- exact dependent-Fin bridge;
- both round trips;
- semantic/actual crossing transport;
- semantic/actual rotation transport;
- source-region proofs;
- axiom/build results;
- exact next step:
    cyclicity + 3-cycle face theorem + combinatorial-map completion.

## Final acceptance audit

Before reporting completion, re-read this instruction and produce an internal
checklist:

    requirement | implemented theorem/definition | status

Every mandatory item A–M and P–Q must be marked implemented.

If any mandatory item is missing, report Outcome P and name the exact missing
bridge.

A successful build of only the files that were written is not sufficient for
GREEN.

## Stop condition

Stop once:

    PortNetworkPort (faceStarNetwork M I)
      ≃
    FaceStarPortDesc M

is kernel-checked in both directions and the verified semantic crossing and
rotation have been transported to actual ports with their exact formulas.

Do not proceed to cyclicity, triangular faces, Euler/genus, coloring
restriction, or universal targets in this checkpoint.
