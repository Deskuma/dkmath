# TRM-043 — Actual Constructor Calibration Closure

## Goal

Close the remaining TRM-042 API calibration gap only.

The actual dependent-Fin codec is already implemented and kernel-checked:

    faceStarPortEquiv
    faceStarPortEncode
    faceStarPortDecode
    faceStarPortDecode_encode
    faceStarPortEncode_decode

The actual transported structures are also already implemented:

    faceStarCrossing
    faceStarLocalRotation

The only blocker is proving that the pre-existing concrete constructors are
exactly the ports produced by faceStarPortEncode.

This checkpoint must prove the three encoder/constructor calibration
theorems, derive the three decoder/constructor calibration theorems, and then
derive the six exact crossing/rotation formulas required by TRM-042.

Do not proceed to cyclicity, triangular faces, Euler/genus, coloring
restriction, or universal targets.

## Read first

Read only:

- CURRENT_STATE.md;
- this instruction;
- DkMath/Tromino/PortFaceStarSubdivision.lean;
- DkMath/Tromino/PortTriangulationReduction.lean;
- DkMathTest/Tromino/PortFaceStarSubdivisionAxiomAudit.lean.

Do not re-read the wider Tromino stack unless a named theorem lookup is
strictly necessary.

## Existing verified base

Treat these as fixed:

- faceStarOldEdgePort
- faceStarRadialOldPort
- faceStarRadialCenterPort
- faceStarOldFiberEquiv
- faceStarCenterFiberEquiv
- faceStarOldSigmaEquiv
- faceStarCenterSigmaEquiv
- faceStarActualRegionEquiv
- faceStarPortSumEquiv
- faceStarSumDescEquiv
- faceStarPortEquiv
- faceStarPortEncode
- faceStarPortDecode
- faceStarPortDecode_encode
- faceStarPortEncode_decode
- faceStarCrossing
- faceStarLocalRotation
- faceStarCrossing_encode
- faceStarLocalRotation_encode.

Do not redesign the codec.

## A. Old-edge encoder calibration

Prove:

    @[simp] theorem faceStarPortEncode_oldEdge
        (I : PortFaceStarIndexing M)
        (p : PortNetworkPort P) :
      faceStarPortEncode I (.oldEdge p)
        =
      faceStarOldEdgePort I p.

Preferred proof route:

1. unfold only enough of:
       faceStarPortEncode
       faceStarPortEquiv
       faceStarPortSumEquiv
       faceStarSumDescEquiv;
2. reduce the old branch of:
       faceStarActualRegionEquiv
       Equiv.sumSigmaDistrib
       faceStarOldSigmaEquiv;
3. close the dependent Sigma equality with:
       Sigma.ext / Sigma.ext_iff;
4. close the local Fin slot equality with:
       Fin.ext;
5. normalize only the relevant:
       finSumFinEquiv
       finProdFinEquiv
       Fin.cast
   round trip.

Do not use a theorem about decoder calibration to prove encoder calibration.

This theorem should be the primary non-circular bridge.

## B. Radial-old encoder calibration

Prove:

    @[simp] theorem faceStarPortEncode_radialOld
        (I : PortFaceStarIndexing M)
        (p : PortNetworkPort P) :
      faceStarPortEncode I (.radialOld p)
        =
      faceStarRadialOldPort I p.

Reuse the old-edge proof structure.

The only semantic difference should be the Fin-2 slot:

    oldEdge      -> 0
    radialOld    -> 1.

If substantial duplicate cast normalization appears, factor it into one
private/named helper for the old-region slot encoder.

## C. Radial-center encoder calibration

Prove:

    @[simp] theorem faceStarPortEncode_radialCenter
        (I : PortFaceStarIndexing M)
        (p : PortNetworkPort P) :
      faceStarPortEncode I (.radialCenter p)
        =
      faceStarRadialCenterPort I p.

Preferred route:

1. unfold the center branch of faceStarPortEncode;
2. expose:
       F := faceCellOfPort M.localRotation M.crossing p;
3. normalize:
       I.faceEquiv F;
4. use:
       I.facePortEquiv F
   and its symm/apply round trips;
5. close the dependent Sigma equality by Sigma.ext;
6. close the subtype port equality by Subtype.ext;
7. close the Fin equality by Fin.ext if still needed.

Avoid a general theorem about arbitrary face-center ports unless this exact
proof naturally yields one.

## D. Decoder constructor calibration

Derive, preferably by rewriting with A-C and faceStarPortDecode_encode:

    @[simp] theorem faceStarPortDecode_oldEdgePort :
      faceStarPortDecode I (faceStarOldEdgePort I p)
        =
      .oldEdge p.

    @[simp] theorem faceStarPortDecode_radialOldPort :
      faceStarPortDecode I (faceStarRadialOldPort I p)
        =
      .radialOld p.

    @[simp] theorem faceStarPortDecode_radialCenterPort :
      faceStarPortDecode I (faceStarRadialCenterPort I p)
        =
      .radialCenter p.

These should be corollaries, not independent dependent-Fin proofs.

## E. Exact crossing formulas

Use:

    faceStarCrossing_encode

plus encoder calibration to prove:

    @[simp] theorem faceStarCross_oldEdge :
      (faceStarCrossing I).cross
        (faceStarOldEdgePort I p)
        =
      faceStarOldEdgePort I (M.crossing.cross p).

    @[simp] theorem faceStarCross_radialOld :
      (faceStarCrossing I).cross
        (faceStarRadialOldPort I p)
        =
      faceStarRadialCenterPort I p.

    @[simp] theorem faceStarCross_radialCenter :
      (faceStarCrossing I).cross
        (faceStarRadialCenterPort I p)
        =
      faceStarRadialOldPort I p.

These proofs should be short after A-C.

## F. Exact rotation formulas

Use:

    faceStarLocalRotation_encode

plus encoder calibration to prove:

    @[simp] theorem faceStarRotate_radialOld :
      (faceStarLocalRotation I).rotate
        (faceStarRadialOldPort I p)
        =
      faceStarOldEdgePort I p.

    @[simp] theorem faceStarRotate_oldEdge :
      (faceStarLocalRotation I).rotate
        (faceStarOldEdgePort I p)
        =
      faceStarRadialOldPort I
        (M.localRotation.rotate p).

    @[simp] theorem faceStarRotate_radialCenter :
      (faceStarLocalRotation I).rotate
        (faceStarRadialCenterPort I p)
        =
      faceStarRadialCenterPort I
        ((portFaceEquiv M.localRotation M.crossing).symm p).

Again, these should be short transport corollaries.

## G. Source calibration

Audit that the existing source theorem reduces on concrete constructors:

    (faceStarOldEdgePort I p).1 = oldRegion I p.1
    (faceStarRadialOldPort I p).1 = oldRegion I p.1
    (faceStarRadialCenterPort I p).1 =
      faceCenterRegion I
        (faceCellOfPort M.localRotation M.crossing p).

Reuse existing theorems from PortFaceStarSubdivision; do not duplicate them.

## H. API hygiene

The six exact formulas should carry @[simp] only if they do not create
rewrite loops with existing encode formulas.

If adding @[simp] creates loops, keep the constructor calibration lemmas
@[simp] and leave crossing/rotation formulas untagged.

No new public theorem should expose raw Eq.rec/cast internals.

## I. Safety policy

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- new noncomputable production declaration.

The calibration theorems must prove equality of the existing concrete ports,
not equality after decoding only.

## J. Audit

Extend:

    DkMathTest/Tromino/PortFaceStarSubdivisionAxiomAudit.lean

Audit at least:

1. faceStarPortEncode_oldEdge;
2. faceStarPortEncode_radialOld;
3. faceStarPortEncode_radialCenter;
4. faceStarPortDecode_oldEdgePort;
5. faceStarPortDecode_radialOldPort;
6. faceStarPortDecode_radialCenterPort;
7. faceStarCross_oldEdge;
8. faceStarCross_radialOld;
9. faceStarCross_radialCenter;
10. faceStarRotate_radialOld;
11. faceStarRotate_oldEdge;
12. faceStarRotate_radialCenter.

Run #print axioms on:

- the three encoder calibration theorems;
- one crossing formula;
- one rotation formula.

## K. Validation

Build:

- DkMath.Tromino.PortTriangulationReduction
- DkMathTest/Tromino/PortFaceStarSubdivisionAxiomAudit

Regression-build:

- DkMath.Tromino.PortFaceStarSubdivision
- DkMath.Tromino.PortCombinatorialMap
- DkMath.Tromino.PortFaceOrbit
- DkMath.Tromino.PortRotationSystem

Run:

- git diff --check;
- production forbidden-construct scan;
- #print axioms audit.

## L. Report

Create:

    docs/dev/Tromino-ExchangeCalculus-260924-v0/report-042.md

Record:

- exact calibration strategy;
- old slot 0/1 normalization;
- center face/subtype normalization;
- the three encoder formulas;
- the three decoder corollaries;
- the six actual crossing/rotation formulas;
- build/axiom results.

If all mandatory theorems A-F are present, report:

    Outcome A — TRM-042 calibration closure complete.

## Final acceptance audit

Before reporting completion, re-read this instruction and make an internal
table:

    requirement | theorem | status

GREEN requires all twelve named calibration/transport formulas A-F.

A successful build without all twelve formulas is Outcome P.

## Stop condition

Stop immediately after the three encoder calibrations, three decoder
calibrations, and six exact crossing/rotation formulas are kernel-checked.

Do not proceed to cyclicity, face-period 3, PortRotationSystem,
PortCombinatorialMap, Euler/genus, coloring restriction, or universal targets.
