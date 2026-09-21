# FLT7TC-005R50 — Source-plane norm-minus-seven landing

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:

- report-055.md
- PrimeTraceOneDirectRealCubicSharpenedBranch.lean
- PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet.lean
- SevenRealCubicSourcePlane.lean
- SevenRealCubicThetaCoordinates.lean
- SevenRealCubicEisenstein.lean
- SevenRealCubicCoprimeExtraction.lean
- SevenRealCubicUnitClass.lean

R49 gives, on the C = 1 branch, a model unit t with

    Y := t^(7^9)
    W = rho * Y
    Y != 1
    norm t = 1
    transported t is non-torsion.

The same provenance gives

    Phi(W) = 0
    Phi(rho * Y) = -3*thetaLinearInt Y + 14*thetaSquareInt Y.

Hence

    3*thetaLinearInt Y = 14*thetaSquareInt Y.

R50 investigates the source-plane landing produced by

    g := 2 - 3*alpha = linearSource 2 (-3).

Its norm is -7, and the displayed line is exactly the condition that g*Y has
zero third alpha-coordinate.

The preferred breakthrough theorem is not a generic Thue solver. First try to
prove the narrower class-zero theorem actually needed by current provenance.

## Part A — exact correction line

From a DirectOrbitTrivialCommonFactorSharpenedPacket h, let

    Y := packet.t^(7^9).

Prove

    3 * thetaLinearInt (Y : SevenRealCubicInt)
      = 14 * thetaSquareInt (Y : SevenRealCubicInt).

Use only packet.correction_eq,
directOrbitDeepJet_normalized_trace_zero,
directOrbitDeepJet_trace_plane_form, and
directOrbitTracePlaneForm_rho_mul.

Also record

    Y != 1
    norm (Y : SevenRealCubicInt) = 1
    projectiveLog (Additive.ofMul Y) = 0.

The projective-log statement should use the existing seventh-power log API.

## Part B — neutral source-plane axis

Create, preferably:

    DkMath/FLT/Seven/SevenRealCubicSourcePlaneNormSeven.lean

Define a neutral element such as

    sourcePlaneNormSevenAxis := linearSource 2 (-3).

Prove exactly:

    sourcePlaneNormSevenAxis = 2 - 3*alpha
    norm sourcePlaneNormSevenAxis = -7
    IsSourcePlane sourcePlaneNormSevenAxis.

For arbitrary theta coordinates prove

    thetaSquareInt
      (sourcePlaneNormSevenAxis * ofThetaCoordinates A B C)
        = -3*B + 14*C.

Equivalent third-alpha-coordinate spelling is acceptable.

Thus prove

    3*B = 14*C
      -> IsSourcePlane
           (sourcePlaneNormSevenAxis * ofThetaCoordinates A B C).

## Part C — current C=1 source-plane landing

For the R49 correction Y prove

    IsSourcePlane
      (sourcePlaneNormSevenAxis * (Y : SevenRealCubicInt))

and

    norm
      (sourcePlaneNormSevenAxis * (Y : SevenRealCubicInt)) = -7.

This is the mandatory R50 landing.

## Part D — exact source-plane norm equation

Prove neutrally

    norm (linearSource a b)
      = a^3 + 2*a^2*b - a*b^2 - b^3.

Therefore every source-plane norm-minus-seven element satisfies

    a^3 + 2*a^2*b - a*b^2 - b^3 = -7.

Do not call this solved from numerical evidence.

## Part E — three visible calibrations

Kernel-check

    linearSource (-3) 1 = eisensteinAxis
    linearSource 1 2    = ramifiedAxis
    linearSource 2 (-3) = sourcePlaneNormSevenAxis

and norm -7 for all three.

For g := sourcePlaneNormSevenAxis, calibrate the correction units Y satisfying
g*Y equal to the three points. Expected theta-coordinate representatives:

    Y0 = 1
    Y1 = ofThetaCoordinates 9 14 3
    Y2 = ofThetaCoordinates (-10) (-14) (-3).

Verify the multiplication equalities, unit status, and exact projective logs.
Expected values from the exploratory calculation are:

    projectiveLog Y0 = (0,0)
    projectiveLog Y1 = (0,5)
    projectiveLog Y2 = (0,1).

Do not assume these values; let Lean determine them.

## Part F — preferred narrow classification theorem

Before attempting full Thue classification, try to prove the theorem actually
needed by current provenance:

    theorem sourcePlaneNormSevenAxis_mul_seventh_class_eq_one
        (u : SevenRealCubicIntˣ)
        (hnorm : norm (u : SevenRealCubicInt) = 1)
        (hlog : projectiveLog (Additive.ofMul u) = 0)
        (hplane :
          IsSourcePlane
            (sourcePlaneNormSevenAxis * (u : SevenRealCubicInt))) :
        u = 1

An equivalent theorem may assume directly that u is a seventh power.

This theorem is not currently known. It is the primary R50 research target.

Audit possible use of:

- the unique ramified prime above seven;
- ramifiedAxis_associated_eisensteinAxis;
- the projective-log class criterion;
- exact theta/source-plane coordinates;
- norm -7 of the multiplier.

Do not infer the theorem merely from ideal association.

## Part G — fallback full norm-minus-seven classification

If Part F does not close, attempt or isolate the exact theorem

    theorem linearSource_norm_neg_seven_classification
        (a b : Z)
        (h : norm (linearSource a b) = -7) :
        (a = -3 and b = 1) or
        (a = 1 and b = 2) or
        (a = 2 and b = -3).

This is the specific binary cubic Thue equation of discriminant 2401 = 49^2.

Do not present bounded search as proof.

Audit whether this special equation admits a short proof from existing
DkMath/Mathlib infrastructure: unique ramified-prime ideal, explicit units,
real embeddings/order, cyclic Galois action, or elementary inequalities.

If it requires genuine effective Thue/Baker machinery, stop and say so.

## Part H — C=1 contradiction if classification succeeds

If either Part F or Part G is kernel-checked, consume the R49 packet.

For Part F:

    Y = t^(7^9)
    projectiveLog Y = 0
    norm Y = 1
    IsSourcePlane (g*Y)

gives Y = 1, contradicting packet.correction_ne_one.

For Part G, use the three calibrated candidates. The two nonidentity candidates
must have nonzero projective log, while the identity candidate contradicts
correction_ne_one.

Preferred endpoint:

    directOrbit_no_trivial_common_factor_sharpened_packet
      (P : DirectOrbitTrivialCommonFactorSharpenedPacket h) : False

or equivalently h.c != 1.

Only add this if classification is genuinely kernel-checked.

## Part I — branch consequence

If C=1 is excluded, collapse the R49 dichotomy to

    1 < h.c
    29 <= h.c
    forall prime q | h.c, q % 7 = 1
    29*h.u^5 < h.v.

Package this only after Part H is green.

## Part J — computational reconnaissance

Python/SymPy/PARI may be used only for discovery.

Current heuristic observations:

- `a^3 + 2*a^2*b - a*b^2 - b^3 = -7` appears to have only
  (-3,1), (1,2), (2,-3) in large search windows.
- the induced norm-one correction line
  `A^3 - 35*A^2*m + 392*A*m^2 - 1421*m^3 = 1`
  appears to have only
  (A,m) = (1,0), (9,1), (-10,-1)
  in large search windows.

These are not proofs.

## Hard stops

- No finite search presented as completeness.
- No claim that association to the unique prime above seven leaves only three generators.
- No new fundamental-unit basis assumption.
- No invented Baker/Thue theorem.
- No arbitrary Hensel continuation.
- No C>1 character/mod-28 work in R50.
- No successor/descent theorem.
- No FLT7 endpoint unless the relevant branch is actually kernel-closed.
- No sorry, sorryAx, admit, unsafe, or project axiom.

## Preferred deliverables

If Part F/H succeeds:

- DkMath/FLT/Seven/SevenRealCubicSourcePlaneNormSeven.lean
- DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicTrivialCommonFactorExclusion.lean
- report-056.md
- ROADMAP.md

If classification remains open, the neutral landing module plus a precise
research report is acceptable.

## Validation

For promoted neutral/public theorems run the focused module builds, facade,
API/axiom clients, scratch, forbidden-source scan, and git diff --check.

Print axioms for:

- correction-line theorem;
- source-plane landing;
- Part F narrow classification, if proved;
- C=1 exclusion, if proved.

Expected project-level axioms remain
[propext, Classical.choice, Quot.sound].

## Outcomes

- Outcome A — narrow/full classification is green and C=1 is eliminated.
- Outcome B — source-plane norm-minus-seven landing and calibrations are green;
  classification is the precise remaining theorem.
- Outcome C — exact correction line and landing are green, but the
  calibration/classification interface still needs new infrastructure.
- Outcome D — the proposed landing identity fails under current exact
  definitions; record the corrected geometry and stop.
