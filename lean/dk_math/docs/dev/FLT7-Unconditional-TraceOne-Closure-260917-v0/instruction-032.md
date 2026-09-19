# FLT7TC-005R26 — Coprime square extraction beneath the seventh-power orbit split

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:
- report-025.md
- report-027.md
- report-030.md
- report-031.md
- PrimeTraceOneDirectRealCubicOrbitPowerSplit.lean
- PrimeTraceOneDirectRealCubicLocalClass.lean
- PrimeTraceOneDirectRealCubicWeightedGapObstruction.lean
- SevenRealCubicUnitClass.lean
- DkMath.Lib.NumberTheory.PowerFactor

R25 formally rules out ordinary homogeneous-gap self-similarity of the smaller
twisted successor. Do not try to restart that route here.

Instead, return to the exact R19 element product before taking norms.

## Goal

For every current DirectOrbitPowerSplitPacket s, prove that the two extracted
seventh roots are coprime and that their product is associated to the scalar
square a^2.

Then use generic coprime power extraction at exponent 2 to prove that each
seventh root is itself associated to a square.

Conceptually:

    IsCoprime g h

    g * h = unit * (a : O)^2

therefore

    g = unit_g * r^2
    h = unit_h * t^2.

This is a new algebraic refinement of the smaller-norm packet. It is not yet a
successor state or a contradiction.

## Part A — coprimality of the extracted seventh roots

From production data:

    IsCoprime gapCore quotientCore

    gapCore      = gapUnit * gapRoot^7
    quotientCore = quotientUnit * quotientRoot^7

prove:

    IsCoprime gapRoot quotientRoot.

Preferred proof:
- either use an existing IsCoprime.of_pow / pow API;
- or use the prime-divisor criterion:
  a common prime divisor of gapRoot and quotientRoot divides both cores,
  since the displayed coefficients are units.

Do not infer this from norm coprimality.

Expose it as a stable theorem on DirectOrbitPowerSplitPacket.

## Part B — the unit defect between the root product and the scalar square

The core product identity is:

    gapCore * quotientCore
      =
    orbitUnit01 *
      (thetaSevenUnit^(1+2*k) * (a : O)^2)^7.

Substitute the two unit-times-seventh-power core equations and isolate the
unit defect:

    delta :=
      orbitUnit01Unit * (gapUnit * quotientUnit)^-1.

Prove:

    projectiveLog delta = 0.

This should now be unconditional from R24:

    projectiveLog gapUnit      = (2,4)
    projectiveLog quotientUnit = (5,1)
    projectiveLog orbitUnit01  = (0,5)

and

    (2,4) + (5,1) = (0,5) in (ZMod 7)^2.

Then use:

    unit_isSeventhPower_iff_projectiveLog_eq_zero

to obtain a unit w with:

    delta = w^7.

Be careful about exact multiplication/inverse orientation.

## Part C — cancel the seventh powers

Let:

    scalarSquare :=
      thetaSevenUnit^(1+2*k) * (a : O)^2.

Using Part B and the core product identity, derive:

    (gapRoot * quotientRoot)^7
      =
    (w * scalarSquare)^7

up to the exact orientation chosen.

Now prove equality of the bases.

Preferred routes, in order:

1. use injectivity of odd seventh powers after transporting to the totally real
   cubic field;
2. equivalently show the quotient is a seventh root of unity and use the
   existing odd-degree/totally-real torsion theorem to rule out nontrivial
   order 7;
3. use an existing local theorem if DkMath already owns seventh-power
   injectivity in SevenRealCubicInt.

Do NOT silently cancel seventh powers in an arbitrary domain.

Conclude a literal equation or at least an Associated theorem:

    gapRoot * quotientRoot
      =
    (unit : O) * (a : O)^2

or

    Associated ((a : O)^2) (gapRoot * quotientRoot).

The thetaSevenUnit power is itself a unit and may be absorbed into the unit.

## Part D — coprime square extraction

Use Part A and the associated-square product from Part C with the generic
coprime power splitter at exponent 2.

Construct:

    gapSquareRoot quotientSquareRoot : O

such that:

    Associated (gapSquareRoot^2) gapRoot
    Associated (quotientSquareRoot^2) quotientRoot.

Prefer the existing theorem:

    exists_associated_pow_of_associated_pow_mul

or the DkMath.Lib.NumberTheory.PowerFactor wrapper.

Do not implement a new square-factorization engine.

## Part E — explicit unit-times-square witnesses

Expose units:

    gapSquareUnit quotientSquareUnit : Oˣ

with equations:

    gapRoot =
      (gapSquareUnit : O) * gapSquareRoot^2

    quotientRoot =
      (quotientSquareUnit : O) * quotientSquareRoot^2.

Retain orientation carefully.

Package the result, conceptually:

    structure DirectOrbitSquareRefinementPacket ... where
      powerSplit : DirectOrbitPowerSplitPacket p
      roots_isCoprime : IsCoprime powerSplit.gapRoot powerSplit.quotientRoot
      rootProductUnit : Oˣ
      rootProduct_eq :
        powerSplit.gapRoot * powerSplit.quotientRoot =
          rootProductUnit * (powerSplit.gapSplit.a : O)^2
      gapSquareRoot quotientSquareRoot : O
      gapSquareUnit quotientSquareUnit : Oˣ
      gapRoot_eq :
        powerSplit.gapRoot =
          gapSquareUnit * gapSquareRoot^2
      quotientRoot_eq :
        powerSplit.quotientRoot =
          quotientSquareUnit * quotientSquareRoot^2

Names may differ.

## Part F — norm-square consequences

Let:

    G := natAbs (norm gapRoot)
    Q := natAbs (norm quotientRoot)

and define:

    R := natAbs (norm gapSquareRoot)
    S := natAbs (norm quotientSquareRoot).

Prove:

    G = R^2
    Q = S^2.

Use natAbs(norm unit)=1.

Combine with the existing theorem:

    G * Q = a^6

to obtain:

    (R*S)^2 = (a^3)^2

and hence, on naturals:

    R * S = a^3.

This is a clean integer refinement.

Also transport the R21 strict inequality:

    0 < G < a

to:

    0 < R
    R^2 < a.

Do not claim R itself is a new gapRoot.

## Part G — audit whether exponent 2 opens a new successor notion

Read-only audit only.

Ask whether the new equations

    g = unit * r^2
    h = unit * s^2
    R*S = a^3

combine with any existing real-cubic/Galois structure to produce:
- a canonical smaller arithmetic state;
- an integer factorization of a;
- a contradiction with the known unit classes;
- or a new well-founded measure.

Do not force an answer.

In particular, do not confuse a square refinement with a seventh-power
self-similarity theorem.

## Part H — rational norm gcd audit, secondary only

If cheap, investigate gcd(G,Q) or gcd(R,S).

Do NOT assume element-level coprimality implies rational norm coprimality:
a rational prime may split into distinct prime ideals and divide both norms.

Record:
- 7 cannot divide G or Q because gapRoot and quotientRoot are theta-units;
- for q != 7, classify whether a common rational prime can only arise from
  split prime ideals in the cyclic cubic field.

Mine generic ideas from SevenRamifiedFusionPrimeLoadGalois if useful, but do
not instantiate historical routing packets.

This part is optional and must not block the square extraction.

## Hard stops

- Ordinary twisted homogeneous restart remains frozen after R25.
- No weighted quotient extension in this checkpoint.
- No inference of norm coprimality from element coprimality.
- No cancellation of seventh powers without a checked injectivity/torsion
  theorem.
- No successor-state or infinite-descent claim.
- No historical receiver/routing packet as an input.
- No sorry/sorryAx/admit/unsafe/project axiom.

## Preferred production file

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicSquareRefinement.lean

Tests:

    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSquareRefinementApi.lean
    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSquareRefinementAxiom.lean

Create report-032.md and update ROADMAP.md.

## Report questions

1. Were gapRoot and quotientRoot proved coprime?
2. Was the unit defect proved to have projectiveLog zero?
3. Was the unit defect extracted as a seventh power?
4. Was seventh-power base cancellation justified honestly?
5. Was gapRoot*quotientRoot proved associated to a^2?
6. Were both roots extracted as unit times squares?
7. Were G=R^2, Q=S^2, and R*S=a^3 proved?
8. Was 0<R and R^2<a proved?
9. Did the square refinement suggest a genuine new successor state?
10. What, if anything, was learned about gcd(G,Q)?

## Outcomes

- Outcome A — COPRIME SQUARE REFINEMENT GREEN; INTEGER NORM SPLIT R*S=a^3 GREEN.
- Outcome B — ROOT PRODUCT ASSOCIATED TO a^2 GREEN; GENERIC SQUARE EXTRACTION
  NEEDS A SMALL API BRIDGE.
- Outcome C — UNIT DEFECT SEVENTH POWER GREEN; SEVENTH-POWER BASE CANCELLATION
  IS THE PRECISE FRONTIER.
- Outcome D — ROOT PRODUCT DOES NOT REDUCE TO AN ASSOCIATED SQUARE; FREEZE THIS
  REFINEMENT ROUTE.

## Validation

At minimum:

    lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareRefinement
    lake build DkMath.FLT.Seven
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquareRefinementApi
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquareRefinementAxiom
    git diff --check

Print axioms for:
- extracted-root coprimality;
- unit-defect projectiveLog zero;
- unit-defect seventh-power witness;
- seventh-power base cancellation;
- associated-square product;
- both square extractions;
- G=R^2, Q=S^2, R*S=a^3;
- strict smaller square-norm theorem.

Run forbidden-source/import scans on every decisive file.
