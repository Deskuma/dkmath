# FLT7TC-005R21 — Sign-free three-conjugate gap height and strict smaller norm

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:

- report-026.md
- PrimeTraceOneDirectRealCubicOrbit.lean
- PrimeTraceOneDirectRealCubicOrbitSplit.lean
- PrimeTraceOneDirectRealCubicOrbitPowerSplit.lean
- PrimeTraceOneDirectRealCubicOrbitHeight.lean
- SevenRealCubicNumberField.lean
- SevenRealCubicCoprimeExtraction.lean
- astra-001/OrbitChecks.lean

This checkpoint supersedes the assumption that total positivity of rho is
necessary for the smaller-norm theorem.

The sign-free inequality

    (s-t)^6 <= 64 * H7(s,t)

is already productionized and holds for arbitrary real s,t.

Apply it simultaneously to the three cyclic real-conjugate pairs. This should
produce a strong norm inequality without proving rho totally positive and
without identifying SevenRealCubic.Field with the maximal real subfield of
CyclotomicField 7 Q.

## Goal

For a current DirectOrbitPowerSplitPacket p, prove in production:

    G := Int.natAbs (SevenRealCubicInt.norm p.gapRoot)

satisfies

    0 < G
    G < p.gapSplit.a
    p.gapSplit.a <= r.summit.gapRoot.

Do not construct a successor arithmetic state and do not call this an infinite
descent theorem.

## Part A — choose one real embedding of the real cubic field

Use the already checked theorem

    SevenRealCubic.isTotallyReal

and Mathlib's

    NumberField.IsTotallyReal.complexEmbedding_isReal

to choose one ring embedding

    realEmbedding : SevenRealCubic.Field ->+* Real.

A suggested construction is:

1. choose any complex embedding of SevenRealCubic.Field;
2. use total reality to prove it is real;
3. apply ComplexEmbedding.IsReal.embedding.

Then define a concrete evaluation ring hom

    realEval : SevenRealCubicInt ->+* Real

by composing:

- SevenRealCubic.modelToRingOfIntegers;
- the canonical coercion/algebra map from the ring of integers to
  SevenRealCubic.Field;
- realEmbedding.

Do not prove or require any positivity property of rho.

## Part B — real evaluation of the cyclic norm

For every x : SevenRealCubicInt, prove

    realEval x *
      realEval (rotateEquiv x) *
      realEval (rotateEquiv (rotateEquiv x))
      =
    (SevenRealCubicInt.norm x : Real).

This should be a direct map of the existing kernel theorem

    mul_rotateEquiv_mul_rotateEquiv_sq_eq_norm.

No field-level extension of rotateEquiv is required.

Also expose the obvious map formulas needed below:

- realEval (x-y) = realEval x - realEval y;
- realEval of integer casts;
- realEval of seventhQuotient in terms of H7.

## Part C — three sign-free quotient inequalities

For a current DirectRealCubicRootPacket p define conceptually:

    rho0 := p.rho
    rho1 := rotateEquiv rho0
    rho2 := rotateEquiv rho1

    d0 := rho1 - rho0
    d1 := rho2 - rho1
    d2 := rho0 - rho2

    H0 := seventhQuotient rho1 rho0
    H1 := seventhQuotient rho2 rho1
    H2 := seventhQuotient rho0 rho2.

Prove the cyclic coherence:

    rotateEquiv H0 = H1
    rotateEquiv H1 = H2
    rotateEquiv H2 = H0

and similarly for the gaps, using rotateEquiv_three.

Let

    s0 := realEval rho0
    s1 := realEval rho1
    s2 := realEval rho2.

Prove:

    realEval H0 = H7 s1 s0
    realEval H1 = H7 s2 s1
    realEval H2 = H7 s0 s2.

Apply production theorem realH7_ge_gap three times:

    (s1-s0)^6 <= 64 * realEval H0
    (s2-s1)^6 <= 64 * realEval H1
    (s0-s2)^6 <= 64 * realEval H2.

Because every left side is nonnegative, also derive:

    0 <= realEval H0
    0 <= realEval H1
    0 <= realEval H2.

Multiply the three inequalities carefully and use Part B to prove the
sign-free norm inequality:

    ((SevenRealCubicInt.norm d0 : Real) ^ 6)
      <=
    64^3 * (SevenRealCubicInt.norm H0 : Real).

Also prove:

    0 <= SevenRealCubicInt.norm H0.

This is the replacement for the total-positivity route.

## Part D — exact norm product of one orbit edge

Productionize the small Astra scratch norm facts if not already public:

    SevenRealCubicInt.norm orbitUnit01 = 1

and, for

    orbitW A :=
      eisensteinAxis^5 * thetaSevenUnit * (A : SevenRealCubicInt)^2,

    SevenRealCubicInt.norm (orbitW A) = 7^5 * (A : Int)^6.

Reuse:

- norm_eisensteinAxis;
- norm thetaSevenUnit;
- norm_intCast;
- norm_mul and norm_pow.

From the exact edge factorization

    d0 * H0 = orbitUnit01 * orbitW(A)^7

take norms and prove the exact integer identity

    norm d0 * norm H0 = 7^35 * (A : Int)^42.

Since A > 0, the right side is strictly positive.

Combine this with Part C to prove:

    0 < norm H0
    0 < norm d0.

Do not infer either sign from the rational norm of rho.

## Part E — natAbs norm of the extracted gap root

Let packet : DirectOrbitPowerSplitPacket p and write

    k := packet.gapSplit.k
    a := packet.gapSplit.a
    g := packet.gapRoot
    eta := packet.gapUnit
    D := Int.natAbs (norm (directOrbitGap p))
    G := Int.natAbs (norm g).

Use:

    directOrbitGap p =
      eisensteinAxis^(32+42*k) * packet.gapCore

and

    packet.gapCore = (eta : SevenRealCubicInt) * g^7.

Prove the generic helper needed for eta:

    Int.natAbs (norm (eta : SevenRealCubicInt)) = 1.

This follows because eta is a unit and norm is multiplicative into Int.

Then prove the exact natural-number identity

    D = 7^(32+42*k) * G^7.

Prefer natAbs multiplicativity; do not choose the sign of norm eta.

Because Part D proves norm(d0) > 0, also record

    D = norm d0

after the appropriate Int/Nat cast normalization.

## Part F — convert the sign-free real bound to naturals

Let

    HN := Int.natAbs (norm H0).

From Part C and Part D, obtain a natural-number inequality

    D^6 <= 64^3 * HN.

From the exact positive norm product, obtain

    D * HN = 7^35 * A^42.

Multiply the first inequality by D and substitute the product identity:

    D^7 <= 64^3 * 7^35 * A^42.

Now substitute:

    D = 7^(32+42*k) * G^7
    A = 7^k * a.

Cancel the positive common factor 7^(35+42*k) and prove:

    7^(189+252*k) * G^49 <= 64^3 * a^42.

Keep this as a named theorem; it is the decisive sign-free height inequality.

## Part G — strict decrease without residualRoot or total positivity

Assume for contradiction

    a <= G.

Then

    a^49 <= G^49.

Combine with Part F and cancel a^42 (using a > 0) to obtain:

    7^(189+252*k) * a^7 <= 64^3.

But:

- a >= 1;
- 189 + 252*k >= 7;
- 64^3 < 7^7.

Therefore

    64^3 < 7^7
      <= 7^(189+252*k) * a^7,

contradiction.

Conclude:

    G < a.

This route deliberately does NOT use:

- total positivity of rho;
- norm(H) >= 7^3 * B^6;
- the original endpoint lower bound A^42 < B^7;
- projective unit classes (2,4)/(5,1).

Then prove:

    0 < G.

Use:

- packet.gapCore_not_axis_dvd, hence gapCore != 0;
- packet.gapCore_eq, hence g != 0;
- injectivity/nonzero norm for a nonzero element of the cubic number-field
  integer model.

Finally prove:

    a <= A

from

    A = 7^k * a

and a > 0.

## Part H — stable smaller-norm packet

Create:

    structure DirectOrbitSmallerNormPacket ... where
      powerSplit : DirectOrbitPowerSplitPacket p
      normRoot : Nat
      normRoot_eq :
        normRoot = Int.natAbs (SevenRealCubicInt.norm powerSplit.gapRoot)
      normRoot_pos : 0 < normRoot
      normRoot_lt_unitPart :
        normRoot < powerSplit.gapSplit.a
      unitPart_le_gapRoot :
        powerSplit.gapSplit.a <= r.summit.gapRoot

and construct it from every current DirectRealCubicRootPacket.

No successor endpoints, no new CounterexamplePack, and no recursion/descent
theorem in this checkpoint.

## Part I — record the superseded frontier

Update ROADMAP/report to state explicitly:

The total-positivity bridge isolated in report-026 remains mathematically
interesting but is no longer required for the current smaller-norm route.

The replacement is the sign-free three-conjugate inequality

    norm(d)^6 <= 64^3 * norm(H),

derived from realH7_ge_gap under one arbitrary real embedding.

## Hard stops

- No total positivity assumption.
- No maximal-real-subfield equivalence as a prerequisite.
- No numerical root approximation.
- No historical receiver/routing packet.
- No projective unit-class assumption.
- No successor state.
- No infinite descent claim.
- No sorry/sorryAx/admit/unsafe/project axiom.

## Preferred production file

Either extend:

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicOrbitHeight.lean

or add, preferably:

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicOrbitGapHeight.lean

Tests:

    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicOrbitGapHeightApi.lean
    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicOrbitGapHeightAxiom.lean

Create report-027.md and update ROADMAP.md.

## Report questions

1. Was one honest real embedding of SevenRealCubic.Field constructed?
2. Was realEval on SevenRealCubicInt constructed?
3. Was the three-conjugate norm realization proved?
4. Was the sign-free norm inequality
   norm(d)^6 <= 64^3 * norm(H) proved?
5. Were norm(H) and norm(d) proved positive from the edge product?
6. Was D = 7^(32+42*k)* G^7 proved?
7. Was
   7^(189+252*k)* G^49 <= 64^3 * a^42
   proved?
8. Was 0 < G < a <= A proved?
9. Was DirectOrbitSmallerNormPacket constructed?
10. Was total positivity removed from the dependency chain?

## Outcomes

- Outcome A — SIGN-FREE STRICT SMALLER POSITIVE NORM GREEN IN PRODUCTION.
- Outcome B — THREE-CONJUGATE NORM INEQUALITY GREEN; FINAL NATURAL-POWER CANCELLATION REMAINS.
- Outcome C — ONE-REAL-EMBEDDING / CONJUGATE-PRODUCT BRIDGE IS THE PRECISE FRONTIER.
- Outcome D — SIGN-FREE HEIGHT BYPASS FAILS; RETURN TO TOTAL POSITIVITY.

## Validation

At minimum:

    lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitGapHeight
    lake build DkMath.FLT.Seven
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicOrbitGapHeightApi
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicOrbitGapHeightAxiom
    git diff --check

Print axioms for:

- realEval;
- cyclic norm evaluation theorem;
- sign-free norm inequality;
- exact edge norm product;
- D formula;
- decisive natural height inequality;
- strict smaller norm theorem;
- packet constructor.

Run forbidden-source/import scans on all decisive files.
