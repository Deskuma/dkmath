# FLT7TC-005R23 — Twisted coefficient classes and self-similarity obstruction audit

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:

- report-028.md
- PrimeTraceOneDirectRealCubicSuccessorAudit.lean
- PrimeTraceOneDirectRealCubicOrbitPowerSplit.lean
- SevenRealCubicUnitClass.lean
- astra-report-001.md
- astra-001/OrbitChecks.lean

R22 constructed an honest cyclic twisted seventh-power successor candidate
with a strictly smaller norm.  The remaining question is whether it can be
normalized back to the unweighted homogeneous-difference form needed by the
existing theta-depth / quotient machinery.

Do not assume that this normalization exists.

## Goal

Productionize the unit-class data needed to decide whether the three
coefficients of DirectRealCubicTwistedSeventhState can be equalized modulo
seventh powers.

If they cannot, record this as a precise obstruction and strengthen the state
only with the transport/local data actually inherited from the current
construction.

This checkpoint is an audit of self-similarity, not a descent claim.

## Part A — Galois action on projective unit classes

Productionize the Astra scratch theorem for the real-cubic rotation action.

For every u : SevenRealCubicIntˣ prove:

    projectiveLog (Additive.ofMul (directOrbitRotateUnit u))
      =
    M (projectiveLog (Additive.ofMul u))

where

    M(X,Y) = (4*X, X + 2*Y)

in ZMod 7 × ZMod 7.

Prefer an explicit definition:

    def rotateProjectiveLog :
      (ZMod 7 × ZMod 7) ->+ (ZMod 7 × ZMod 7)

or the appropriate additive equivalence if invertibility is convenient.

Kernel-check:

    M^3 = id
    id + M + M^2 = 0

if the latter is already available cheaply from Astra scratch.

Do not make these identities prerequisites if the basic action theorem is
already sufficient downstream.

## Part B — projective class of the extracted gap unit

For the current DirectOrbitPowerSplitPacket s, productionize the
generator-independent theorem predicted by Astra:

    projectiveLog (Additive.ofMul s.gapUnit) = (2,4).

The proof must not depend on an arbitrary PID generator choice.

Use only checked data:

- s.gapCore_eq;
- s.quotientCore_eq;
- s.cores_product_eq;
- local theta residue / quotient-core congruence from the exact-depth split;
- projectiveLog_pow_seven = 0;
- the known class of orbitUnit01 and thetaSevenUnit.

If the exact class of quotientUnit is easier to establish first, prove:

    projectiveLog quotientUnit = (5,1)

and derive the gapUnit class from the product identity.

It is acceptable to expose both.

## Part C — coefficient classes of the twisted successor

Recall:

    eps0 = eta
    eps1 = P^e * sigma(eta)
    eps2 = P^e * sigma(eps1)

with:

    P = directOrbitPairAxisUnitOne
    e = 32 + 42*k.

Productionize:

    projectiveLog P = (2,5)

using the existing alphaAddOne theorem.

Prove:

    (e : ZMod 7) = 4.

Then compute exactly:

    projectiveLog eps0 = (2,4)
    projectiveLog eps1 = (2,2)
    projectiveLog eps2 = (2,5).

Do not hard-code these results without deriving them from Part A/B.

Also compute the three ratio classes:

    projectiveLog (eps1 * eps0⁻¹) = (0,5)
    projectiveLog (eps2 * eps1⁻¹) = (0,3)
    projectiveLog (eps0 * eps2⁻¹) = (0,6)

up to the exact orientation chosen in the code.

Every reported ratio class must be checked to be nonzero.

## Part D — no seventh-power gauge equalization

Use:

    unit_isSeventhPower_iff_projectiveLog_eq_zero

to prove that no ratio of distinct successor coefficients is a seventh power
unit.

In particular prove a theorem of the conceptual form:

    ¬ ∃ v1 v2 : SevenRealCubicIntˣ,
        eps1 = eps0 * v1^7 ∧
        eps2 = eps0 * v2^7.

Equivalently: there do not exist seventh-power unit rescalings of root1/root2
that turn

    eps0*g0^7 + eps1*g1^7 + eps2*g2^7 = 0

into a common-coefficient equation

    eps0*(g0^7 + g1'^7 + g2'^7) = 0.

This theorem is the decisive audit result.

Do NOT interpret it as a contradiction of the twisted state itself.

## Part E — ordinary homogeneous-difference restart audit

The original direct split relies on a literal unweighted difference

    rho1^7 - rho0^7
      =
    (rho1-rho0) * seventhQuotient rho1 rho0.

For the successor state, inspect the two-term weighted expression

    eps1 * root1^7 - eps0 * root^7.

Prove a generic remainder identity modulo the root gap:

    eps1 * root1^7 - eps0 * root^7
      =
    eps1 * (root1^7-root^7)
      + (eps1-eps0) * root^7.

Hence divisibility by root1-root requires control of the coefficient-difference
term.

Audit the actual constructed state:

- is eps1-eps0 divisible by root1-root?
- if not, is it at least divisible by a fixed theta power?
- what is the exact theta depth of eps1-eps0?
- what is the exact theta depth of root1-root currently provable from the
  strengthened state?

Do not assert divisibility without checking it.

If the weighted expression is not divisible by the root gap, record that the
existing HomogeneousPowerQuotient kernel cannot restart directly.

## Part F — strengthen the successor state with inherited transport data

The current DirectRealCubicTwistedSeventhState forgets data that is genuinely
true for states produced by R22.

Define a stronger state only if justified, conceptually:

    structure DirectRealCubicTransportedTwistedState extends
      DirectRealCubicTwistedSeventhState where
      k : Nat
      exponent : Nat
      exponent_eq : exponent = 32 + 42*k
      coeff1_transport :
        coeff1 = P^exponent * sigmaUnit coeff0
      coeff2_transport :
        coeff2 = P^exponent * sigmaUnit coeff1
      root_not_axis_dvd : ¬ theta ∣ root
      -- add exact facts only when already proved from the constructor.

Construct it from every DirectOrbitPowerSplitPacket / smaller-norm packet.

Do not include original integer endpoints unless an actual theorem needs them.

## Part G — identify the correct next algebraic kernel

After Parts D/E, classify the next route.

### Route 1 — ordinary quotient survives

Only if the actual coefficient-difference term is divisible strongly enough
to recover a useful homogeneous quotient.

State the exact theorem required.

### Route 2 — twisted homogeneous quotient

If ordinary divisibility fails, formulate the weakest useful weighted kernel
for:

    u*x^7 - v*y^7

with u,v units related by the transport law.

Determine whether there is a natural factor after adjoining/retaining the
unit ratio, or whether a different gap variable is required.

Do not implement a large abstraction unless one concrete successor instance
demonstrates the needed identity.

### Route 3 — state is not self-similar

If the current successor data cannot reproduce an exact factorization of the
same kind, record this cleanly.  The strict smaller norm remains true, but it
does not by itself generate an iterable descent.

This is a legitimate Outcome C/D and is preferable to forcing a false
self-similarity theorem.

## Part H — integer summit route remains separate

Do not reopen direct PrimitiveRamifiedSummitPacket reconstruction in this
checkpoint except to update the audit conclusion if new coefficient-class
data materially changes it.

The known missing integer data remain:

- successor endpoints;
- Fermat seventh-power equation;
- exact 7^6 gap;
- cyclotomic residual seventh-power equation;
- primitive/seven-unit conditions;
- TraceOne root and exact norm.

## Hard stops

- No assumption that the three twisted coefficients are equal modulo seventh
  powers.
- No dropping coefficient units.
- No claim that a twisted weighted difference factors by root1-root without an
  explicit divisibility theorem.
- No inference that smaller norm alone gives an iterable descent.
- No historical receiver/routing packet as an input.
- No sorry/sorryAx/admit/unsafe/project axiom.

## Preferred production file

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicTwistClass.lean

Tests:

    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicTwistClassApi.lean
    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicTwistClassAxiom.lean

Create report-029.md and update ROADMAP.md.

## Report questions

1. Was the Galois action M on projectiveLog productionized?
2. Was gapUnit class (2,4) proved generator-independently?
3. Were successor coefficient classes computed exactly?
4. Were all coefficient-ratio classes proved nonzero?
5. Was seventh-power gauge equalization ruled out?
6. Does the actual weighted two-term difference factor by root1-root?
7. What are the theta depths of the coefficient difference and root gap?
8. Was a stronger transported twisted state constructed?
9. Can the old homogeneous quotient machinery restart?
10. What exact new kernel, if any, is required for self-similarity?

## Outcomes

- Outcome A — TWISTED COEFFICIENTS NORMALIZE AND OLD HOMOGENEOUS QUOTIENT RESTARTS.
- Outcome B — COEFFICIENT CLASSES FIXED; A CHECKED WEIGHTED/TWISTED QUOTIENT BRIDGE RESTARTS EXTRACTION.
- Outcome C — COEFFICIENT CLASSES FIXED; SEVENTH-POWER EQUALIZATION FAILS; ONE PRECISE TWISTED FACTORIZATION BRIDGE REMAINS.
- Outcome D — SUCCESSOR STATE IS NOT SELF-SIMILAR UNDER THE CURRENT EXTRACTION MECHANISM.

## Validation

At minimum:

    lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTwistClass
    lake build DkMath.FLT.Seven
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTwistClassApi
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTwistClassAxiom
    git diff --check

Print axioms for:

- Galois action on projectiveLog;
- gapUnit class;
- all three coefficient classes;
- coefficient-ratio non-seventh-power theorems;
- transported twisted-state constructor;
- any claimed weighted-gap divisibility theorem.

Run forbidden-source/import scans on every decisive file.
