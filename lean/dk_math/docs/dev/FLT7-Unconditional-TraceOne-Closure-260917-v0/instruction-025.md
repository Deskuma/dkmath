# FLT7TC-005R19 — Stripped-core seventh-power extraction and unit-class productionization

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:

- report-023.md
- astra-report-001.md
- PrimeTraceOneDirectRealCubicOrbitSplit.lean
- DkMath.Lib.NumberTheory.HomogeneousPowerQuotient

This checkpoint is algebraic only. Do not attempt the Archimedean smaller-norm
inequality yet.

## Goal

Starting from the production theorem

    directOrbit_stripped_cores_isCoprime

upgrade the two theta-free cores to explicit unit times seventh powers:

    gapCore      = (eta : SevenRealCubicInt) * g^7
    quotientCore = (nu  : SevenRealCubicInt) * h^7

and prove the exact projective unit classes

    projectiveLog eta = (2,4)
    projectiveLog nu  = (5,1)

for suitable extracted representatives/classes.

The output must retain all witnesses needed by the next height checkpoint.

## Part A — consume the new generic homogeneous quotient kernel

Import:

    DkMath.Lib.NumberTheory.HomogeneousPowerQuotient

Audit the current theorem

    directOrbit_commonPrime_associated_theta

and refactor its generic logical core to use:

    prime_dvd_exponent_cast_of_coprime_gap_and_homogeneous

at n=7 whenever this shortens the proof.

The remaining p=7-specific step is only:

    q ∣ (7 : SevenRealCubicInt)
      -> Associated q eisensteinAxis

using

    7 = eisensteinAxis^3 * thetaSevenUnit.

Do not duplicate the gap congruence proof now that the neutral Lib theorem
exists.

Keep the public theorem statement unchanged if useful for downstream
compatibility.

## Part B — exact stripped product identity

Unpack the witness from directOrbit_stripped_cores_isCoprime:

    A = 7^k * a
    d = theta^(32+42*k) * gapCore
    H = theta^3 * quotientCore
    IsCoprime gapCore quotientCore
    theta ∤ gapCore
    theta ∤ quotientCore.

Starting from

    d * H
      = orbitUnit01 *
        (theta^5 * thetaSevenUnit * A^2)^7

and

    7 = theta^3 * thetaSevenUnit,

cancel the exact common theta power and prove a literal product identity of
the form

    gapCore * quotientCore
      =
      orbitUnit01 *
        (thetaSevenUnit^(1 + 2*k) * (a : O)^2)^7

or an algebraically equivalent unit orientation.

Here O = SevenRealCubicInt.

Do not use Associated yet if a literal equality can be retained.

Audit exponent arithmetic carefully:

    total theta depth RHS = 35 + 42*k
    stripped depth LHS    = (32+42*k) + 3.

The theta powers must cancel exactly.

## Part C — generic coprime power extraction

Reuse existing generic machinery rather than historical packets.

Preferred sources:

- DkMath.Lib.NumberTheory.PowerFactor
- Mathlib exists_associated_pow_of_associated_pow_mul if already imported
- a tiny neutral wrapper only if needed.

From:

    IsCoprime gapCore quotientCore

and the product identity, extract:

    ∃ g, Associated (g^7) gapCore

and symmetrically:

    ∃ h, Associated (h^7) quotientCore.

Then expose the associated units explicitly:

    gapCore      = (eta : O) * g^7
    quotientCore = (nu  : O) * h^7

for eta,nu : Oˣ.

Be explicit about orientation of Associated. Do not silently invert a unit.

## Part D — determine the two unit classes

Astra-001 predicts:

    log eta = (2,4)
    log nu  = (5,1).

Productionize these exact class statements.

The derivation must not assume particular PID generators.

The correct target is invariance modulo seventh powers:

- changing g by a unit/seventh-power representative must not change the
  projective class of eta;
- likewise for nu.

Use:

    projectiveLog_pow_seven = 0

and multiplicativity of projectiveLog.

For quotientCore, use the local congruence obtained from exact quotient depth:

    quotientCore ≡ thetaSevenUnit * rho^6  (mod theta / equivalently mod 7
    after the checked normalization used in Astra-001)

together with the fact that rho is rational-scalar modulo (7).

For gapCore, use the stripped product identity and:

    log orbitUnit01 = (0,5)
    log thetaSevenUnit = (5,1)

plus the quotient-core class.

If a direct coordinate proof is simpler and kernel-checkable, it is acceptable.

Do not apply a theorem restricted to global units to a nonunit core.

## Part E — stable extraction packet

Create a production packet, conceptually:

    structure DirectOrbitPowerSplitPacket ... where
      base : DirectRealCubicRootPacket source r
      gapSplit : DirectOrbitGapSplit source r
      gapCore quotientCore : O
      gap_eq : ...
      quotient_eq : ...
      cores_isCoprime : IsCoprime gapCore quotientCore
      gapRoot : O
      quotientRoot : O
      gapUnit quotientUnit : Oˣ
      gapCore_eq :
        gapCore = (gapUnit : O) * gapRoot^7
      quotientCore_eq :
        quotientCore = (quotientUnit : O) * quotientRoot^7
      gapUnit_log :
        projectiveLog (Additive.ofMul gapUnit) = (2,4)
      quotientUnit_log :
        projectiveLog (Additive.ofMul quotientUnit) = (5,1)

Names may differ, but retain the witnesses.

Do not yet add norm inequalities.

## Part F — optional unit-absorption audit only

Audit whether the historical coprime exponents 3 and 7 trick from
SevenRealCubicAxisDrop.nonempty_axisDrop can convert the current gap equation
into a cleaner form

    d = droppedAxis^? * descentWitness^7

without losing the current exact depth 32+42*k.

Do not instantiate historical packet types.

If a clean generic lemma can be reused directly, record the resulting current
equation. Otherwise stop; this is optional and must not block Outcome A.

## Hard stops

- No historical receiver/routing packet as input.
- No Archimedean embeddings or smaller-norm proof in this checkpoint.
- No successor-state construction.
- No claim of descent.
- No dropping eta/nu.
- No applying projectiveLog unit criteria to nonunits.
- No inference from norms to element equality/coprimality.
- No sorry/sorryAx/admit/unsafe/project axiom.

## Preferred production file

Either extend:

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicOrbitSplit.lean

or, preferably for auditability, add:

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicOrbitPowerSplit.lean

Tests:

    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicOrbitPowerSplitApi.lean
    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicOrbitPowerSplitAxiom.lean

Create report-025.md and update ROADMAP.md.

## Report questions

1. Was directOrbit_commonPrime_associated_theta refactored to consume the new
   neutral HomogeneousPowerQuotient kernel?
2. Was the exact theta-cancelled core product identity proved?
3. Were both cores extracted as associated seventh powers?
4. Were explicit units eta,nu exposed?
5. Were the exact classes (2,4) and (5,1) proved independent of generator choice?
6. Was a stable power-split packet created?
7. Did the optional current-route axis absorption produce a useful equation?
8. What remains before the smaller-norm theorem?

## Outcomes

- Outcome A — STRIPPED CORES EXTRACTED AS UNIT×SEVENTH-POWERS; BOTH UNIT CLASSES GREEN.
- Outcome B — COPRIME SEVENTH-POWER EXTRACTION GREEN; UNIT-CLASS IDENTIFICATION REMAINS.
- Outcome C — EXACT CORE PRODUCT GREEN; ASSOCIATED POWER EXTRACTION API IS THE FRONTIER.
- Outcome D — ASTRA EXTRACTION CLAIM FAILS TO PRODUCTIONIZE.

## Validation

At minimum:

    lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitPowerSplit
    lake build DkMath.FLT.Seven
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicOrbitPowerSplitApi
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicOrbitPowerSplitAxiom
    git diff --check

Print axioms for:

- exact stripped product identity;
- gap-core associated seventh-power theorem;
- quotient-core associated seventh-power theorem;
- explicit unit equations;
- both unit-class theorems;
- stable packet constructor.

Run forbidden-source/import scans on all decisive files.
