# FLT7TC-005R17 — Real-cubic exact-power orbit and fixed unit-class frontier

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Start from the committed R16 state in report-021.md.

R16 gives a current-provenance normalized cyclotomic seventh root gammaNorm with

    gammaNorm^7 = Q1
    cyclotomicNormHom gammaNorm = residualRoot
    endpointRight ≡ scalarLift(gamma)^7 (mod 49).

This checkpoint must not return to the historical receiver path.

## Part A — close the mod-49 local gate honestly

The current summit already has

    PrimitiveRamifiedSummitPacket.endpointRight_sixth_eq_one_mod49

while R16 gives that the same endpoint is a seventh power modulo 49.

Prove a provenance-independent finite theorem on ZMod 49:

    theorem isUnit_seventhPower_iff_pow_six_eq_one_mod49
        (u : ZMod 49) (hu : IsUnit u) :
        (∃ c : ZMod 49, u = c ^ 7) ↔ u ^ 6 = 1

An equivalent six-residue statement is acceptable.

Then specialize it to current endpointRight and record explicitly that the
R16 seventh-power gate is locally exhausted: it is not a contradiction and
does not reduce the already existing six endpoint unit classes.

Do not spend another checkpoint enumerating the same six residues.

## Part B — exact relative-norm seventh root

For a current DirectCyclotomicNormalizedRootPacket source r, define

    rho := QuadraticAlgebra.norm gammaNorm

in SevenRealCubicInt.

Prove:

    directChosenQuotientRealSource r = rho ^ 7

using gammaNorm^7 = Q1 and
QuadraticAlgebra.norm Q1 = directChosenQuotientRealSource r.

Also prove exactly:

    SevenRealCubicInt.norm rho = (r.summit.residualRoot : ℤ)

using the definition of cyclotomicNormHom and the R16 exact norm.
Preserve the sign.

Since residualRoot is a seven-unit, prove the smallest useful local
consequence that rho is not divisible by eisensteinAxis, or equivalently
has nonzero theta residue, reusing an existing theorem when available.

Package this as a small current-provenance real-root packet.

## Part C — build the order-three exact-power orbit

Let

    S0 := directChosenQuotientRealSource r
    rho0 := rho
    S1 := rotateEquiv S0
    rho1 := rotateEquiv rho0
    S2 := rotateEquiv S1
    rho2 := rotateEquiv rho1.

Kernel-check

    S0 = rho0^7
    S1 = rho1^7
    S2 = rho2^7

and record cyclic closure via rotateEquiv_three.

Use only the concrete SevenRealCubicInt.rotateEquiv.

## Part D — factor the first Galois source difference

Write conceptually

    theta := eisensteinAxis
    U := thetaSevenUnit
    A := r.summit.gapRoot
    Rscalar := endpointLeft * endpointRight

so that

    S0 = Rscalar - theta^35 * U^12 * A^14.

The rational scalar is fixed by rotateEquiv.

Reuse the checked rotation theorem

    rotateEquiv theta = theta * pairAxisUnit 1

up to the exact repository name.

Derive the rotation law for U from

    7 = theta^3 * U

rather than postulating it. A preferred division-free statement is

    (pairAxisUnit 1)^3 * rotateEquiv U = U.

It is acceptable to package pairAxisUnit 1 as a unit and use its inverse.

Then prove an explicit factorization, up to an overall sign/orientation:

    rotateEquiv S0 - S0
      = orbitUnit01 * (theta^5 * U * (A : SevenRealCubicInt)^2)^7.

The exact definition of orbitUnit01 may differ, but it must be:

- explicit;
- independent of source arithmetic data;
- proved to be a unit.

The algebraic shape is expected from

    theta^35 * A^14 = (theta^5 * A^2)^7
    U^12 = U^5 * U^7.

Do not assume the remaining fixed unit is a seventh power.

One orbit edge is enough if the second edge is only bookkeeping.

## Part E — compute the fixed unit class

Turn orbitUnit01 into a concrete SevenRealCubicInt unit and compute exactly

    projectiveLog (Additive.ofMul orbitUnit01Unit)

in ZMod 7 × ZMod 7.

Then use

    SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero

to decide by kernel-checked proof whether this fixed unit is a seventh power.

If the class is zero:

- construct v with orbitUnit01 = v^7;
- absorb it and obtain a pure real-cubic equation

      rho1^7 - rho0^7 = omega^7

  up to sign/orientation.

Do not call this integer FLT7.

If the class is nonzero:

- record the exact class;
- prove that no unit seventh root exists.

That nonzero class is not by itself a contradiction; it is the precise
global unit-class obstruction of the Galois difference.

## Part F — bounded descent-consumer audit

After Part E, inspect only clean existing real-cubic machinery:

- SevenRealCubicThetaCoordinates
- SevenRealCubicThetaSeventhPower
- SevenRealCubicCoprimeExtraction
- SevenRealCubicAxisDrop

Do not instantiate a historical packet merely because formulas look similar.

Audit whether the current equation

    rho1^7 - rho0^7 = orbitUnit01 * W^7

has enough checked hypotheses for any generic theorem giving:

1. exact theta depth of rho1 - rho0;
2. stripped-factor coprimality;
3. coprime seventh-power extraction;
4. a smaller current-provenance arithmetic state.

If one applies cleanly, use it.

Otherwise stop at the first exact missing theorem. A legitimate frontier is
a current-route theorem controlling the theta-adic factorization/coprimality of

    rho1 - rho0

and the homogeneous seventh quotient.

Do not claim descent until a new state/counterexample and a strict measure are
both constructed.

## Hard stops

- No CubicGapSeventhShapeReceiver.
- No RamifiedSignedRootRoutingPacket as an input to the new direct route.
- No theorem carrying sorryAx.
- Do not treat the R16 mod-49 gate as a contradiction.
- Do not assume thetaSevenUnit or orbitUnit01 is a seventh power.
- Do not infer element coprimality from norm coprimality without a theorem.
- Do not call a real-cubic seventh-power equation an integer FLT7 solution.
- No sorry, admit, unsafe, or project axiom.

## Preferred implementation

Production:

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicOrbit.lean

Tests:

    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicOrbitApi.lean
    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicOrbitAxiom.lean

Create report-022.md and update ROADMAP.md.

Keep facade exposure conservative.

## Report questions

1. Was the R16 mod-49 seventh-power gate shown redundant/equivalent to the
   existing endpoint sixth-root condition for units?
2. Was rho retained with directChosenQuotientRealSource = rho^7?
3. Was norm rho = residualRoot proved exactly?
4. Was the order-three exact-power orbit constructed?
5. Was the first Galois source difference factored as explicit unit times
   a seventh power?
6. Was the remaining coefficient proved to be a source-independent unit?
7. What is its exact projectiveLog?
8. Is that fixed unit a seventh power?
9. If yes, was a pure real-cubic seventh-power difference obtained?
10. Which clean descent/coprimality theorem applies next, or what exact theorem
    is missing?

## Outcomes

- Outcome A — REAL-CUBIC ORBIT DIFFERENCE GREEN; FIXED UNIT ABSORBED; CLEAN DESCENT CONSUMER APPLIES.
- Outcome B — REAL-CUBIC ORBIT DIFFERENCE GREEN; FIXED UNIT CLASS DECIDED; NEXT THETA-ADIC COPRIMALITY/DESCENT BRIDGE IDENTIFIED.
- Outcome C — EXACT REAL-CUBIC ROOT/ORBIT GREEN; EXPLICIT ORBIT-UNIT FACTORIZATION IS THE PRECISE FRONTIER.
- Outcome D — RELATIVE-NORM EXACT-POWER TRANSPORT ITSELF FAILS OR REQUIRES A NEW BRIDGE.

## Validation

At minimum:

    lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbit
    lake build DkMath.FLT.Seven
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicOrbitApi
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicOrbitAxiom
    git diff --check

Print axioms for:

- the mod-49 equivalence audit;
- the exact real-root seventh-power theorem;
- the exact norm theorem;
- the Galois source-difference factorization;
- the fixed unit-class/seventh-power decision theorem;
- any claimed descent consumer.

Run forbidden-source scans on all decisive new/modified files.
