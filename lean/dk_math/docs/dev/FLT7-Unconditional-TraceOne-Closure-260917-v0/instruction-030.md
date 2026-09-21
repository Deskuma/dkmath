# FLT7TC-005R24 — Theta-free local class bridge for the extracted orbit cores

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:

- report-029.md
- PrimeTraceOneDirectRealCubicOrbitSplit.lean
- PrimeTraceOneDirectRealCubicOrbitPowerSplit.lean
- PrimeTraceOneDirectRealCubicTwistClass.lean
- SevenRealCubicAxisDrop.lean
- SevenRealCubicUnitClass.lean

This checkpoint has one purpose only:

Determine, from current production data and explicit local theta arithmetic,
whether the extracted quotient/gap units have the predicted projective classes

    quotientUnit : (5,1)
    gapUnit      : (2,4).

Do not work on the weighted successor divisibility until this bridge is
settled.

## Part A — expose the theta-free quotient core canonically enough

The current split only stores

    directOrbitQuotient p = theta^3 * quotientCore
    theta ∤ quotientCore.

This is insufficient by itself to determine the projective class of the
associated extraction unit.

Go back to the actual definition

    directOrbitQuotient p
      = seventhQuotient (rotateEquiv p.rho) p.rho

and the checked fact

    theta ∣ rotateEquiv p.rho - p.rho
    theta ∤ p.rho.

Derive an explicit expansion modulo sufficiently high theta power, at least
through the coefficients detected by:

    thetaConstModSeven
    thetaLinearModSeven
    thetaSquareModSeven.

A preferred target is a canonical theta-free quotient-core congruence after
dividing by theta^3.

Do not choose an arbitrary quotient witness if its low theta coordinates cannot
be shown independent of that choice.

## Part B — quotient core residue invariants

For the production quotientCore in DirectOrbitPowerSplitPacket, prove exact
values/formulas for:

    thetaConstModSeven quotientCore
    thetaLinearModSeven quotientCore
    thetaSquareModSeven quotientCore.

The formulas may depend on the theta residue of p.rho, but should be explicit.

Use the fact that p.rho is a theta-unit.

If a normalization by a scalar power of thetaResidue p.rho is convenient,
state it explicitly rather than silently setting the residue to 1.

The goal is to identify the projective class of the unit in

    quotientCore = quotientUnit * quotientRoot^7.

## Part C — generic projective-log extraction from a theta-free source

If not already present, prove a reusable local theorem of the form:

Given a theta-unit source x and an equation

    x = (u : O) * r^7,

with thetaResidue x != 0,

then projectiveLog u is determined by the normalized first two nilpotent
coordinates of x.

In particular, derive projectiveLog u directly from:

    thetaConstModSeven x
    thetaLinearModSeven x
    thetaSquareModSeven x.

This should be a local analogue of

    projectiveLog_eq_zero_of_linearSource_eq_unit_mul_pow_seven

but without assuming the specialized linearSource shape.

Keep the theorem in the FLT7 real-cubic unit-class module unless its algebraic
surface is clearly neutral enough for Lib.

## Part D — quotientUnit class

Apply Part C to:

    quotientCore = quotientUnit * quotientRoot^7

and prove, if supported by the actual residue calculation:

    projectiveLog (Additive.ofMul quotientUnit) = (5,1).

This theorem must hold for the actual production packet, not for a finite
experimental witness.

If the class differs from Astra's predicted (5,1), record the kernel-checked
value and update the downstream arithmetic accordingly.

## Part E — gapUnit class from the product identity

Use:

    gapCore * quotientCore
      =
    orbitUnit01 *
      (thetaSevenUnit^(1+2*k) * a^2)^7

together with:

- projectiveLog orbitUnit01 = (0,5);
- projectiveLog of a seventh power = 0;
- the proved quotientUnit class.

Derive the gapUnit class.

The expected value is:

    projectiveLog gapUnit = (2,4).

Do not hard-code it; derive it.

## Part F — discharge the conditional successor coefficient theorems

If Part E proves the expected class, instantiate the existing conditional
theorems in PrimeTraceOneDirectRealCubicTwistClass to obtain unconditional:

    coeff0 class
    coeff1 class
    coeff2 class

and unconditional ratio non-seventh-power theorems.

Do not yet attempt weighted gap divisibility.

If Part E fails or the local residue data are insufficient, stop there and
record that the coefficient-class obstruction is not production-supported.

## Part G — audit canonicity of quotientCore

Because quotientCore arises by dividing by theta^3 in a domain, prove that its
value is unique for the fixed equality

    directOrbitQuotient p = theta^3 * quotientCore.

This should follow from theta^3 != 0 by cancellation.

Use this to justify that the local residue invariants are independent of the
existential witness chosen in R18.

If the existing packet already stores a unique literal quotientCore via the
constructor, still prove the mathematical uniqueness theorem for auditability.

## Hard stops

- No use of Astra's predicted (5,1)/(2,4) as assumptions in unconditional
  declarations.
- No finite numerical witness as proof of a universal packet theorem.
- No weighted-divisibility or successor-depth claims in this checkpoint.
- No historical receiver/routing packet.
- No sorry/sorryAx/admit/unsafe/project axiom.

## Preferred production file

Either extend:

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicTwistClass.lean

or add:

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicLocalClass.lean

Tests:

    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicLocalClassApi.lean
    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicLocalClassAxiom.lean

Create report-030.md and update ROADMAP.md.

## Report questions

1. Was quotientCore proved unique?
2. Were its three theta-local coordinates computed?
3. Was a generic local projective-log extraction theorem proved?
4. Was quotientUnit class proved universally?
5. Was gapUnit class proved universally?
6. Did the values equal (5,1) and (2,4)?
7. Were successor coefficient/ratio class theorems discharged
   unconditionally?
8. What exact local congruence was decisive?
9. If the class bridge failed, why exactly?
10. Is weighted-divisibility research now justified, or should the twisted
    route be frozen?

## Outcomes

- Outcome A — UNIVERSAL LOCAL CLASS BRIDGE GREEN; (5,1)/(2,4) PRODUCTIONIZED.
- Outcome B — QUOTIENT CORE LOCAL COORDINATES GREEN; PROJECTIVE UNIT EXTRACTION
  NEEDS ONE SMALL BRIDGE.
- Outcome C — CANONICAL CORE GREEN; REQUIRED THETA-LOCAL COORDINATES ARE THE
  PRECISE FRONTIER.
- Outcome D — CURRENT PACKET DOES NOT DETERMINE THE PREDICTED UNIT CLASSES;
  FREEZE THE TWISTED SELF-SIMILARITY ROUTE.

## Validation

At minimum:

    lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicLocalClass
    lake build DkMath.FLT.Seven
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicLocalClassApi
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicLocalClassAxiom
    git diff --check

Print axioms for:

- quotientCore uniqueness;
- all theta-local coordinate theorems;
- generic local projective-log extraction;
- quotientUnit class;
- gapUnit class;
- unconditional coefficient-ratio obstruction theorems.

Run forbidden-source/import scans on all decisive files.
