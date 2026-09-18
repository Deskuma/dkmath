# Generalization checkpoint — Homogeneous power quotient common-prime kernel

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

This checkpoint extracts only the genuinely reusable algebraic kernel identified
by Astra-001. It is independent of the FLT7 successor-state problem.

Run after, or at least separately from, instruction-023. Do not mix p=7
real-cubic implementation details into the neutral module.

## Ownership

Preferred namespace:

    DkMath.Lib.NumberTheory

Preferred new module:

    DkMath/Lib/NumberTheory/HomogeneousPowerQuotient.lean

Before adding anything, audit existing:
- DkMath.Lib.Cosmic.GTailCyclotomic
- DkMath.NumberTheory.GcdDiffPow
- DkMath.NumberTheory.CyclotomicQRCommonPrimeSupport
- DkMath.Lib.NumberTheory.PowerFactor

Reuse existing definitions/theorems if they already provide the same neutral
surface. Do not create a second competing homogeneous quotient.

## Part A — neutral homogeneous quotient

Expose or define, for a commutative semiring/ring as appropriate,

    H_n(x,y) = sum i in range n, x^(n-1-i) * y^i

with the standard factorization when subtraction is available:

    x^n - y^n = (x-y) * H_n(x,y).

If an existing DkMath/Mathlib definition is already canonical, provide only a
thin wrapper/theorem layer.

## Part B — gap congruence

Prove the exponent-independent congruence:

    (x-y) ∣ H_n(x,y) - n * y^(n-1)

with the scalar n interpreted by Nat.cast in the ambient ring.

An equivalent ideal-membership or quotient-ring statement is acceptable if it
is more natural and can be specialized back to divisibility.

This theorem is the generic content behind the FLT7 lemma

    gap_dvd_seventhQuotient_sub_seven_mul_pow_six.

## Part C — common-prime localization

Under the weakest clean domain/GCD hypotheses you can support, prove a theorem
of the following shape:

    q prime
    q ∣ x-y
    q ∣ H_n(x,y)
    q ∤ y
    ----------------
    q ∣ (n : R)

or a prime-ideal version with the same meaning.

If a fully generic prime-element statement causes excessive typeclass
overhead, implement a neutral integer theorem first and separately document
the stronger abstract statement as future work.

Do not hard-code n=7.

Also provide the symmetric variant using x when convenient.

## Part D — coprime corollary

Provide a reusable corollary:

If x and y are coprime/primitive enough to exclude q | y, then every common
prime divisor of x-y and H_n(x,y) lies over the exponent scalar n.

For prime exponent p, this is the algebraic common-support localization:

    common support(gap, quotient) ⊆ support(p).

Do not state stronger ideal ramification conclusions without hypotheses.

## Part E — FLT7 calibration only

In an FLT7 test/bridge file, show that the generic theorem reproduces the
logical core of:

    gap_dvd_seventhQuotient_sub_seven_mul_pow_six

and/or the Astra direct common-prime argument.

Do not move:
- SevenRealCubicInt;
- eisensteinAxis;
- theta depth;
- orbitUnit01;
- projectiveLog;
into DkMath.Lib.

The Lib module must import no FLT module.

## Part F — optional inequality research note, not a blocker

Astra-001 also exposed the general mathematical inequality, for odd p and
nonnegative real s,t,

    H_p(s,t) >= p * (s*t)^((p-1)/2).

Do not implement this generic AM-GM theorem in this checkpoint unless it is
straightforward with existing Mathlib APIs.

If not implemented, add a short TODO/research note pointing out that the p=7
production inequality is an instance and may later become a reusable height
kernel.

The common-prime localization is the mandatory deliverable.

## Hard stops

- No imports from DkMath.FLT.*
- No exponent 7 in the generic theorem statements.
- No cyclotomic-field or number-field assumptions unless strictly necessary.
- No duplicate of existing DkMath.Lib functionality.
- No sorry/sorryAx/admit/unsafe/project axiom.

## Tests

Preferred:

    DkMathTest/NumberTheory/HomogeneousPowerQuotient.lean

Calibrate at least:
- n=3;
- n=5;
- n=7;
- one abstract or integer common-prime example.

If the module is stable and genuinely neutral, add it to DkMath.Lib.lean.

## Report

Create a short report documenting:
1. whether an existing definition was reused;
2. the weakest hypotheses achieved;
3. the exact common-prime localization theorem;
4. FLT7 calibration;
5. whether the generic AM-GM lower bound was deferred.

## Outcome labels

- Outcome A — GENERIC HOMOGENEOUS QUOTIENT COMMON-PRIME KERNEL PROMOTED TO LIB.
- Outcome B — GAP CONGRUENCE GENERIC; PRIME-SUPPORT COROLLARY NEEDS A STRONGER TYPECLASS BRIDGE.
- Outcome C — EXISTING DKMATH API ALREADY OWNS THE KERNEL; ONLY RE-EXPORT/CALIBRATION NEEDED.
- Outcome D — PROPOSED GENERALIZATION DOES NOT SURVIVE API/HYPOTHESIS AUDIT.
