# FLT7TC-005R20 — Archimedean bridge and strict smaller-norm production theorem

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:
- astra-report-001.md
- report-023.md
- report-025.md
- PrimeTraceOneDirectRealCubicOrbit.lean
- PrimeTraceOneDirectRealCubicOrbitSplit.lean
- PrimeTraceOneDirectRealCubicOrbitPowerSplit.lean
- SevenRealCubicNumberField.lean
- astra-001/OrbitChecks.lean

This checkpoint productionizes the surviving Astra-001 height argument.
Do NOT block on the unresolved projective unit classes (2,4) and (5,1).
They are not required for the norm decrease.

## Goal

Starting from a current DirectOrbitPowerSplitPacket p, prove a production
theorem exposing

    G := Int.natAbs (SevenRealCubicInt.norm packet.gapRoot)

with

    0 < G
    G < packet.gapSplit.a
    packet.gapSplit.a <= r.summit.gapRoot.

This is a strict smaller positive integer norm theorem.

Do NOT construct a successor counterexample/state and do NOT call the result
a descent theorem.

## Part A — productionize the two real inequalities

Move the two already kernel-checked Astra scratch inequalities into a stable
production location.

Define/reuse

    H7(s,t) =
      s^6 + s^5*t + s^4*t^2 + s^3*t^3 +
      s^2*t^4 + s*t^5 + t^6.

Prove:

    realH7_ge_seven
      (s t : ℝ) (hs : 0 <= s) (ht : 0 <= t) :
      7*(s*t)^3 <= H7 s t.

Use the checked sum-of-squares identity from Astra-001.

Also prove for arbitrary reals L,R:

    realH7_ge_gap :
      (L-R)^6 <= 64 * H7 L R.

Again reuse the Astra sum-of-squares identity.

These two theorems are p=7 production lemmas. Do not attempt the generic AM-GM
generalization in this checkpoint.

## Part B — bridge the concrete real cubic order to its three real embeddings

The exact new bridge required by this checkpoint is positivity of the current
real-cubic root.

Let

    rho := p.rho.

Use the already established origin of rho as

    QuadraticAlgebra.norm gammaNorm

from the current direct cyclotomic normalized-root route.

Prove, in a form convenient for the later norm product, that every real
embedding of the cubic field sends rho to a strictly positive real number.

Preferred abstract shape:

    ∀ φ : SevenRealCubic.Field →+* ℝ,
      0 < φ (modelToField rho)

or the corresponding ring-of-integers form.

Equivalent explicit three-embedding statements are acceptable if much shorter.

The mathematical reason must be retained:
each real embedding of K+ extends to a complex embedding of the cyclotomic CM
field K, and the relative norm becomes

    z * conjugate(z) = |z|^2 > 0

because gammaNorm is nonzero.

Do not assert positivity merely because the rational norm B is positive.

### B1. Allowed fallback

If Mathlib's abstract extension/CM API is too expensive, it is acceptable to
construct the three real embeddings concretely by composing one real embedding
with powers of ringOfIntegersRotateEquiv / rotateEquiv, provided:
- they are proved to be exactly the three embeddings;
- positivity of rho under the base embedding comes honestly from the
  cyclotomic relative norm;
- no numerical approximation is used.

Stop with Outcome C if this bridge cannot be completed cleanly.

## Part C — norm lower bound for the homogeneous quotient

Let

    rho0 = rho
    rho1 = rotateEquiv rho
    rho2 = rotateEquiv (rotateEquiv rho)

and

    H01 = seventhQuotient rho1 rho0.

The other two Galois conjugates of H01 are the corresponding cyclic quotients.

Using Part B and realH7_ge_seven at each real embedding, prove:

    7^3 * B^6 <= SevenRealCubicInt.norm H01

where

    B := r.summit.residualRoot.

Pay attention to signs: this is an integer inequality, and positivity of all
three real conjugates should imply the norm is positive.

Use the exact identity

    rho0 * rho1 * rho2 = B

coming from the checked real-cubic norm.

Do not replace the product identity by norm equality without a theorem.

## Part D — norm equation for the stripped gap factor

Let packet : DirectOrbitPowerSplitPacket p.

Write:

    d := directOrbitGap p
    H := directOrbitQuotient p
    k := packet.gapSplit.k
    a := packet.gapSplit.a
    g := packet.gapRoot
    eta := packet.gapUnit
    G := Int.natAbs (norm g).

Use

    d = theta^(32+42*k) * packet.gapCore
    packet.gapCore = eta * g^7

and:
- abs(norm theta) = 7;
- norm of a global unit is ±1;
- n = 32+42*k is even.

Prove the absolute norm identity

    |norm d| = 7^(32+42*k) * G^7.

A natAbs formulation is acceptable and may be easier.

Similarly use the direct edge factorization or norm_orbitW-style arithmetic
to obtain:

    |norm d| * norm H = 7^35 * A^42

with A = r.summit.gapRoot.

Since Part C gives norm H > 0, avoid unnecessary absolute values on H.

After substituting

    A = 7^k * a

and cancelling powers of seven, prove

    G^7 * B^6 <= a^42.

This is the first decisive height inequality.

## Part E — lower bound for B from the original integer endpoints

Let

    L := r.summit.endpointLeft
    R := r.summit.endpointRight
    A := r.summit.gapRoot
    B := r.summit.residualRoot.

Use the checked summit equations:

    L - R = 7^6 * A^7
    cyclotomicSeven L R = 7 * B^7.

Identify the real polynomial H7 L R with the integer cyclotomic-seven
homogeneous quotient under casts.

Apply realH7_ge_gap to obtain

    (7^6 * A^7)^6 <= 64 * 7 * B^7.

Derive the exact convenient inequality:

    B^7 >= 7^35 * A^42 / 64.

It is enough for downstream use to prove the stronger/simple discrete
consequence

    A^42 < B^7

using the elementary numerical fact

    64 < 7^35.

Then use a <= A to conclude

    a^42 < B^7.

### E1. Prefer the simpler natural-number reduction

Since

    a^42 = (a^6)^7,

use strict monotonicity of seventh powers on naturals to derive

    a^6 < B.

Then obtain

    a^35 < B^6

for positive a.

This avoids Astra's more cumbersome 42nd-power comparison.

## Part F — strict smaller norm

First prove:

    0 < G.

Use:
- g != 0, derived from packet.gapCore_eq and exact theta-freeness/nonzero core;
- norm of a nonzero element in this number-field order is nonzero;
- natAbs positivity.

Then prove by contradiction:

If

    a <= G,

then

    a^7 <= G^7

and Part E gives

    a^35 < B^6.

Hence

    a^42 < G^7 * B^6,

contradicting Part D:

    G^7 * B^6 <= a^42.

Conclude:

    0 < G ∧ G < a.

Finally reuse the gap split

    A = 7^k * a

and positivity to prove

    a <= A.

## Part G — stable smaller-norm packet

Extend or wrap DirectOrbitPowerSplitPacket with a new packet, conceptually:

    structure DirectOrbitSmallerNormPacket ... where
      powerSplit : DirectOrbitPowerSplitPacket p
      normRoot : ℕ
      normRoot_eq :
        normRoot = Int.natAbs (SevenRealCubicInt.norm powerSplit.gapRoot)
      normRoot_pos : 0 < normRoot
      normRoot_lt_unitPart :
        normRoot < powerSplit.gapSplit.a
      unitPart_le_gapRoot :
        powerSplit.gapSplit.a <= r.summit.gapRoot

Create:

    directOrbitSmallerNorm_nonempty

and, if appropriate, a Classical.choice accessor.

Do not add successor endpoints or a successor CounterexamplePack.

## Part H — deferred projective classes

Do not make (2,4) / (5,1) unit classes a prerequisite.

Add a short comment/TODO or report note:
- the classes remain structurally interesting;
- the smaller-norm theorem depends only on unit norm ±1, not on their
  projective classes;
- they may be revisited only if successor reconstruction needs them.

This prevents the current FLT7 closure route from stalling on a nonessential
local classification.

## Hard stops

- No successor state.
- No "infinite descent" claim.
- No historical receiver/routing packet input.
- No use of projective class claims not yet productionized.
- No numerical floating-point embedding argument.
- No inference "positive rational norm => totally positive".
- No dropping unit norms without proving abs(norm(unit)) = 1.
- No sorry/sorryAx/admit/unsafe/project axiom.

## Preferred production file

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicOrbitHeight.lean

Tests:

    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicOrbitHeightApi.lean
    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicOrbitHeightAxiom.lean

Create:

    docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-026.md

and update ROADMAP.md.

## Report questions

1. Were both real inequalities productionized?
2. Was total positivity of the current rho proved honestly from its
   cyclotomic relative-norm origin?
3. Was norm H >= 7^3 * B^6 proved?
4. Was the absolute norm identity for the stripped gap proved?
5. Was G^7 * B^6 <= a^42 proved?
6. Was A^42 < B^7 (or an equivalent stronger bound) proved?
7. Was 0 < G < a <= A proved?
8. Was a stable smaller-norm packet created?
9. Did any step require the unresolved projective unit classes?
10. What exact data would a successor-state constructor still need?

## Outcomes

- Outcome A — STRICT SMALLER POSITIVE NORM GREEN IN PRODUCTION.
- Outcome B — TOTAL POSITIVITY AND NORM(H) LOWER BOUND GREEN; FINAL INTEGER HEIGHT COMPARISON REMAINS.
- Outcome C — REAL-EMBEDDING / TOTAL-POSITIVITY BRIDGE IS THE PRECISE FRONTIER.
- Outcome D — ASTRA SMALLER-NORM DEDUCTION DOES NOT SURVIVE PRODUCTION AUDIT.

## Validation

At minimum:

    lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitHeight
    lake build DkMath.FLT.Seven
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicOrbitHeightApi
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicOrbitHeightAxiom
    git diff --check

Print axioms for:
- total positivity / embedding positivity theorem;
- norm(H) lower bound;
- stripped gap absolute norm theorem;
- G^7 * B^6 <= a^42;
- original endpoint lower bound;
- strict smaller norm theorem;
- packet constructor.

Run forbidden-source/import scans on all decisive files.
