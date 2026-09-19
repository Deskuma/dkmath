# FLT7TC-005R31 — Complete-split prime residue criterion modulo seven

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:
- report-036.md
- PrimeTraceOneDirectRealCubicSquareGaloisSupport.lean
- SevenRealCubicNumberField.lean
- SevenRamifiedFusionCyclotomicDegreeSixCarrier.lean (for algebraic identities only)
- Mathlib finite-field / algebraic-closure APIs

R30 proves that every rational prime q dividing both current square-root norms:
- is different from 7;
- splits completely in SevenRealCubic.Field;
- has ramification index one and inertia degree one.

This checkpoint proves the explicit residue criterion

    q % 7 = 1 or q % 7 = 6.

Do not import historical routing/address packets as hypotheses.

## Goal

For a current DirectOrbitSquareRefinementPacket t, prove:

    theorem common_norm_prime_mod_seven
      (hq : q.Prime)
      (hqR : q ∣ natAbs(norm t.gapSquareRoot))
      (hqS : q ∣ natAbs(norm t.quotientSquareRoot)) :
      q % 7 = 1 ∨ q % 7 = 6.

Conceptually:

    common norm prime
      -> complete split in real cubic
      -> degree-one residue root beta in F_q
      -> primitive seventh root in a quadratic extension of F_q
      -> 7 | q^2 - 1
      -> q = ±1 mod 7.

## Part A — choose one degree-one prime above q

From R29/R30 choose any prime ideal P above q that divides the principal ideal
of the gap square root.

Retain:
- P.IsMaximal;
- P.LiesOver (q);
- inertia degree of P over q is one.

If the public R30 theorem only exposes the common value
    (q).inertiaDegIn O = 1,
use the Galois theorem identifying individual prime inertia degrees with the
common value.

Do not construct a historical quotient-prime address.

## Part B — identify the residue field with ZMod q

Let:

    kP := P.ResidueField

or use the quotient field O / P if that API is simpler.

Because the inertia degree is one, prove that the residue field has q elements.

Preferred routes:
1. use cardQuot_pow_inertiaDeg and the base quotient cardinal;
2. use absNorm / cardQuot directly;
3. use the definition of inertia degree as residue-field finrank.

Then construct a ring/field equivalence:

    residueEquiv : kP ≃+* ZMod q

or the reverse orientation, using:

    FiniteField.ringEquivOfCardEq

or an equivalent finite-field uniqueness theorem.

The equivalence may be noncanonical; only existence is needed.

## Part C — real-cubic evaluation modulo P

Define a ring hom:

    evalP : SevenRealCubicInt →+* ZMod q

by:
- modelEquivRingOfIntegers;
- quotient/residue-field map modulo P;
- residueEquiv.

Prove:
- evalP maps integer casts to the usual cast in ZMod q;
- its kernel contains the model pullback of P;
- define

      beta := evalP SevenRealCubicInt.alpha.

Map the checked alpha relation:

    alpha^3 - 2*alpha^2 - alpha + 1 = 0

to obtain:

    beta^3 - 2*beta^2 - beta + 1 = 0.

If using theta instead, set beta := evalP(theta) + 3 and prove the equivalent
alpha relation.

## Part D — beta is not three

Prove:

    beta ≠ 3.

If beta = 3, substitute into the cubic relation. The left side becomes 7, so
7 = 0 in ZMod q. Since q is prime this forces q = 7, contradicting R30.

Keep this proof current-provenance and independent of endpoint ratios.

## Part E — reciprocal quadratic lift

Let F := ZMod q and A := AlgebraicClosure F.

Map beta into A and define:

    quad :=
      X^2 - C(beta - 1) * X + 1.

Use IsAlgClosed.exists_root to choose t : A with:

    t^2 - (beta - 1)*t + 1 = 0.

Prove immediately:

    t ≠ 0

because the constant term is one.

Rearrange:

    beta = 1 + t + t^-1.

All casts into A must be explicit and checked.

## Part F — primitive seventh root

Use the polynomial identity

    t^3 * ((1+t+t^-1)^3
           - 2*(1+t+t^-1)^2
           - (1+t+t^-1) + 1)
      =
    1 + t + t^2 + t^3 + t^4 + t^5 + t^6.

Together with the beta cubic relation, prove:

    1 + t + t^2 + t^3 + t^4 + t^5 + t^6 = 0.

Hence:

    t^7 = 1.

Prove:

    t ≠ 1.

If t=1 then beta=3, contradicting Part D.

Since 7 is prime, conclude:

    IsPrimitiveRoot t 7.

Prefer an existing IsPrimitiveRoot constructor for prime exponent rather than
manually classifying all proper divisors.

This part is a good candidate for a small neutral lemma:

    cubicRoot_to_primitiveSeventhRoot

if its statement no longer mentions FLT packets.

## Part G — Frobenius preserves the quadratic

Let:

    tq := t^q.

Because beta lies in F = ZMod q, prove its image in A is fixed by q-th power:

    beta^q = beta.

Use the standard finite-field identity in ZMod q, transported through the
algebra map.

Raise the quadratic relation to the q-th power and prove that tq is also a
root of the same quadratic.

Since the roots of

    X^2 - (beta-1)X + 1

are t and t^-1, prove:

    t^q = t ∨ t^q = t^-1.

Preferred proof:
- factor the polynomial explicitly as (X-t)(X-t^-1);
- evaluate at t^q and use no-zero-divisors in the algebraic closure.

Do not use numerical finite-field enumeration.

## Part H — seventh order divides q squared minus one

From Part G prove:

    t^(q^2) = t.

Since t ≠ 0:

    t^(q^2 - 1) = 1.

From IsPrimitiveRoot t 7 conclude:

    7 ∣ q^2 - 1.

If natural-number subtraction is inconvenient, prove the integer version:

    (7 : Z) ∣ (q : Z)^2 - 1

and convert at the end.

## Part I — classify q modulo seven

Reduce the divisibility to ZMod 7:

    (q : ZMod 7)^2 = 1.

Factor:

    (q - 1) * (q + 1) = 0.

Since ZMod 7 is a field:

    q = 1 or q = -1 in ZMod 7.

Convert to the exact natural remainder statement:

    q % 7 = 1 ∨ q % 7 = 6.

This is the main production theorem.

Optionally expose the equivalent:

    q % 7 ∈ {1,6}

or

    q ≡ 1 [MOD 7] ∨ q ≡ -1 [MOD 7].

## Part J — gcd support theorem

Let:

    R := natAbs(norm t.gapSquareRoot)
    S := natAbs(norm t.quotientSquareRoot)
    C := Nat.gcd R S.

Prove:

    for every prime q,
      q ∣ C
        -> q % 7 = 1 or q % 7 = 6.

Also retain q != 7.

This theorem should be the stable arithmetic summary of R29-R31.

Do not claim C=1.

## Part K — current FLT7 clash audit

After the residue support theorem is green, search current direct provenance
only for a theorem forcing a prime divisor of gcd(R,S), a, R, or S into a
residue class outside ±1 mod 7.

Possible inputs may include:
- current seven-adic unit-part a;
- exact R*S=a^3;
- current primitive/coprime endpoint data.

Do not use historical routing/address assumptions.

If no clash exists, record:

    complete splitting plus q ≡ ±1 mod 7 is a support theorem, not yet a
    contradiction.

## Generalization candidate

Parts E-I form a neutral finite-field lemma:

    if beta in F_q satisfies
      beta^3 - 2 beta^2 - beta + 1 = 0
    and beta != 3,
    then q ≡ ±1 mod 7.

If clean, place this outside the current packet module, preferably in a small
SevenRealCubic residue module. It is specialized to conductor seven but not to
FLT provenance.

Do not generalize beyond what the proof naturally supports.

## Hard stops

- No historical RamifiedSignedRootRoutingPacket or quotient-prime address as
  an input.
- No maximal-real-subfield equivalence is required.
- No claim q % 7 = 1; the real cubic criterion is ±1 mod 7.
- No use of projective unit classes for this finite-field result.
- No FLT7 contradiction unless a separate current theorem clashes with the
  residue support.
- No successor/descent claim.
- No sorry/sorryAx/admit/unsafe/project axiom.

## Preferred production files

If useful, split into:

    DkMath/FLT/Seven/SevenRealCubicResidueCriterion.lean

for the neutral beta / primitive-root criterion, and:

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicSquareResidueSupport.lean

for the current packet instantiation.

Tests:

    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSquareResidueSupportApi.lean
    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSquareResidueSupportAxiom.lean

Create report-037.md and update ROADMAP.md.

## Report questions

1. Was a degree-one prime P above a common norm prime selected?
2. Was its residue field identified with ZMod q?
3. Was a direct current evalP : SevenRealCubicInt ->+* ZMod q constructed?
4. Was the cubic relation for beta proved?
5. Was beta != 3 proved from q != 7?
6. Was the reciprocal quadratic root t constructed in an algebraic closure?
7. Was t proved a primitive seventh root?
8. Was Frobenius shown to send t to t or t^-1?
9. Was 7 | q^2-1 proved?
10. Was q % 7 = 1 or 6 productionized?
11. Was the gcd(R,S) support theorem obtained?
12. Does any current direct theorem clash with this support?

## Outcomes

- Outcome A — COMMON NORM PRIME RESIDUE SUPPORT q ≡ ±1 (mod 7) GREEN.
- Outcome B — DEGREE-ONE RESIDUE EVALUATION AND BETA CUBIC GREEN; QUADRATIC
  PRIMITIVE-ROOT LIFT NEEDS ONE BRIDGE.
- Outcome C — COMPLETE SPLITTING GREEN; RESIDUE-FIELD IDENTIFICATION WITH
  ZMod q IS THE PRECISE FRONTIER.
- Outcome D — EXPECTED REAL-CUBIC RESIDUE CRITERION FAILS; REOPEN THE
  SPLITTING INTERPRETATION.

## Validation

At minimum:

    lake build DkMath.FLT.Seven.SevenRealCubicResidueCriterion
    lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareResidueSupport
    lake build DkMath.FLT.Seven
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquareResidueSupportApi
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquareResidueSupportAxiom
    git diff --check

If only one production file is used, adapt the focused build accordingly.

Print axioms for:
- residue-field evaluation;
- beta cubic relation / beta != 3;
- primitive seventh-root lift;
- Frobenius root-pair theorem;
- 7 | q^2-1;
- q mod 7 classification;
- gcd support theorem.

Run forbidden-source/import scans on every decisive file.
