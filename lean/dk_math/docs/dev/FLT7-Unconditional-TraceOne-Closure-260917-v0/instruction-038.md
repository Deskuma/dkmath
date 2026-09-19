# FLT7TC-005R32 — Cube-defect normal form of the square-root norm split

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:
- report-032.md
- report-034.md
- report-037.md
- PrimeTraceOneDirectRealCubicSquareRefinement.lean
- PrimeTraceOneDirectRealCubicSquarePrimeSupport.lean
- PrimeTraceOneDirectRealCubicResidueSupport.lean
- Mathlib Nat.factorization API

R31 proves that every prime dividing the gcd of the two square-root norms is
congruent to ±1 modulo 7.

This checkpoint combines that support theorem with the exact identity

    R * S = a^3

and produces the complete cube-defect normal form of R and S.

Do not search for a contradiction before the normal form is kernel-checked.

## Goal

For the current DirectOrbitSquareRefinementPacket t, let

    R := natAbs (norm t.gapSquareRoot)
    S := natAbs (norm t.quotientSquareRoot)
    a := t.powerSplit.gapSplit.a.

Construct positive naturals D1,D2,U,V satisfying

    R = D1 * D2^2 * U^3
    S = D1^2 * D2 * V^3
    a = D1 * D2 * U * V

with:
- D1 and D2 squarefree;
- Nat.Coprime D1 D2;
- every prime divisor of D1 or D2 is congruent to 1 or 6 modulo 7;
- D1*D2 divides gcd(R,S);
- the strict height refinement

      D1 * D2^3 * U^5 < V.

This is an arithmetic normal form, not a successor state.

## Part A — valuation ledger from R*S=a^3

Productionize a neutral theorem for positive naturals R,S,a:

If

    R*S = a^3

then for every prime q,

    R.factorization q + S.factorization q
      =
    3 * a.factorization q.

Use:
- Nat.factorization_mul for nonzero factors;
- Nat.factorization_pow.

Keep the theorem generic if convenient.

For the current packet, positivity/nonzeroness of R,S,a is already available
or should be derived from R26/R28.

## Part B — off-exception primes occur to cube multiplicity

Let

    exceptional7 q := q % 7 = 1 ∨ q % 7 = 6.

For a prime q with not exceptional7 q, prove:

1. q cannot divide both R and S, by R31.
2. If q divides R, then

       S.factorization q = 0
       3 ∣ R.factorization q.

3. If q divides S, then

       R.factorization q = 0
       3 ∣ S.factorization q.

This is the key interpretation:

    every non-cubic valuation defect is supported only at ±1 mod 7 primes.

Expose this as a stable packet theorem even if the later decomposition is
implemented separately.

## Part C — define the two cube-defect kernels

Using R.factorization, define conceptually:

    D1 := product of primes q with
            R.factorization q % 3 = 1

    D2 := product of primes q with
            R.factorization q % 3 = 2

and

    U := product over q of q^(R.factorization q / 3).

Equivalent definitions via Finsupp.prod are preferred if they simplify proofs.

Prove:

    R = D1 * D2^2 * U^3.

Also prove:

    Squarefree D1
    Squarefree D2
    Nat.Coprime D1 D2.

Do not assume the supports are disjoint; prove it from the mutually exclusive
remainders modulo 3.

A reusable generic theorem

    exists_cube_defect_decomposition_three

is welcome if the statement is clean.

## Part D — complementary defect on S

Use the valuation ledger from Part A.

For every prime q:
- if R exponent is 1 mod 3, S exponent is 2 mod 3;
- if R exponent is 2 mod 3, S exponent is 1 mod 3;
- if R exponent is 0 mod 3, S exponent is 0 mod 3.

Construct V such that:

    S = D1^2 * D2 * V^3.

Do not define a second unrelated pair of defect kernels for S. The point is
that the same D1,D2 occur with complementary exponents.

## Part E — reconstruct a exactly

Multiply the R and S normal forms:

    R*S = (D1*D2*U*V)^3.

Compare with:

    R*S = a^3.

Use injectivity of natural-number cubes to prove:

    a = D1 * D2 * U * V.

This literal equality is preferred over Associated/divisibility forms.

## Part F — exceptional support of D1,D2

Let q be prime.

If:

    q ∣ D1

or

    q ∣ D2,

then the R exponent modulo 3 is nonzero. By Part D the S exponent is also
nonzero. Hence q divides both R and S.

Apply R31:

    q % 7 = 1 ∨ q % 7 = 6.

Also prove:

    D1 * D2 ∣ Nat.gcd R S.

Optionally prove the stronger exact statement that every prime in D1*D2 has
positive valuation in both R and S.

Do not claim that D1*D2 equals the full gcd; cube factors may also be common.

## Part G — height refinement

Use the existing strict inequality:

    R^2 < a

and substitute:

    R = D1 * D2^2 * U^3
    a = D1 * D2 * U * V.

First prove:

    0 < D1
    0 < D2
    0 < U
    0 < V.

Cancel the positive common factor D1*D2*U and obtain exactly:

    D1 * D2^3 * U^5 < V.

Useful corollaries:

    U < V
    U^5 < V
    U^6 < a.

Do not call U a successor gap root.

## Part H — package the current normal form

Define a stable packet, conceptually:

    structure DirectOrbitCubeDefectPacket ... where
      squareRefinement : DirectOrbitSquareRefinementPacket p
      D1 D2 U V : Nat
      D1_pos : 0 < D1
      D2_pos : 0 < D2
      U_pos : 0 < U
      V_pos : 0 < V
      D1_squarefree : Squarefree D1
      D2_squarefree : Squarefree D2
      D1_D2_coprime : Nat.Coprime D1 D2
      gapNorm_eq :
        natAbs(norm gapSquareRoot) = D1 * D2^2 * U^3
      quotientNorm_eq :
        natAbs(norm quotientSquareRoot) = D1^2 * D2 * V^3
      unitPart_eq :
        a = D1 * D2 * U * V
      defect_dvd_gcd :
        D1*D2 ∣ gcd R S
      defect_prime_support :
        every prime divisor of D1*D2 is ±1 mod 7
      height :
        D1 * D2^3 * U^5 < V

Names may differ.

Provide a nonempty/choice constructor from every current square-refinement
packet.

## Part I — optional residue of the defect product

Because every prime divisor of D1 and D2 is ±1 mod 7, audit whether it is cheap
to prove:

    D1 % 7 = 1 ∨ D1 % 7 = 6
    D2 % 7 = 1 ∨ D2 % 7 = 6
    (D1*D2) % 7 = 1 ∨ (D1*D2) % 7 = 6.

This is optional. Do not block the checkpoint on a finite-product residue
lemma.

## Part J — clash audit

After the packet is green, inspect current direct provenance only.

Ask whether any existing theorem forces:
- D1=D2=1;
- a prime divisor of a outside the decomposition;
- a residue class of a incompatible with
      a = D1*D2*U*V;
- or a bound incompatible with
      D1*D2^3*U^5 < V.

Do not use historical routing/address assumptions.

If no clash exists, record the honest conclusion:

    R31 support plus R*S=a^3 yields a canonical exceptional cube-defect normal
    form, but not yet an FLT7 contradiction.

## Generic arithmetic candidate

Parts A-E are not FLT-specific.

If clean, place a generic theorem in DkMath.Lib.NumberTheory or a neutral
NumberTheory module:

    R*S=a^3
      -> complementary squarefree cube-defect decomposition.

The residue-support application remains in FLT7.

Do not over-generalize to arbitrary exponent n unless exponent 3 falls out
cleanly first.

## Hard stops

- No claim gcd(R,S)=1.
- No claim D1=D2=1 without a new theorem.
- No inference that all primes dividing a are ±1 mod 7.
- No successor/descent interpretation of U or V.
- No historical receiver/routing packet as input.
- No FLT7 contradiction unless a separate current theorem clashes with the
  normal form.
- No sorry/sorryAx/admit/unsafe/project axiom.

## Preferred production files

If the generic arithmetic split is clean:

    DkMath/Lib/NumberTheory/CubeDefect.lean

and current instantiation:

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicCubeDefect.lean

Otherwise a single FLT7-local module is acceptable.

Tests:

    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicCubeDefectApi.lean
    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicCubeDefectAxiom.lean

Create report-038.md and update ROADMAP.md.

## Report questions

1. Was the valuation ledger for R*S=a^3 proved?
2. Were off-exception prime exponents proved divisible by three?
3. Were D1,D2,U constructed with R=D1*D2^2*U^3?
4. Were D1,D2 proved squarefree and coprime?
5. Was S=D1^2*D2*V^3 proved with the same defects?
6. Was a=D1*D2*U*V proved?
7. Was every prime divisor of D1*D2 proved ±1 mod 7?
8. Was D1*D2 proved to divide gcd(R,S)?
9. Was D1*D2^3*U^5<V proved?
10. Did the normal form clash with any current direct-provenance theorem?

## Outcomes

- Outcome A — COMPLEMENTARY CUBE-DEFECT NORMAL FORM GREEN; CURRENT ARITHMETIC
  ALSO FORCES A CONTRADICTION.
- Outcome B — CUBE-DEFECT NORMAL FORM AND ±1 SUPPORT GREEN; NO CONTRADICTION
  YET.
- Outcome C — VALUATION/SUPPORT LEDGER GREEN; GLOBAL FACTORIZATION PACKAGING IS
  THE PRECISE FRONTIER.
- Outcome D — R*S=a^3 DOES NOT PRODUCE THE EXPECTED COMPLEMENTARY DEFECT FORM;
  REOPEN THE ARITHMETIC INTERPRETATION.

## Validation

At minimum:

    lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCubeDefect
    lake build DkMath.FLT.Seven
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCubeDefectApi
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCubeDefectAxiom
    git diff --check

If a generic CubeDefect module is created, build and axiom-audit it directly.

Print axioms for:
- valuation ledger;
- off-exception cube-multiplicity theorem;
- both defect decompositions;
- squarefree/coprime defect kernels;
- exact a reconstruction;
- defect gcd support;
- height refinement;
- current packet constructor.

Run forbidden-source/import scans on every decisive file.
