# FLT7TC-005R33 — Galois prime allocation and canonical common-factor normal form

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:

- report-033.md
- report-034.md
- report-036.md
- report-037.md
- report-038.md
- PrimeTraceOneDirectRealCubicSquareTwistObstruction.lean
- PrimeTraceOneDirectRealCubicSquarePrimeSupport.lean
- PrimeTraceOneDirectRealCubicSquareGaloisSupport.lean
- PrimeTraceOneDirectRealCubicResidueSupport.lean
- PrimeTraceOneDirectRealCubicCubeDefect.lean
- Mathlib Galois action on Ideal.primesOver

R32 gives the generic complementary cube-defect normal form.  This checkpoint
uses the special square-twisted additive equation to recover the actual Galois
allocation of common norm primes.

The expected new fact is:

    every common norm prime q is carried by exactly one of the three primes
    above q on the gap-square-root side and by the other two on the
    quotient-square-root side.

If this is kernel-checked, the two squarefree defect kernels D1,D2 collapse
arithmetically to one canonical common factor C = gcd(R,S).

## Goal

For the current DirectOrbitSquareRefinementPacket t, write

    r := t.gapSquareRoot
    s := t.quotientSquareRoot
    R := natAbs (norm r)
    S := natAbs (norm s)
    a := t.powerSplit.gapSplit.a.

For every prime q with q|R and q|S, prove the exact 1-versus-2 allocation of
the three primes above q.

Then derive the canonical integer normal form

    C := gcd R S

    R = C * U^3
    S = C^2 * V^3
    a = C * U * V

with

    C | a
    every prime divisor of C is ±1 mod 7
    C * U^5 < V.

This is still not a successor/descent theorem.

## Part A — principal ideal scalar split in the actual ring of integers

Reuse R28:

    r * s = unit * (a : SevenRealCubicInt).

Transport this equation to O = ring of integers and prove the principal-ideal
identity

    Ideal.span {rI} * Ideal.span {sI}
      =
    Ideal.span {(a : O)}.

Also transport the element coprimality:

    IsCoprime rI sI

or equivalently

    Ideal.span {rI} sup Ideal.span {sI} = top.

Do not rebuild this from norms.

## Part B — every prime above a common q is allocated to exactly one side

Let q be prime with q|R and q|S.

R30/R31 give:

- q != 7;
- exactly three primes above q;
- ramification index one;
- inertia degree one.

First prove q|a from R*S=a^3.

Let P be any prime ideal above q.

Because q|a, show:

    (a : O) in P.

Using the principal-ideal product from Part A and P.IsPrime, prove:

    rI in P or sI in P.

Use coprimality to prove not both.

Package:

    xor (rI in P) (sI in P)

for every P in primesOver(q).

This is the allocation partition.

## Part C — make the cyclic Galois orbit explicit

Choose one P0 above q containing rI. Existence comes from R29 because q|R.

Use the Galois action on primesOver and the checked order-three rotation to
define/order:

    P0
    P1 := sigma • P0
    P2 := sigma^2 • P0.

Prove:

- P0,P1,P2 are pairwise distinct;
- they exhaust primesOver(q).

Preferred API:

- Ideal.orbit_eq_primesOver;
- the IsGalois pretransitive action on primesOver;
- R30 cardinality = 3.

Do not identify ideals by hand through quotient evaluations if the Galois
action API suffices.

## Part D — rotation/membership compatibility

Let:

    r0 := r
    r1 := rotateEquiv r
    r2 := rotateEquiv (rotateEquiv r).

Prove the exact membership transport:

    ri in Pj
      iff
    r0 in sigma^(-i) • Pj

with the repository's exact action orientation.

At minimum obtain the concrete three cyclic equivalences needed below.

Be extremely careful about map versus comap orientation.

## Part E — two gap primes would force all three

Assume two distinct primes above q contain rI.

Using Part C/D, choose a prime P above q for which two of

    r0, r1, r2

lie in P.

Now use the exact R27 equation

    c0*(r0^7)^2 + c1*(r1^7)^2 + c2*(r2^7)^2 = 0.

The coefficients c0,c1,c2 are units, hence none belongs to the proper prime
ideal P.

If exactly two rotated roots lie in P, the equation forces the third term into
P and therefore forces the third rotated root into P.

Translate that membership back via Part D. Conclude all three primes above q
contain rI.

But q|S gives some prime Q above q containing sI by R29. Since all three
primes above q now contain rI, Q contains both rI and sI, contradicting
coprimality.

Therefore:

    at most one prime above q contains rI.

R29 gives at least one, hence exactly one.

This is the decisive new structural theorem.

## Part F — quotient side gets exactly two primes

From Part B and the total cardinality three, deduce:

    exactly two primes above q contain sI.

Do not prove this independently from the square-twisted equation.

Expose clean cardinal statements, conceptually:

    ncard {P in primesOver(q) | rI in P} = 1
    ncard {P in primesOver(q) | sI in P} = 2.

A finite-subtype formulation is acceptable.

## Part G — exact q-adic norm exponents

Let:

    m := a.factorization q.

Use:

- q is completely split;
- e=f=1;
- each prime above q occurs in the principal ideal (a) with exponent m;
- Part E/F allocation;
- ideal norm / principal ideal factorization.

Prove:

    R.factorization q = m
    S.factorization q = 2*m.

This is stronger than the R32 modulo-three ledger.

If the ideal-factorization API makes literal Nat.factorization equalities
expensive, an equivalent padicValNat statement is acceptable, provided it is
converted to the natural norm factorization in the packet layer.

Do not infer these equalities merely from R*S=a^3.

## Part H — noncommon prime exponents

Let q be prime dividing a.

If q does not divide both R and S, use

    R.factorization q + S.factorization q = 3*a.factorization q

to prove the only possibilities are:

    (Rexp,Sexp) = (3*m,0)
    or
    (0,3*m).

This part does not need Galois theory once non-commonness is known.

Together with Part G, every prime divisor of a has one of exactly three
allocation types:

    gap-full:      (3m,0)
    split 1-to-2:  (m,2m)
    quotient-full: (0,3m).

## Part I — canonical common factor C

Define:

    C := Nat.gcd R S.

From Parts G/H prove for every prime q:

    C.factorization q =
      if q divides both R and S then a.factorization q else 0.

Deduce:

    C | a.

Also use R31 to prove:

    every prime divisor q of C satisfies
      q % 7 = 1 or q % 7 = 6.

This upgrades R31 from a support theorem to a canonical factor theorem.

## Part J — canonical cubic decomposition

Using the exact exponent classification, construct positive U,V with:

    R = C * U^3
    S = C^2 * V^3
    a = C * U * V.

Prefer a factorization-based generic constructor after the packet-specific
allocation theorem.

Prove the literal equalities, not only divisibility.

This decomposition should be canonical up to the ordinary uniqueness of
natural cube roots.

Relate it to R32:

- D1,D2 are the mod-three squarefree shadow of C;
- do not delete the R32 API, but state a bridge if cheap.

## Part K — height refinement

Use:

    R^2 < a

and substitute:

    R = C*U^3
    a = C*U*V.

With positivity prove:

    C * U^5 < V.

Useful corollaries:

    U^5 < V
    U^6 < a.

Do not interpret U as a successor FLT gap root.

## Part L — package

Define a stable packet, conceptually:

    structure DirectOrbitPrimeAllocationPacket ... where
      squareRefinement : DirectOrbitSquareRefinementPacket p
      C U V : Nat
      C_pos : 0 < C
      U_pos : 0 < U
      V_pos : 0 < V
      C_eq_gcd : C = gcd R S
      C_dvd_a : C | a
      common_prime_allocation_one_two : ...
      common_prime_gap_exp : ...
      common_prime_quotient_exp : ...
      C_prime_support : ...
      R_eq : R = C * U^3
      S_eq : S = C^2 * V^3
      a_eq : a = C * U * V
      height : C * U^5 < V.

Names may differ.

Provide a constructor from every current square-refinement packet.

## Part M — clash audit

Only after the 1-to-2 allocation theorem and canonical C normal form are
green, inspect current direct-provenance facts for a clash.

Specifically ask:

- can a common prime be forced to allocate two primes to r by another current
  theorem?
- does the twisted coefficient/local residue data forbid the remaining
  one-prime allocation?
- does the original summit impose a q-adic exponent on a incompatible with
  Rexp=m and Sexp=2m?
- does C|a plus C*U^5<V clash with another checked bound?

Do not import historical routing/address packets.

If no clash exists, record Outcome B and stop. The next research problem is
then a genuinely local residue analysis of the surviving 1-to-2 allocation.

## Hard stops

- No cardinal allocation claim from norm exponents alone.
- No manual assumption that the Galois rotation acts transitively; use the
  checked IsGalois action.
- No confusion between rotateEquiv on elements and the ideal action
  orientation.
- No q-adic exponent equality before ideal allocation is proved.
- No deletion/reinterpretation of R32.
- No successor/descent or FLT7 contradiction claim without a separate clash.
- No historical receiver/routing packet as input.
- No sorry/sorryAx/admit/unsafe/project axiom.

## Preferred production file

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicPrimeAllocation.lean

A small generic ideal-allocation helper module is acceptable if genuinely
reusable.

Tests:

    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicPrimeAllocationApi.lean
    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicPrimeAllocationAxiom.lean

Create report-039.md and update ROADMAP.md.

## Report questions

1. Was the principal-ideal scalar split proved in the actual ring of integers?
2. Was every prime above a common q proved allocated to exactly one of r,s?
3. Was the three-prime Galois orbit made explicit?
4. Was rotation/membership compatibility kernel-checked?
5. Was "two r-primes -> all three r-primes" proved from the R27 equation?
6. Was exactly one prime above q assigned to r and exactly two to s?
7. Were v_q(R)=v_q(a) and v_q(S)=2*v_q(a) proved?
8. Were noncommon exponent pairs classified as (3m,0)/(0,3m)?
9. Was C=gcd(R,S) proved to divide a with ±1 mod 7 prime support?
10. Were R=C*U^3, S=C^2*V^3, a=C*U*V proved?
11. Was C*U^5<V proved?
12. Did any current theorem clash with the surviving 1-to-2 allocation?

## Outcomes

- Outcome A — 1-TO-2 PRIME ALLOCATION GREEN AND CURRENT LOCAL DATA CLOSES A
  CONTRADICTION.
- Outcome B — 1-TO-2 PRIME ALLOCATION AND CANONICAL CUBIC NORMAL FORM GREEN;
  NO CONTRADICTION YET.
- Outcome C — ALLOCATION CARDINALITY GREEN; IDEAL-VALUATION/NORM-EXPONENT
  TRANSPORT IS THE PRECISE FRONTIER.
- Outcome D — SQUARE-TWISTED EQUATION DOES NOT FORCE THE EXPECTED ALLOCATION;
  REOPEN THE R32 INTERPRETATION.

## Validation

At minimum:

    lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicPrimeAllocation
    lake build DkMath.FLT.Seven
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicPrimeAllocationApi
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicPrimeAllocationAxiom
    git diff --check

Print axioms for:

- ideal scalar split;
- allocation xor theorem;
- Galois orbit enumeration;
- rotation/membership bridge;
- two-to-three forcing theorem;
- one-versus-two allocation cardinalities;
- norm exponent equalities;
- C|a and support theorem;
- canonical C,U,V normal form;
- height refinement.

Run forbidden-source/import scans on every decisive file.
