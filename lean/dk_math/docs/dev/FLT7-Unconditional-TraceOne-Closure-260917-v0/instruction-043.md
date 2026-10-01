# FLT7TC-005R37 — Canonical gcd cubic split of the square-root norms

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:

- report-042.md
- PrimeTraceOneDirectRealCubicCanonicalCommonFactor.lean
- PrimeTraceOneDirectRealCubicCubeDefect.lean
- PrimeTraceOneDirectRealCubicResidueSupport.lean
- PrimeTraceOneDirectRealCubicSquareRefinement.lean

R36 has kernel-checked the exact common-prime natural exponents. Writing

    R := Int.natAbs (norm t.gapSquareRoot)
    S := Int.natAbs (norm t.quotientSquareRoot)
    a := t.powerSplit.gapSplit.a
    m := a.factorization q,

for every prime q dividing both R and S:

    R.factorization q = m
    S.factorization q = 2*m.

The neutral cube ledger already gives for every q:

    R.factorization q + S.factorization q = 3 * a.factorization q.

This checkpoint is purely arithmetic. Do not reopen Galois, ideal, residue-field, successor, or descent arguments.

## Goal

Construct a canonical packet with

    C := Nat.gcd R S

and positive U,V satisfying literal equalities

    R = C * U^3
    S = C^2 * V^3
    a = C * U * V.

Also prove:

    C | a
    Nat.Coprime C U
    Nat.Coprime C V
    Nat.Coprime U V
    every prime q | C satisfies q % 7 = 1 or q % 7 = 6
    C * U^5 < V.

Preferred cheap consequences:

    U^5 < V
    U^6 < a.

Stop after the canonical packet and an immediate clash audit.

## Part A — three-way prime classification on a

For q prime with q | a, prove q divides at least one of R or S using

    R * S = a^3.

Classify q into exactly one of:

    Common(q)       := q | R and q | S
    GapOnly(q)      := q | R and not q | S
    QuotientOnly(q) := not q | R and q | S.

Prove the three predicates are pairwise disjoint and exhaustive on a.primeFactors.

Do not use residue classes modulo seven for this classification.

## Part B — exact exponent table for all primes dividing a

For common q, reuse R36:

    (R.factorization q, S.factorization q) = (m, 2*m).

For gap-only q, use the cube ledger and S.factorization q = 0 to prove

    R.factorization q = 3*m
    S.factorization q = 0.

For quotient-only q, prove

    R.factorization q = 0
    S.factorization q = 3*m.

Expose a stable theorem giving the complete three-case exponent table.

Do not infer noncommon exponents from modulo-three congruence alone; use the exact ledger.

## Part C — finite canonical supports

Define finite supports inside a.primeFactors, conceptually:

    commonSupport
    gapOnlySupport
    quotientOnlySupport.

Each support should be a filter of a.primeFactors by the Part A predicates.

Prove:

    commonSupport ∪ gapOnlySupport ∪ quotientOnlySupport = a.primeFactors

with pairwise disjointness.

## Part D — canonical products

Define

    commonFactorProduct :=
      product over q in commonSupport of q^(a.factorization q)

    canonicalGapCubeRoot U :=
      product over q in gapOnlySupport of q^(a.factorization q)

    canonicalQuotientCubeRoot V :=
      product over q in quotientOnlySupport of q^(a.factorization q).

All three products are positive.

Use Part B pointwise on a.primeFactors to prove directly:

    R = commonFactorProduct * U^3
    S = commonFactorProduct^2 * V^3
    a = commonFactorProduct * U * V.

Preferred proof pattern: reconstruct numbers from primeFactors/factorization as in PrimeTraceOneDirectRealCubicCubeDefect.lean, or use Nat.factorization_inj after proving both sides nonzero.

Do not introduce arbitrary existential cube roots when these canonical finite products are available.

## Part E — identify the common product with gcd

Define

    C := Nat.gcd R S.

Use Nat.factorization_gcd and the Part B exponent table to prove primewise that

    C.factorization q =
      if Common(q) then a.factorization q else 0

for prime q, and then prove

    C = commonFactorProduct.

Equivalently the equality may be proved by Nat.factorization_inj.

Consequences:

    C | R
    C | S
    C | a.

The last statement must use the exact common exponent formula, not only gcd divisibility.

## Part F — literal canonical normal form

Substitute Part E into Part D and expose:

    R = C * U^3
    S = C^2 * V^3
    a = C * U * V.

These literal equalities are mandatory.

## Part G — pairwise coprimality

From support disjointness prove:

    Nat.Coprime C U
    Nat.Coprime C V
    Nat.Coprime U V.

Use prime-support arguments or pairwise coprime finite products. Do not infer coprimality merely from the three reconstruction equalities.

These fields are important for the next local residue checkpoint and should be public if green.

## Part H — common-factor residue support

Reuse the existing R31 theorem for prime divisors of gcd R S to prove:

    q.Prime -> q | C -> q % 7 = 1 or q % 7 = 6.

Do not rebuild the finite-field primitive-seventh-root argument.

Optional useful corollary:

    7 does not divide C.

if it follows immediately from the residue support theorem.

## Part I — relation to R32 cube defect

Do not delete or modify DirectOrbitCubeDefectPacket.

Record the conceptual relation:

- R32 D1,D2 record only the common-factor exponent modulo 3;
- canonical C retains the full common exponent;
- canonical U,V contain only exclusive support and are therefore pairwise coprime with C.

If cheap, prove primewise bridge theorems:

    q | D1 iff q | C and C.factorization q % 3 = 1
    q | D2 iff q | C and C.factorization q % 3 = 2.

These bridge theorems are optional.

Do not assert C = D1*D2. This is false when a common-prime exponent is divisible by 3 or exceeds its residue representative.

## Part J — height refinement

Use the existing strict bound

    R^2 < a

and the canonical identities

    R = C*U^3
    a = C*U*V

with positivity to prove

    C * U^5 < V.

Then, if cheap, derive

    U^5 < V
    U^6 < a.

Do not interpret U or V as a successor-state gap/root.

## Part K — stable production packet

Create a packet conceptually:

    structure DirectOrbitCanonicalCommonFactorPacket ... where
      squareRefinement : DirectOrbitSquareRefinementPacket p
      C U V : Nat
      C_pos U_pos V_pos : ...
      C_eq_gcd : C = Nat.gcd R S
      C_dvd_a : C | a
      R_eq : R = C * U^3
      S_eq : S = C^2 * V^3
      a_eq : a = C * U * V
      C_U_coprime : Nat.Coprime C U
      C_V_coprime : Nat.Coprime C V
      U_V_coprime : Nat.Coprime U V
      C_prime_support : ...
      height : C * U^5 < V

Names may differ.

Provide a constructor from every current DirectOrbitSquareRefinementPacket.

Prefer to continue in:

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicCanonicalCommonFactor.lean

unless a neutral arithmetic helper materially simplifies the proof.

## Part L — immediate clash audit and stop

After the packet is green, audit only existing checked theorems for an immediate contradiction.

Questions:

- Does any existing theorem force C = 1?
- Does existing element-level coprimality of the algebraic square roots imply any stronger rational-norm coprimality now that the allocation is explicit?
- Does the projective unit-class or twisted-signature layer forbid a nontrivial C?
- Does the height inequality clash with any existing independent upper bound on V?
- Does 7 not dividing C interact with current ramified provenance to force triviality?

Do not start a new residue calculation in this checkpoint.

Expected result is Outcome B unless an already checked theorem closes the clash.

## Hard stops

- No assumption that Nat.Coprime of algebraic elements implies coprime rational norms.
- No assumption that C is squarefree.
- No C = D1*D2 claim.
- No use of R32 modulo-three data in place of the exact R36 common exponents.
- No successor/descent interpretation of U or V.
- No new residue-field analysis in R37.
- No FLT7 contradiction claim without an independent checked clash.
- No sorry, sorryAx, admit, unsafe, or project axiom.

## Tests

Update/add focused API and axiom audits for the canonical packet and its decisive theorems.
Keep the existing R35/R36 tests green.

Create report-043.md and update ROADMAP.md.

## Report questions

1. Was the prime support of a partitioned exhaustively into common/gap-only/quotient-only?
2. Was the exact full exponent table kernel-checked?
3. Were canonical finite products U and V constructed rather than arbitrary roots chosen?
4. Was the common product identified exactly with gcd R S?
5. Was C | a proved?
6. Were R=C*U^3, S=C^2*V^3, a=C*U*V proved literally?
7. Were C,U,V proved pairwise coprime?
8. Was the q mod 7 = 1 or 6 support theorem transported to C?
9. Was C*U^5<V proved?
10. Did the immediate existing-theorem audit produce a contradiction?

## Outcomes

- Outcome A — canonical gcd cubic split green and current checked data immediately closes a contradiction.
- Outcome B — canonical C,U,V packet green; no contradiction yet.
- Outcome C — exponent table/support partition green; identifying the common product with gcd is the precise frontier.
- Outcome D — canonical gcd identification green; reconstructing literal R,S,a products is the precise frontier.
- Outcome E — canonical products green; pairwise coprimality or height refinement is the precise frontier.

## Validation

At minimum:

    lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCanonicalCommonFactor
    lake build DkMath.FLT.Seven
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCanonicalCommonFactorApi
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCanonicalCommonFactorAxiom
    lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicCanonicalCommonFactorScratch.lean
    git diff --check

Print axioms for:

- complete prime exponent classification;
- common product = gcd;
- C | a;
- the three canonical equalities;
- the three pairwise coprimality theorems;
- C prime residue support;
- height refinement.

Run forbidden-source/import scans on every decisive file.
