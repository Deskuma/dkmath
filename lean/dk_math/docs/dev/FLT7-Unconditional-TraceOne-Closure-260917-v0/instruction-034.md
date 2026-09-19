# FLT7TC-005R28 — Square-root scalar split and Galois prime-support audit

Branch: research/FLT7-Unconditional-TraceOne-Closure-260917-v0

Authoritative inputs:
- report-032.md
- report-033.md
- PrimeTraceOneDirectRealCubicSquareRefinement.lean
- PrimeTraceOneDirectRealCubicSquareTwistObstruction.lean
- SevenRamifiedFusionPrimeLoadGalois.lean
- SevenRealCubicNumberField.lean

R27 freezes repeated power-refinement:
- seventh-power gauge normalization is obstructed;
- ordinary homogeneous restart is obstructed;
- square-gauge normalization is obstructed.

Do not extract further powers in this checkpoint.

Instead, use the R26 square roots as a coprime algebraic factorization of the
rational scalar a and audit their rational prime support.

## Goal

For a current DirectOrbitSquareRefinementPacket t, let

    r := t.gapSquareRoot
    s := t.quotientSquareRoot
    a := t.powerSplit.gapSplit.a
    R := natAbs (norm r)
    S := natAbs (norm s).

Productionize:

    IsCoprime r s
    Associated (r * s) (a : O)

and preferably an explicit unit equation

    r * s = unit * (a : O).

Retain:

    R * S = a^3
    0 < R
    R^2 < a.

Then classify what a common rational prime divisor of R and S means in the
cyclic real cubic field.

This is a prime-support audit, not a descent theorem.

## Part A — coprimality of the square roots

From:

    IsCoprime gapRoot quotientRoot

and:

    gapRoot      = gapSquareUnit * r^2
    quotientRoot = quotientSquareUnit * s^2

remove the unit factors and use IsCoprime.pow_iff to prove:

    IsCoprime r s.

Do not infer this from R,S.

Expose as a stable theorem on DirectOrbitSquareRefinementPacket.

## Part B — scalar product associated to a

From:

    gapRoot * quotientRoot = rootProductUnit * (a : O)^2

and the two unit-times-square equations, derive:

    Associated ((r*s)^2) ((a : O)^2).

Use Mathlib's:

    Associated.pow_iff

at exponent 2 in the integrally closed real-cubic integer ring to conclude:

    Associated (r*s) (a : O).

Do not cancel squares by a real embedding, because exponent two is not
injective over R.

Then expose an explicit unit:

    ∃ u : Oˣ, r*s = (u : O) * (a : O).

This is the preferred stable element-level scalar split.

## Part C — norm consequences and compatibility

Take natAbs norms and recover:

    R*S = a^3.

Check that this agrees definitionally/theorem-wise with the existing R26
norm theorem rather than creating a competing proof surface.

Retain:

    0 < R
    R^2 < a.

Also prove S > 0.

Do not claim gcd(R,S)=1.

## Part D — theta-unit status of r and s

Prove:

    ¬ theta ∣ r
    ¬ theta ∣ s.

Reason:
- gapRoot and quotientRoot are theta-units;
- if theta divided r or s, it would divide the corresponding square and hence
  the original root despite the unit factor.

Consequently:

    7 ∤ R
    7 ∤ S

using the exact ramified-prime/norm bridge already available in the real cubic
model.

If the final rational divisibility statement costs too much, the element-level
theta-unit facts are mandatory and the norm statement may be reported as a
frontier.

## Part E — common rational norm prime means two distinct primes above q

Let q be a rational prime with:

    q ∣ R
    q ∣ S.

Construct prime ideals P,Q of the real cubic ring of integers such that:

    P ∣ (r)
    Q ∣ (s)

and both contract to (q), or use an equivalent ideal-factorization theorem.

Use IsCoprime r s to prove:

    P ≠ Q.

Do not infer a common element divisor from q dividing both norms.

This is exactly the distinction that earlier checkpoints deliberately
preserved.

## Part F — classify the splitting type of a common norm prime

For q != 7, the real cubic field is cyclic Galois of degree three.

Use a neutral number-field/Galois splitting theorem if available to prove:

If q has two distinct primes above it, then q splits completely in the real
cubic field.

Preferred current-field conclusion:

    q splits completely in SevenRealCubic.Field.

If the explicit cyclotomic residue criterion is cheap, strengthen to:

    q ≡ 1 or -1 (mod 7)

equivalently for odd q:

    q ≡ 1 or 13 (mod 14).

Do NOT instantiate historical RamifiedSignedRootRoutingPacket merely to obtain
its quotient-prime address theorems.

It is acceptable to mine those files for a neutral lemma and promote that
lemma to a current/generic location.

## Part G — gcd support theorem

Define conceptually:

    C := Nat.gcd R S.

Prove the strongest honest statement available:

Every prime q dividing C:
- q != 7;
- q splits completely in the real cubic field;
- optionally q ≡ ±1 mod 7.

Do not prove C=1 unless a separate current theorem excludes split primes from
a.

This support theorem is the main arithmetic output if Part F succeeds.

## Part H — audit primes dividing a

Since:

    r*s = unit * a

every prime ideal above every rational prime dividing a is allocated to one of
the coprime factors r or s.

Audit the possible allocation types under the cyclic Galois action:

1. inert rational prime: unique prime above q, hence it lies entirely on one
   side;
2. split rational prime: three conjugate primes may be partitioned between
   r and s;
3. q=7: excluded by theta-unit status.

Record the induced possible q-adic exponents in R and S.

Do not assume Galois-invariance of the factor r.

## Part I — look for a current contradiction only after the support theorem

Search current direct-provenance facts for any theorem forcing a prime divisor
of a into a nonsplit residue class, or conversely forcing a common norm prime.

If such a theorem exists, combine it.

Otherwise record cleanly:

    the square-root scalar split refines the arithmetic support but does not
    yet close FLT7.

Do not import the historical receiver/routing conclusion as an assumption.

## Part J — generalization candidate

If Parts E-G require a reusable theorem of the form:

    coprime algebraic factors of a rational scalar
      -> common rational norm primes are split primes,

place the neutral theorem outside FLT7 if the hypotheses are genuinely generic
for finite Galois/Dedekind extensions.

Do not generalize the explicit q mod 7 criterion unless it is naturally tied
to the seventh real-cyclotomic field.

## Hard stops

- Repeated power-refinement remains frozen after R27.
- No inference IsCoprime r s -> Nat.Coprime R S.
- No use of historical receiver/routing packets as input.
- No claim that q|norm r gives q|r as an element.
- No successor/descent theorem.
- No FLT7 contradiction unless an independent current-provenance residue
  restriction clashes with the support theorem.
- No sorry/sorryAx/admit/unsafe/project axiom.

## Preferred production file

    DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicSquarePrimeSupport.lean

Tests:

    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSquarePrimeSupportApi.lean
    DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSquarePrimeSupportAxiom.lean

Create report-034.md and update ROADMAP.md.

## Report questions

1. Were r and s proved element-coprime?
2. Was Associated (r*s) a proved using Associated.pow_iff?
3. Was an explicit unit-times-scalar equation constructed?
4. Were r and s proved theta-units?
5. Was 7 excluded from R and S?
6. For q|R and q|S, were two distinct primes above q constructed?
7. Was complete splitting of such q proved?
8. Was the residue criterion q ≡ ±1 mod 7 obtained?
9. What is the exact prime support of gcd(R,S)?
10. Does any current theorem on a clash with that support?

## Outcomes

- Outcome A — SCALAR SPLIT AND COMMON-NORM-PRIME SPLITTING GREEN; CURRENT
  RESIDUE DATA CLOSES A CONTRADICTION.
- Outcome B — SCALAR SPLIT GREEN; GCD(R,S) SUPPORT RESTRICTED TO COMPLETELY
  SPLIT PRIMES; NO CONTRADICTION YET.
- Outcome C — ELEMENT SCALAR SPLIT GREEN; NORM-PRIME TO IDEAL-SPLITTING BRIDGE
  IS THE PRECISE FRONTIER.
- Outcome D — SQUARE ROOTS DO NOT RECOVER A RATIONAL SCALAR SPLIT; REOPEN R26.

## Validation

At minimum:

    lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquarePrimeSupport
    lake build DkMath.FLT.Seven
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquarePrimeSupportApi
    lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSquarePrimeSupportAxiom
    git diff --check

Print axioms for:
- square-root coprimality;
- associated scalar product;
- explicit unit-times-scalar equation;
- theta-unit theorems;
- common norm prime -> distinct primes above q;
- common norm prime -> complete splitting;
- gcd support theorem.

Run forbidden-source/import scans on every decisive file.
