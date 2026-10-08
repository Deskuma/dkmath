# Instruction 018 - Centered fold gcd normal form and odd-gap product

## Mission

Continue from Instruction 017.

Instruction 017 produced a genuinely useful arithmetic coordinate system for a centered fold pair.

For j < n, let:

  L(n,j) = n^2 + centeredLeftOffset n j
  R(n,j) = n^2 + centeredRightOffset n j
  G(j)   = 2*j + 1
  N(n)   = centeredFoldNorm n = n^2 + (n+1)^2

The proved identities include:

  L + R = N
  R - L = G
  N = 2*L + G

and prime common support is exactly controlled by divisibility of both N and G.

The first required target of Instruction 018 is the exact gcd normal form:

  gcd(L,R) = gcd(N,G)

After that theorem is fixed, aggregate the entire internal odd-gap ladder

  1, 3, 5, ..., 2*n-1

into one finite product and determine exactly how much of N is visible through the fold gcds.

The central question is:

Can the local common-support data of all centered fold pairs be compressed into one exact primorial-like or valuation object without losing the fresh-prime branch?

Do not claim a Legendre advance unless a new full-cover obstruction is actually proved.

All new instruction, findings, and report artifacts must remain parser-safe plain text. Avoid backslash notation and LaTeX control sequences.

## Required source audit

Audit at minimum:

DkMath.NumberTheory.Legendre.QuadraticGnomonFold
DkMath.NumberTheory.Legendre.CenteredOwnerFold
DkMath.NumberTheory.Legendre.CenteredFoldSupportNorm
DkMath.NumberTheory.Legendre.CenteredPair
DkMath.NumberTheory.Legendre.OldSupportGcd
DkMath.NumberTheory.Legendre.GnomonResidueCover
DkMath.NumberTheory.Legendre.CyclotomicPersistence
DkMath.NumberTheory.Primitive
DkMath.NumberTheory.PrimorialUniverse
DkMath.CosmicFormula and its cyclotomic or GTail bridge modules where relevant

Also audit Mathlib for:

- gcd addition and subtraction identities
- gcd multiplication by a coprime factor
- finite product divisibility
- Nat.factorization support
- padicValNat product or valuation formulas
- minFac and composite small-factor bounds
- existing odd double factorial or odd-product APIs
- factorial big-operator APIs

Audit DkMath Pascal and Wallis modules for an existing odd half-product before defining a new duplicate abstraction.

Record exact reusable theorem names in source-inventory-018.md.

## Phase 1 - exact centered pair gcd normal form

Implement the report-017 proposed theorem:

  centeredPair_gcd_eq_norm_gap

Statement shape:

  for j < n,

  Nat.gcd
    (n^2 + centeredLeftOffset n j)
    (n^2 + centeredRightOffset n j)
  =
  Nat.gcd
    (centeredFoldNorm n)
    (2*j + 1)

Preferred proof route:

1. Replace gcd(L,R) by gcd(L,R-L) using R-L = G.
2. Replace gcd(N,G) by gcd(2*L+G,G).
3. Use oddness of G to remove the factor 2 from gcd(2*L,G).
4. Avoid a new valuation proof if standard gcd lemmas close the result.

Keep a Nat-safe proof.

Mandatory regressions:

- j = 0, gap 1
- n = 3, j = 2, gcd = 5 fresh above n
- n = 6, j = 2, gcd = 5 old
- at least one repeated-prime gcd example if one exists in a bounded scan

## Phase 2 - exact local corollaries

From the gcd normal form derive:

- gcd(L,R) divides centeredFoldNorm n
- gcd(L,R) divides 2*j+1
- every prime divisor of gcd(L,R) is 1 mod 4
- gcd(L,R) is odd
- old versus fresh classification by comparison with n
- any fresh prime common divisor satisfies n < p < 2*n

The upper bound should come from p dividing an internal gap at most 2*n-1.

Do not collapse a nontrivial fresh gcd into gcd = 1.

Preserve the existing OldSupportGcd fresh-prime branch.

## Phase 3 - define the odd-gap aggregate

Prefer reuse of centeredInternalGaps.

Define, only if no equivalent reusable product already exists:

  centeredOddGapProduct n
  =
  product over j in range n of (2*j+1)

This is the arithmetic object usually written as:

  1 * 3 * 5 * ... * (2*n-1)

Do not depend on double-factorial notation in theorem names unless an existing library API already uses it.

Prove:

- centeredOddGapProduct 0 = 1
- positive for all n
- successor recursion:
  centeredOddGapProduct (n+1)
  =
  centeredOddGapProduct n * (2*n+1)

Also prove equality with the product of centeredInternalGaps if both carriers are retained.

## Phase 4 - prime support of the odd-gap product

For prime p, prove the exact support criterion:

  p divides centeredOddGapProduct n
  iff
  p != 2 and p < 2*n

Use the fact that every odd prime below 2*n occurs literally as one internal gap p = 2*j+1.

Handle n = 0 and small n exactly.

This theorem is the direct primorial bridge:

the prime support of the odd-gap product is exactly the odd prime basis below 2*n.

If useful, define a finite odd prime basis such as:

  oddPrimeScalesBelowTwice n

but prefer an existing primeScalesUpTo filter if it gives a cleaner API.

## Phase 5 - primorial comparison

Audit whether the squarefree radical or prime-support product of centeredOddGapProduct n can be identified with the odd part of a bounded primorial.

A preferred finite statement is:

  product of distinct prime divisors of centeredOddGapProduct n
  =
  product of primes p with p < 2*n and p != 2

If the existing PrimorialUniverse finitePrimeBasisProduct can express this without awkward division by 2, bridge to it.

Do not introduce a second competing primorial framework.

The goal is to show precisely how the internal odd-gap ladder contains the odd primorial support.

## Phase 6 - aggregate norm-gap gcd

Define:

  centeredNormGapGcd n
  =
  Nat.gcd (centeredFoldNorm n) (centeredOddGapProduct n)

This is a support-level aggregate.

Prove for prime p:

  p divides centeredNormGapGcd n
  iff
  p divides centeredFoldNorm n and p != 2 and p < 2*n

Then connect this to local fold pairs:

  p divides centeredNormGapGcd n
  iff
  there exists j < n such that p divides gcd(L(n,j),R(n,j))

for prime p.

This must include fresh primes above n.

Then add the old-support specialization:

  p <= n
  and
  p divides centeredNormGapGcd n

iff p occurs as common bounded support in at least one centered fold pair.

Reuse centeredCommonSupportIndices.

## Phase 7 - composite detector for the fold norm

Investigate and, if correct, prove the following exact classification for positive n:

  centeredFoldNorm n is prime
  iff
  centeredNormGapGcd n = 1

Equivalent pairwise form:

  centeredFoldNorm n is prime
  iff
  every centered fold pair has gcd 1

This is a major acceptance target, but prove it only if the finite inequalities close exactly.

Expected proof idea for the composite direction:

- centeredFoldNorm n is odd
- if it is composite, choose a small prime divisor using minFac or an existing small-factor theorem
- show that a suitable prime divisor p satisfies p < 2*n
- because p is odd, p appears in centeredOddGapProduct n
- therefore the aggregate gcd is nontrivial

Audit small anchors n = 1,2,3 separately if the uniform inequality needs n >= 4.

Do not bury finite exceptions.

Mandatory calibration:

- n = 1, norm 5
- n = 2, norm 13
- n = 3, norm 25 and aggregate gcd 5
- n = 6, norm 85 and aggregate gcd divisible by 5
- n = 297, norm 177013, known prime from report-017 diagnostics if kernel verification is affordable

Do not treat Python primality diagnostics as kernel theorems unless rechecked in Lean.

## Phase 8 - product of local fold gcds

Define, if useful:

  centeredFoldGcdProduct n
  =
  product over j in range n of gcd(L(n,j),R(n,j))

Using the gcd normal form, prove:

  centeredFoldGcdProduct n
  =
  product over j in range n of gcd(centeredFoldNorm n, 2*j+1)

Then prove safe divisibility bounds:

  centeredFoldGcdProduct n divides
  (centeredFoldNorm n)^n

and

  centeredFoldGcdProduct n divides
  centeredOddGapProduct n

These preserve multiplicity and are stronger than a support union statement.

Do not claim centeredFoldGcdProduct equals centeredNormGapGcd.
They generally encode different valuation multiplicities.

## Phase 9 - valuation formula

Audit padicValNat and factorization APIs.

For prime p, seek the exact formula:

  v_p(centeredFoldGcdProduct n)
  =
  sum over j < n of
    min(v_p(centeredFoldNorm n), v_p(2*j+1))

Use the repository's existing valuation conventions and zero hypotheses.

If the exact theorem is expensive, first prove the factorization-coordinate version.

Then compare with:

  v_p(centeredNormGapGcd n)
  =
  min(
    v_p(centeredFoldNorm n),
    v_p(centeredOddGapProduct n)
  )

The report must explicitly distinguish:

- support aggregate centeredNormGapGcd
- incidence or multiplicity aggregate centeredFoldGcdProduct

This distinction is essential.

## Phase 10 - valuation of the odd-gap product

Only if current APIs support it cleanly, derive an exact valuation formula for centeredOddGapProduct.

Possible forms:

- sum over odd multiples of p^k below 2*n
- difference of factorial valuations
- reuse of an existing Wallis or odd-half-product identity

Do not build a large new factorial theory for this checkpoint.

A clean bridge to existing Pascal or Wallis odd-product code is preferable.

If no compact theorem is available, record the exact missing API and stop this phase.

## Phase 11 - old and fresh common-support split

Using centeredNormGapGcd, define or characterize two prime regions:

Old:
  p <= n

Fresh:
  n < p < 2*n

For p dividing centeredFoldNorm n, the internal fold can only see p if p < 2*n.

Prove exact existence statements:

- an old visible prime gives common old support in some fold pair
- a fresh visible prime gives a nontrivial common divisor in some fold pair but not old bounded support
- all such primes are 1 mod 4

This should unify the n=6 old example and the n=3 fresh example.

## Phase 12 - cyclotomic interpretation audit

The fold norm has the form:

  centeredFoldNorm n
  =
  n^2 + (n+1)^2

This is the homogeneous degree-2 evaluation of the fourth cyclotomic shape:

  Phi_4(a,b) = a^2 + b^2

Audit existing DkMath cyclotomic APIs before adding anything.

If a light bridge is available, prove that a prime p dividing centeredFoldNorm n has the order-four address expected from the ratio of consecutive coordinates modulo p.

Target conceptual statement:

  p divides centeredFoldNorm n
  implies
  the square of n/(n+1) is -1 mod p

with denominator nonzero already supplied by
prime_dvd_centeredFoldNorm_not_dvd_succ.

If existing multiplicative-order APIs make it clean, strengthen to order 4.

Do not create a heavy cyclotomic-field dependency merely for this observation.

The existing mod-four theorem is already sufficient if the order-four bridge is not cheap.

## Phase 13 - consecutive-shell aggregate separation

Instruction 017 proved:

  Coprime(N(n), N(n+1))

Use the aggregate divisibility results to prove, if straightforward:

  Coprime(
    centeredNormGapGcd n,
    centeredNormGapGcd (n+1)
  )

and similarly, if justified:

  Coprime(
    centeredFoldGcdProduct n,
    centeredFoldGcdProduct (n+1)
  )

The second should follow if each local-gcd product divides a power of its shell norm.

This gives an exact shell-to-shell separation of all common-fold multiplicity.

State clearly that it does not by itself rule out full cover.

## Phase 14 - relation to primorial and primitive structure

The user-facing research question is whether the fold exposes a primitive primorial-like structure.

Do not use that phrase as a theorem name without an exact definition.

Instead answer these precise questions:

1. Is the prime support of centeredOddGapProduct exactly the odd bounded-prime universe below 2*n?
2. Is centeredNormGapGcd exactly the part of centeredFoldNorm visible inside that odd prime universe?
3. Does a prime divisor of centeredFoldNorm carry a degree-4 cyclotomic address?
4. Are consecutive visible norm parts coprime?
5. Does any of this yield a new primitive-prime or first-appearance theorem across n?

Only item 5 would justify introducing new primitive terminology.

If no first-appearance theorem is proved, keep the result as a primorial/cyclotomic bridge only.

## Phase 15 - test connection to the Legendre full-cover packet

This phase is mandatory and skeptical.

Under:

  SquareOffsetsFullyCovered n

determine whether the new gcd aggregates impose any condition beyond existing support coverage.

Test at least:

- does full cover force centeredNormGapGcd n > 1?
- does full cover force any fold pair to have nontrivial gcd?
- does full cover force an old common-support pair?
- can a fully covered pair family have every fold gcd equal to 1?

Do not assume the answer.

Use bounded search to find the smallest compatible patterns or counterexamples.

If the gcd aggregate is independent of full cover, say so explicitly.

## Phase 16 - bounded diagnostics

For a justified finite range, record:

- centeredFoldNorm n
- primality or factorization diagnostic
- centeredOddGapProduct support, not necessarily full huge product value
- centeredNormGapGcd n
- number of fold pairs with gcd > 1
- old versus fresh common-gcd prime factors
- centeredFoldGcdProduct factorization or valuations where feasible
- whether n is a near-miss shell from Instruction 016
- whether any new gcd statistic correlates exactly with U or full-cover failure

Mandatory anchors:

  3
  5
  6
  8
  11
  19
  29
  297
  1031 if runtime permits without huge integer products

For large n, store factorizations, supports, or valuations instead of enormous decimal products.

Do not infer asymptotics.

## Phase 17 - next theorem judgment

At the end choose exactly one next contract.

Possible directions:

A. Full-cover obstruction from fold multiplicity

The new gcd or valuation aggregate imposes an inequality incompatible with full cover.

B. Primitive/cyclotomic first-appearance law

The fold norm sequence admits a provable primitive prime-address theorem useful for shell transitions.

C. Exact arithmetic bridge only

The gcd normal form, odd primorial support, composite detector, and valuation aggregate are exact but independent of full cover.

D. One precise valuation bridge remains

The support theory closes, but one exact padic or product theorem blocks the aggregate classification.

Do not disguise Legendre itself as the next provider.

## Expected implementation surface

Prefer extending:

DkMath/NumberTheory/Legendre/CenteredFoldSupportNorm.lean

Add a new focused module only if the aggregate product and valuation API becomes too large, for example:

DkMath/NumberTheory/Legendre/CenteredFoldGcdAggregate.lean

If a generic odd-product theorem belongs in Pascal or a neutral arithmetic namespace, keep dependencies acyclic and add only a bridge in Legendre.

Do not import heavy analytic modules.

## Validation

For all new production declarations:

- focused builds
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- forbidden-token scan
- print axioms for every new public declaration
- git diff --check

All new production declarations must remain free of sorryAx.

Preserve current file-header and file-marker conventions.

## Durable checkpoint protocol

Update findings after:

- gcd normal form
- local prime corollaries
- odd-gap product
- prime support and primorial bridge
- aggregate gcd
- prime iff aggregate-gcd-one classification
- local gcd product
- valuation formula
- old/fresh split
- cyclotomic audit
- consecutive-shell aggregate coprimality
- full-cover relevance test
- bounded diagnostics
- final judgment

Preserve false conjectures and smallest counterexamples.

## Final report

Answer explicitly:

1. Was centeredPair_gcd_eq_norm_gap proved exactly?
2. What are the exact old and fresh prime consequences?
3. What finite object represents 1*3*5*...*(2*n-1)?
4. Is its prime support exactly all odd primes below 2*n?
5. How does this object relate to the existing primorial universe?
6. What exactly does centeredNormGapGcd measure?
7. Is centeredFoldNorm n prime iff centeredNormGapGcd n = 1 for n>0?
8. What is the exact product of local fold gcds?
9. What valuation identity was proved for that product?
10. How do support aggregate and multiplicity aggregate differ?
11. Does the fold norm have a clean Phi_4 or order-four cyclotomic interpretation?
12. Are the aggregate fold-gcd objects coprime across consecutive shells?
13. Does any of the new arithmetic constrain SquareOffsetsFullyCovered beyond existing theorems?
14. What single next theorem should be attempted?

End with exactly one judgment:

Outcome A - FOLD GCD AGGREGATE YIELDS A NEW FULL-COVER OBSTRUCTION
Outcome B - FOLD GCD AGGREGATE YIELDS A NEW PRIMORIAL OR CYCLOTOMIC BRIDGE
Outcome C - FOLD GCD AGGREGATE IS EXACT BUT FULL-COVER INDEPENDENT
Outcome P - ONE PRECISE VALUATION OR PRODUCT BRIDGE REMAINS
