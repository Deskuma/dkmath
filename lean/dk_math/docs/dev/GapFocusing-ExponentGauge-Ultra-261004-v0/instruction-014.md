# Instruction 014 — Legendre sqrt rough support stratification / singleton cofactor census

## Mission

Continue from Instruction 013.

Instruction 013 converted the independent sqrt cutoff

    P = Nat.sqrt n

into an exact finite support-moment world. Every sqrt-rough candidate has

    activeSupport.card <= 3,

and the following factorization results are already production theorems:

- three supported labels p<q<s imply

      n^2+r = p*q*s;

- exactly two supported labels p<q imply

      n^2+r = p^2*q  or  n^2+r = p*q^2;

- every prime divisor of a sqrt-rough point is >sqrt n, including prime factors
  above the active-prime universe.

The exact moment identities are also complete:

    U + roughI + M3 = R + M2,
    tail + M3 = M2.

The remaining structurally unclassified covered rough seats are exactly the
support-cardinality-one seats.

The purpose of this task is to classify them arithmetically and then turn the
entire sqrt-rough carrier into a disjoint factorization census.

Do not introduce another coverage, excess, or moment ledger.

## Primary conjectural classification to test

Let r be a sqrt-rough candidate with

    paritySafeActiveSupport n r = {p}.

Since p is an actual active label,

    sqrt n < p <= n.

Test and prove if correct:

    n^2+r = p^3

or

    exists q, q.Prime and n<q and n^2+r = p*q.

The second factor q is deliberately outside the active-prime universe.

This classification is a target, not an assumption.

If false, preserve the smallest kernel counterexample and derive the corrected
cofactor classification.

## Required source audit

Audit at minimum:

    DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughFactorization
    DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughMoments
    DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughProductWaves
    DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootTail
    DkMath.NumberTheory.Legendre.ParitySafeCanonicalRoughCount
    DkMath.NumberTheory.Legendre.ParitySafePrimeAnchorCap
    DkMath.NumberTheory.Legendre.ParitySafeReducedResidue
    DkMath.NumberTheory.Legendre.PairOverlap

and relevant Mathlib APIs for:

- prime divisors / `Nat.minFac`;
- unique factorization of natural numbers;
- prime powers and divisibility;
- Finset fiber/cardinality bijections.

Record exact theorem names before adding new helper lemmas.

## Phase 1 — support-cardinality strata

Define only the minimal useful existing-carrier filters:

    roughZeroSeats n   := sqrt-rough seats with support.card=0,
    roughSingletonSeats n := sqrt-rough seats with support.card=1,
    roughDoubleSeats n := sqrt-rough seats with support.card=2,
    roughTripleSeats n := sqrt-rough seats with support.card=3.

`roughZeroSeats` should immediately identify with the existing
`paritySafeUncoveredCandidates` via `rough_empty_eq_uncovered`.

Prove the four strata are pairwise disjoint and partition

    canonicalRoughCandidates n (Nat.sqrt n).

Prefer filtered Finsets and existing card<=3 rather than a new datatype.

## Phase 2 — exact stratum cardinal algebra

Let N0,N1,N2,N3 denote the four stratum cards.

Prove exact identities:

    R = N0+N1+N2+N3,
    roughI = N1+2*N2+3*N3,
    M2 = N2+3*N3,
    M3 = N3.

Then prove the report-013 proposed identity:

    roughCovered.card + 2*M3 = N1 + M2.

Also expose the exact uncovered criterion:

    N0>0
      iff
    N1 + M2 < R + 2*M3.

Use Nat-safe additive equalities; do not introduce premature subtraction.

## Phase 3 — singleton support label extraction

For r in `roughSingletonSeats n`, extract the unique supported active prime p.

Provide a reusable packet:

    p.Prime,
    sqrt n < p,
    p <= n,
    p divides n^2+r,
    activeSupport n r = {p}.

Use Finset card-one APIs rather than a choice axiom beyond the project's normal
classical finite-set usage.

## Phase 4 — singleton cofactor theorem

Write

    n^2+r = p*c.

Use the already proved theorem

    sqrt_rough_prime_divisor_gt

to control every prime divisor of c.

Prove the strongest correct elementary classification of c.

The preferred route is:

1. If c is prime, then c cannot be <=n unless c=p.
2. The case c=p gives p^2, which lies at or below n^2 and cannot be in the
   open square shell.
3. Therefore a prime cofactor must satisfy c>n, yielding the cross-semiprime
   point p*c.
4. If c is composite, use its least prime divisor u.
5. If u>n, then c has at least two prime factors >n, making p*c too large.
6. Hence u<=n, so u is an active support label; singleton support forces u=p.
7. Divide once more and show only one additional p can remain. The p^2 point
   is below the shell, while p^4 exceeds the shell by the existing fourth-power
   threshold.

Target theorem:

    support={p}
      -> point=p^3 or exists q, q.Prime and n<q and point=p*q.

Do not force this exact proof route if Mathlib offers a cleaner factorization
argument.

## Phase 5 — disjointness of singleton types

Prove the cube type and cross-semiprime type cannot overlap.

For cross-semiprime representation, prove uniqueness:

    p*q = p'*q'

with

    p,p' active sqrt-rough labels <=n,
    q,q' prime >n,

implies

    p=p' and q=q'.

Use prime divisibility / size separation, not numerical factorization.

## Phase 6 — converse for singleton cube seats

Define a finite cube-key carrier from actual rough active labels p satisfying

    n^2 < p^3 <= n^2+2n.

Prove that the offset

    r = p^3 - n^2

is an actual sqrt-rough candidate and has support exactly `{p}`.

Required checks:

- shell offset range;
- oddness and Coprime(2n, point);
- p is active and >sqrt n;
- no other active support prime divides p^3.

Then prove a bijection between cube keys and cube-type singleton seats.

## Phase 7 — cube occupancy bound

Prove an elementary global bound on cube keys.

Preferred target:

    cubeKeys(n).card <= 1.

Suggested argument:

for p>sqrt n, consecutive cubes satisfy

    (p+1)^3 - p^3 > 2*n,

so two distinct prime cubes cannot both lie in one shell of width 2n.

Handle small n explicitly if required.

Do not use real cube roots or analytic estimates.

## Phase 8 — converse for cross-semiprime singleton seats

Define an explicit finite key carrier for pairs (p,q) with

    p in actual active primes,
    sqrt n < p <= n,
    q.Prime,
    n < q,
    n^2 < p*q <= n^2+2n.

Use a finite q range justified from the shell endpoint, for example

    n < q <= n^2+2n.

Prove that

    r = p*q - n^2

is a sqrt-rough candidate with support exactly `{p}`.

Then prove a bijection between these keys and cross-semiprime singleton seats.

Do not assume q belongs to `squareAnchorOddActivePrimes n`; it does not because
q>n.

## Phase 9 — exact singleton census

Let

    CubeCount(n)  = cube keys in the shell,
    CrossCount(n) = eligible p*q keys with p<=n<q.

Prove the exact cardinal identity:

    roughSingletonSeats.card = CubeCount + CrossCount.

This is the first main factorization census theorem.

If public numerical definitions are unnecessary, express it directly as cards
of the finite key carriers.

## Phase 10 — exact two-support repeated-product carrier

Instruction 013 proved the forward classification

    support={p,q}
      -> point=p^2*q or p*q^2.

Now implement the converse.

Use a key

    (p,q,side)

where p<q are actual rough active labels and `side` records which prime repeats.

Filter by the shell inequalities for

    p^2*q

or

    p*q^2.

Prove each eligible key gives an actual sqrt-rough candidate whose support is
exactly `{p,q}`.

Prove key-to-seat injectivity using prime divisibility / unique factorization.

Then obtain an exact bijection and cardinal count for `roughDoubleSeats`.

Preserve a counterexample if two syntactically different keys can hit the same
seat under a poorly chosen side encoding; repair the encoding rather than
quotienting after the fact.

## Phase 11 — exact three-support seat bijection

Instruction 013 already proved:

    M3 = sqrtRoughTripleProductsInShell.card

and each eligible triple wave is the unique product seat.

Complete the seat-level bijection:

    roughTripleSeats
      <->
    sqrtRoughTripleProductsInShell.

Then prove directly:

    roughTripleSeats.card = M3.

This should agree with the local cardinal stratum identity from Phase2.

## Phase 12 — complete sqrt-rough factorization census

Combine Phases9–11 with the zero class.

Prove an exhaustive disjoint classification for every sqrt-rough candidate
point:

    support.card=0:
      uncovered / prime square-cell point;

    support.card=1:
      p^3 or p*q with p<=n<q prime;

    support.card=2:
      p^2*q or p*q^2;

    support.card=3:
      p*q*s with p<q<s;

with all p,q,s that are active support labels satisfying >sqrt n and <=n.

Prefer one theorem returning the appropriate disjunction from an arbitrary
rough candidate, plus separate uniqueness/cardinality theorems.

Do not redefine primality of the zero-support case; reuse the existing
uncovered-to-square-cell-prime consumer where possible.

## Phase 13 — moment formulas in product-count normal form

Using the exact stratum/product bijections, rewrite:

    M3 = TripleProductCount,

    M2 = DoubleProductCount + 3*TripleProductCount,

    roughI = SingletonCount + 2*DoubleProductCount + 3*TripleProductCount,

    roughCovered = SingletonCount + DoubleProductCount + TripleProductCount.

Then the moment criterion should reduce exactly to:

    SingletonCount + DoubleProductCount + TripleProductCount < R

or an equivalent additive form whose margin is U.card.

Keep each product type visible; do not simplify away the arithmetic information
that later providers will need.

## Phase 14 — semiprime quotient-fiber form

For a fixed rough active p, characterize cross-semiprime singleton keys by q:

    q.Prime,
    n<q,
    n^2/p < q <= (n^2+2n)/p,

with exact endpoint handling avoiding rational arithmetic.

Prove an exact finite fiber/cardinality expression for the p-owned cross count.

Regroup:

    CrossCount = sum over rough active p of CrossFiber(n,p).card.

This is intended to expose the true remaining arithmetic obligation.

Do not apply PNT, Bertrand, Brun, Selberg, or analytic prime-counting estimates.

## Phase 15 — structural bounds available without prime counting

Extract all elementary bounds that follow merely from the shell geometry.

At minimum investigate:

- cube count <=1;
- for fixed p, cross q-values lie in an interval of length controlled by 2n/p;
- parity spacing between distinct odd q values;
- repeated-product keys have one-seat occupancy by product uniqueness;
- triple-product keys have one-seat occupancy from Instruction013.

If a clean uniform cardinal upper bound on CrossFiber(n,p) follows, formalize it.

Do not overstate a bound that still scales too poorly when summed over p.

## Phase 16 — calibration

Kernel-check the full census at:

    n=211,503,1009,1013,1019.

Also choose at least one prime anchor >1019 if runtime permits.

For each report:

    R, U, N1, N2, N3,
    CubeCount, CrossCount,
    RepeatedProductCount, TripleProductCount.

Check:

    N1 = CubeCount+CrossCount,
    N2 = RepeatedProductCount,
    N3 = TripleProductCount,

and recover U from the complete census.

Structural endpoint proofs must not depend on direct whole-E/I evaluation.

## Phase 17 — bounded discovery for the singleton bottleneck

Run a bounded finite diagnostic over prime anchors in a justified range.

Measure:

- singleton fraction N1/R;
- cube contribution versus cross-semiprime contribution;
- which p fibers dominate CrossCount;
- maximum CrossFiber(n,p).card;
- whether repeated/triple composite types become negligible or remain material.

Preserve the full diagnostic output, but kernel-check only selected calibration
anchors and any smallest structural counterexamples.

Do not infer asymptotics from the finite scan.

## Phase 18 — isolate the next uniform theorem

After the census, state one exact theorem contract that would imply an uncovered
sqrt-rough seat.

Preferred form:

    CubeCount(n) + CrossCount(n)
      + RepeatedProductCount(n) + TripleProductCount(n)
      < canonicalRoughCandidates(n,sqrt n).card.

Since CubeCount should be <=1 and the other two multi-support counts now have
exact product carriers, identify whether the true remaining obstruction is the
cross-semiprime sum.

If so, state the next contract explicitly as a bound on

    sum_p CrossFiber(n,p).card.

Do not hide that obligation behind a generic 'singleton estimate'.

## Optional Phase 19 — relation to quotient/wave arithmetic

Only if natural after Phase14, connect CrossFiber(n,p) to the existing
active-wave quotient representation.

The quotient is now a prime q>n rather than a reduced active label.

Prove an exact map before reusing any old quotient capacity theorem.

Do not identify this with `canonicalRoughWave` secondary labels: those q are
active <=n, while the cross cofactor here is deliberately >n.

## Possible outcomes

### Outcome A — complete sqrt-rough factorization census

Singleton support is classified as cube/cross-semiprime, N1/N2/N3 all receive
exact product carriers, and the remaining uniform obstruction is reduced to an
explicit cross-semiprime fiber inequality.

### Outcome B — multi-support census complete, singleton classification partial

N2/N3 product bijections and stratum algebra are complete, but singleton
cofactors admit an additional arithmetic type or the converse product carrier
remains incomplete.

### Outcome P — one precise singleton-cofactor bridge remains

The support strata and forward singleton classification are complete, but one
exact converse/uniqueness theorem blocks the cardinal census.

### Outcome C — proposed singleton classification is false

A genuine additional singleton factorization type occurs. Preserve the smallest
counterexample and replace the proposed census with the correct one.

## Non-goals

Do not claim:

    Legendre's conjecture;
    uniform T=1;
    PNT/RH;
    analytic sieve estimates;
    asymptotic semiprime estimates;
    FLT/ABC consequences.

Do not prove calibration endpoints by evaluating whole E or whole I.

Do not introduce an alternate support universe or alternate uncovered notion.

Do not use sorryAx-bearing endpoints in production.

## Implementation guidance

A focused module split is reasonable, for example:

    DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughStrata.lean
    DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughSingleton.lean
    DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughCensus.lean.

Extend `ParitySafeSqrtRoughFactorization` where the theorem is genuinely a
factorization lemma rather than a carrier/cardinality theorem.

Keep neutral finite-set bijection lemmas outside the Legendre namespace when
appropriate.

## Validation

For all new production declarations:

- focused builds;
- lake build DkMath.NumberTheory.Legendre;
- lake build DkMath;
- forbidden-token scan;
- #print axioms for every new public declaration;
- git diff --check.

All new production declarations must remain free of sorryAx.

Keep the existing project convention for file headers and the import-adjacent

    #print "file: ..."

marker on every modified/new Lean file.

## Durable checkpoint protocol

Update findings after:

- support strata partition;
- singleton label packet;
- singleton cofactor classification;
- cube converse/bijection;
- cross-semiprime converse/bijection;
- repeated-product converse/bijection;
- triple-seat bijection;
- complete census theorem;
- per-p CrossFiber regrouping;
- bounded singleton diagnostics;
- final A/B/P/C judgment.

Preserve every failed singleton classification and smallest counterexample.

## Final report

Answer explicitly:

1. What exact support-cardinality stratification was proved?
2. Is every singleton-support rough point exactly p^3 or p*q with p<=n<q prime?
3. Are cube and cross-semiprime representations unique and disjoint?
4. Is CubeCount<=1 proved uniformly?
5. Is roughSingletonSeats.card exactly CubeCount+CrossCount?
6. Is roughDoubleSeats exactly counted by p^2*q / p*q^2 product keys?
7. Is roughTripleSeats exactly counted by distinct p*q*s shell products?
8. What complete factorization census theorem was obtained?
9. What exact per-p quotient/fiber formula describes CrossCount?
10. After the census, what is the smallest explicit uniform inequality still missing?

End with exactly one judgment:

    Outcome A — COMPLETE SQRT-ROUGH FACTORIZATION CENSUS
    Outcome B — MULTI-SUPPORT CENSUS COMPLETE, SINGLETON PARTIAL
    Outcome P — PRECISE SINGLETON-COFACTOR BRIDGE REMAINS
    Outcome C — PROPOSED SINGLETON CLASSIFICATION IS FALSE