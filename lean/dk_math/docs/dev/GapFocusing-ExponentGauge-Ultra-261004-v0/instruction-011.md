# Instruction 011 — Legendre canonical rooted-pair fibers / minimum-prime sieve

## Mission

Continue from Instruction 010.

Instruction 010 showed that fixed finite CRT witness pools are useful but do not
scale uniformly with the required charge. In particular, the tested fixed bases
miss demand at 211 and 503.

Before introducing more certificate families, audit the exact support-excess
structure already present in the mature Legendre stack.

The key existing fact is:

    card(paritySafeCanonicalQuotientCoSupportIncidences n)
      = paritySafeSupportExcess n.

Each incidence (r,q) has a recoverable canonical first support prime

    p = paritySafeCanonicalSupportPrime n r,

and the existing packet proves

    p != q,
    p*q | n^2+r,
    p,q active,
    Coprime (2*n) (p*q).

Therefore support excess already has an exact canonical rooted-pair interpretation.

The purpose of this task is not to create a duplicate rooted-pair ledger.

It is to:

1. reindex the exact existing incidence set by its canonical root p;
2. characterize the p-root fiber by product-wave divisibility plus exclusion of
   smaller active primes;
3. obtain structural lower bounds on those fibers;
4. test whether the first few roots p=3,5,7 already meet the hard demand at
   211 and 503.

## Required source audit

Audit at minimum:

    DkMath.NumberTheory.Legendre.ParitySafeSupportExcessQuotient
    DkMath.NumberTheory.Legendre.ParitySafePairResidual
    DkMath.NumberTheory.Legendre.PairOverlap
    DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveRoughCofactor
    DkMath.NumberTheory.Legendre.ParitySafeCRTSeat
    DkMath.NumberTheory.Legendre.ParitySafeMergedCRT
    DkMath.NumberTheory.Legendre.ParitySafeIncidenceUpper
    DkMath.NumberTheory.Legendre.ParitySafeReducedResidue

and any existing first-prime fiber / product-wave counting modules already
exported by DkMath.NumberTheory.Legendre.

Do not reprove:

    paritySafeCanonicalQuotientCoSupportIncidences_card_eq_supportExcess

or introduce a second exact excess object unless a reindexing definition is
strictly useful.

## Phase 1 — canonical root is actually the minimum

For a canonical quotient co-support incidence (r,q), prove or recover the
strong ordering statement

    paritySafeCanonicalSupportPrime n r < q.

The existing packet currently exposes only inequality by distinctness.

Use the fact that the canonical prime is min' of actual support.

This ordering is important because the rooted pair should be represented
canonically as p<q.

## Phase 2 — root-fiber reindexing

Define, only if useful, the finite fiber

    canonicalRootFiber n p

consisting of canonical quotient co-support incidences whose canonical support
prime equals p.

Prove an exact decomposition:

    E(n)
      = sum_{p in active primes} card(canonicalRootFiber n p).

or an equivalent Finset card partition theorem.

Prefer reindexing/filtering the existing exact incidence set over reconstructing
it from scratch.

Also provide the finer pair fiber if useful:

    canonicalRootPairFiber n p q

with

    E(n)
      = sum_{p} sum_{q>p} card(canonicalRootPairFiber n p q).

Do not force a public definition if a local theorem gives the same reusable API.

## Phase 3 — exact root criterion via smaller-prime exclusion

For an actual candidate seat r with active p and q and p<q, characterize

    paritySafeCanonicalSupportPrime n r = p

as:

    p belongs to activeSupport(n,r),
    and no active prime a<p belongs to activeSupport(n,r).

Then rewrite the smaller-prime condition using divisibility of n^2+r.

Desired shell-point form:

    p is canonical at r
      iff p divides n^2+r
          and every active a<p does not divide n^2+r,

under the candidate/active hypotheses.

This is the pair-level analogue of the existing far-product rough-cofactor
canonical-minimum rewrite.

Reuse that methodology where possible.

## Phase 4 — pair fiber as a product wave with exclusions

For active p<q, characterize the canonical rooted-pair seat fiber as:

    candidate r,
    p*q divides n^2+r,
    and no active prime a<p divides n^2+r.

Connect the unfiltered p*q divisibility seats to existing product-wave APIs:

    squarePrimePairOverlapOffsets
    squareWaveOffsets
    card_squareWaveOffsets_eq_div_add_carry

or the strongest parity-safe version already present.

Then express the canonical p-root q-fiber as an exact filtered product wave.

## Phase 5 — prime-anchor simplification

Specialize to prime anchors n>7.

Then 3,5,7 are active and candidate coprimality is particularly simple.

For p=3:

    there is no smaller odd active prime.

So prove the clean exact/structural description:

    root-3 pair fiber for q
      = candidate seats with 3*q | n^2+r,

for active q>3.

For p=5:

    root-5 pair fiber for q
      = seats with 5*q | n^2+r and 3 does not divide n^2+r.

For p=7:

    root-7 pair fiber for q
      = seats with 7*q | n^2+r
        and 3 does not divide n^2+r
        and 5 does not divide n^2+r.

State only the exact hypotheses needed.

## Phase 6 — finite exclusion counting

Build Nat-safe finite counting lemmas for one product-wave fiber minus smaller-root
contamination.

For p=5, target a lower bound of the shape:

    card(wave(5*q)) - card(wave(3*5*q))
      <= card(root5PairFiber(q)).

with candidate/parity corrections included honestly.

For p=7, use two-exclusion inclusion-exclusion:

    card(wave(7*q))
      - card(wave(3*7*q))
      - card(wave(5*7*q))
      + card(wave(3*5*7*q))
      <= card(root7PairFiber(q)),

again in a Nat-safe formulation.

An exact equality is welcome only if all candidate/reduced conditions are
actually accounted for.

Do not silently replace parity-safe candidate fibers by raw square-wave counts.

## Phase 7 — sum over secondary q

For each root p in {3,5,7}, sum the proved pair-fiber lower bounds over
secondary active primes q>p.

Obtain production lower bounds:

    RootCharge3(n) <= E(n),
    RootCharge3(n)+RootCharge5(n) <= E(n),
    RootCharge3(n)+RootCharge5(n)+RootCharge7(n) <= E(n),

where the RootCharge names are conceptual; production definitions are optional.

Different canonical roots are disjoint by construction, so no merged-seat
double-counting problem should remain.

## Phase 8 — hard checkpoints 211 and 503

Mandatory diagnostics:

    n=211,
    n=503.

Compute and kernel-check, using the new structural root-fiber bounds and not
whole-shell support-excess evaluation:

    A(n),
    B2(n),
    D(n)=B2-A+1,
    root-3 lower charge,
    root-3+5 lower charge,
    root-3+5+7 lower charge.

Primary tests:

    Does root3+root5 meet D(211)?
    Does root3+root5+root7 meet D(503)?

If yes, derive:

    uncoveredCandidates(n).Nonempty

and the corresponding square-cell prime theorem.

Do not use direct evaluation of E(n) or I(n) as a substitute for the new
structural lower bound.

## Phase 9 — compare with actual canonical-root diagnostics

For diagnostics only, finite evaluation may compute the actual canonical-root
contributions to E at selected anchors.

Compare structural lower bounds with actual root contributions.

Required checkpoints:

    127,211,503.

Record how much loss comes from:

- parity/candidate filtering;
- smaller-prime exclusion overestimation;
- long-period carry terms;
- secondary-q truncation;
- crude Nat subtraction.

These diagnostics must not enter production proofs except through explicit
proved finite equalities.

## Phase 10 — canonical star vs forest interpretation

Audit the relation between:

1. existing exact canonical star incidences;
2. Instruction010 merged CRT witness unions;
3. a fixed rooted-star collection of pair families;
4. a general forest of supported prime-pair edges.

Prove at least the rooted-star combinatorial statement if not already implied
cleanly by merged witness union:

    if a fixed root p and distinct secondary labels q are all supported at a
    seat, then the number of realized star edges is <= local support excess.

If a generic finite forest theorem is easy and does not import a heavy graph
stack, it may be added.

Do not introduce graph abstraction merely for terminology.

## Phase 11 — adaptive root hierarchy

If roots 3,5,7 succeed on 211/503, extend the construction conceptually to

    p = next active prime,

where canonical ownership requires excluding all smaller active primes.

Formulate a generic finite-root theorem:

    canonical p-root pair fiber
      = p*q product-wave hits surviving the finite smaller-active-prime sieve.

The smaller-prime set should be

    {a in activePrimes(n) | a<p}.

Then expose a reusable finite inclusion-exclusion or subset-exclusion lower
bound when practical.

Do not attempt a full symbolic inclusion-exclusion over arbitrarily many primes
unless Mathlib support makes it clean.

## Phase 12 — scaling audit

Compare the cumulative structural rooted charge with demand on prime anchors:

    47,97,127,211,503

and, if runtime permits, a few larger primes.

Report the smallest root cutoff P such that roots <=P meet demand in each
checked case.

The research question is now:

> Does allowing more canonical roots close demand in a controlled way, even
> when a fixed CRT witness basis fails?

Do not infer an asymptotic theorem from finite data.

## Phase 13 — exact next uniform theorem

If the finite rooted hierarchy succeeds strongly, state the exact missing
uniform theorem.

A likely form is:

    for every prime anchor n, the cumulative canonical-root lower bound up to
    a controlled root cutoff P(n) is at least B2(n)-A(n)+1.

If this is still false or quantitatively weak, identify whether the missing
step is:

- a better lower estimate for surviving product-wave hits;
- a better bound on smaller-prime contamination;
- a better incidence upper bound;
- or a fundamentally different provider.

## Possible outcomes

### Outcome A — canonical root sieve breaks the fixed-basis barrier

The exact existing canonical-star ledger is successfully fibered by root,
211 and503 are solved structurally without direct E/I evaluation, and the
root hierarchy gives a stronger scaling route than fixed-basis CRT.

### Outcome B — exact root fibers work, but scaling remains limited

The canonical-root decomposition and sieve bounds are formalized and solve at
least one hard checkpoint, but cumulative lower charge still misses larger
demand.

### Outcome P — one exact root-fiber counting bridge remains

The exact root decomposition and minimum-prime criterion are complete, but one
precise parity-safe product-wave exclusion count blocks the quantitative result.

### Outcome C — rooted-pair reformulation adds no quantitative leverage

The exact decomposition is mostly a reindexing of existing data and the
available lower bounds are too weak to improve on merged CRT certificates.

Identify the next currency/provider.

## Non-goals

Do not claim:

    Legendre's conjecture;
    uniform T=1;
    PNT/RH;
    analytic sieve estimates;
    FLT/ABC consequences.

Do not duplicate existing exact support-excess or pair-overlap ledgers.

Do not use direct whole-shell E/I evaluation as the proof of 211/503.

Do not use sorryAx-bearing endpoints in production.

## Implementation guidance

Prefer extending/reusing:

    DkMath.NumberTheory.Legendre.ParitySafeSupportExcessQuotient
    DkMath.NumberTheory.Legendre.PairOverlap

or add a focused reusable module such as

    DkMath/NumberTheory/Legendre/ParitySafeCanonicalRootFiber.lean

only if the root-fiber API is substantial.

Keep finite inclusion-exclusion helpers in a neutral namespace where sensible.

## Validation

For all new production declarations:

- focused builds;
- lake build DkMath.NumberTheory.Legendre;
- lake build DkMath;
- forbidden-token scan;
- #print axioms for every new public declaration;
- git diff --check.

All new production declarations must remain free of sorryAx.

## Durable checkpoint protocol

Update findings after:

- canonical p<q ordering;
- exact root-fiber partition;
- smaller-active-prime canonical criterion;
- p=3 exact fiber;
- p=5 one-exclusion count;
- p=7 two-exclusion count;
- 211 test;
- 503 test;
- root-hierarchy scaling table;
- final A/B/P/C judgment.

Preserve false exact-equality candidates and smallest counterexamples.

## Final report

Answer explicitly:

1. Was a new exact rooted-pair ledger needed, or was the existing canonical
   quotient incidence already exactly E?
2. What exact root-fiber decomposition was proved?
3. Is canonical root p equivalent to excluding all smaller active prime
   divisors at the seat?
4. What exact/inequality formulas were proved for root3, root5 and root7?
5. What structural lower charges are obtained at211 and503?
6. Are211 and503 proved to contain square-cell primes without direct E/I
   evaluation?
7. How close are the structural root bounds to the actual finite canonical-root
   contributions?
8. Does the rooted-star/forest interpretation improve the demand-scaling story
   over fixed-basis CRT?
9. What root cutoff is needed at the tested prime checkpoints?
10. What exact uniform theorem remains?

End with exactly one judgment:

    Outcome A — CANONICAL ROOT SIEVE BREAKS FIXED-BASIS BARRIER
    Outcome B — ROOT FIBERS WORK, SCALING LIMITED
    Outcome P — PRECISE ROOT-FIBER COUNTING BRIDGE REMAINS
    Outcome C — ROOTED-PAIR REFORMULATION ADDS NO LEVERAGE