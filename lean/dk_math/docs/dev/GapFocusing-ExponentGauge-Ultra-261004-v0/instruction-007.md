# Instruction 007 — Legendre uncovered-deficit / incidence-upper-bound frontier

## Mission

Continue from Instruction 006.

Instruction 006 identified the quantity that survives the current cancellation:

    I + U = A + E

where

- I = paritySafeIncidenceCount
- U = paritySafeUncoveredCandidates.card
- A = squareAnchorOddPointCoprimeOffsets.card
- E = paritySafeSupportExcess.

The new support-excess lower bound from Instructions 004–005 is real, but after the strongest existing cancellation it does not produce a new obstruction by itself.

The quantity that does not disappear is the uncovered-candidate deficit U.

The next target is therefore:

> Produce a full-cover-independent upper bound on incidence count strong enough to force U > 0.

The long-term strategy is to shrink the width of a finite block contradiction:

    T = 20 -> smaller T -> ... -> T = 1.

At T=1, a uniform contradiction would be Legendre's conjecture itself.

Do not assume that this task reaches T=1.

## Starting exact identities

Reuse the current production facts:

    paritySafeIncidenceCount_eq_candidate_support_sum
    paritySafeIncidenceCount_eq_reducedQuotientInterval_sum
    paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence
    paritySafeCoveredCandidates_card_add_uncoveredCandidates_card_eq_candidate_card
    paritySafeIncidenceConservation

In particular:

    I + U = A + E.

Also reuse the generic block consumers from Instruction 006:

    incidence upper bound < candidate demand + mandatory temporal excess
      -> not simultaneous full cover.

Do not create a second incidence ledger.

## Required source audit

Audit at minimum:

    DkMath.NumberTheory.Legendre.ParitySafeIncidenceBalance
    DkMath.NumberTheory.Legendre.ParitySafeReducedResidue
    DkMath.NumberTheory.Legendre.ParitySafeMobiusOddCorrection
    DkMath.NumberTheory.Legendre.ParitySafeWavePruning
    DkMath.NumberTheory.Legendre.ParitySafePersistence
    DkMath.NumberTheory.Legendre.ParitySafePersistenceParity
    DkMath.NumberTheory.Legendre.ParitySafeFreshCost
    DkMath.NumberTheory.Legendre.ParitySafeBlockLocalization
    DkMath.NumberTheory.Legendre.ParitySafeFullCoverCapacityFrontier
    DkMath.NumberTheory.Legendre.ParitySafeActualFiberCancellation
    DkMath.NumberTheory.Legendre.ParitySafeUnusedResidualPairRouting

Record exact existing theorem names before adding code.

## Phase 1 — choose the correct incidence representation

There are two exact views.

Candidate-side:

    I_n =
      sum over candidate seats r of
        (paritySafeActiveSupport n r).card.

Prime/wave-side:

    I_n =
      sum over active primes q of
        (paritySafeReducedQuotientInterval n q).card.

Determine which side exposes the strongest upper bound without a full-cover hypothesis.

Do not choose one in advance.

If useful, derive a theorem that allows switching representations locally in a block argument.

## Phase 2 — per-prime wave cardinal upper bounds

For an active prime q at shell n, study

    paritySafeReducedQuotientInterval n q.

Its members k satisfy

    n^2 < q*k <= n^2 + 2*n
    and
    Coprime (2*n) k.

The raw interval length is about 2*n/q, while parity/reduced-residue conditions remove candidates.

Find the strongest exact or elementary upper bound currently available.

Candidate targets include:

    card <= ceil(2*n/q)

or the exact natural-number interval-card analogue.

Then improve it using already-formalized constraints:

- odd quotient spacing;
- same-wave quotient rigidity;
- quotient differences are even;
- reduced residue condition;
- any Möbius/odd correction already present in production.

A useful result must be full-cover independent.

## Phase 3 — exploit same-wave 2q rigidity

Existing production proves that distinct seats in one active q-wave satisfy

    2*q | (s-r).

This is stronger than merely q | (s-r).

Use it to bound the cardinality of one wave directly inside the square-offset window.

Test the clean finite packing theorem:

    activeWaveOffsets.card <= ceil((2*n)/(2*q))

or the correct endpoint-sensitive form.

Compare this with the quotient-interval bound and retain the sharper one.

Do not infer exact adjacency; only the divisibility/spacing theorem is checked.

## Phase 4 — sum over active primes

Convert the best per-q upper bound into

    paritySafeIncidenceCount n
      <= sum_{q in active primes} waveCap(n,q).

Then simplify the RHS using the actual active-prime conditions:

    q prime
    q <= n
    q != 2
    q does not divide n.

Possible normalizations:

- primeScalesUpTo n with exclusions;
- squareAnchorOddActivePrimes n directly;
- grouped by quotient capacity classes.

Avoid replacing the finite prime sum by an analytic prime-counting bound unless one already exists in the repository and is fully proved.

This phase should remain elementary/finite if possible.

## Phase 5 — seat-side dual upper bound

Independently audit whether the candidate-side support cardinal can be bounded using the Instruction 004–005 seat arithmetic.

Persistent support obeys:

    persistent q at seat r -> q | 4*r+1.

Fresh support does not obey that constraint.

However, the active support itself satisfies q | n^2+r with q<=n, q not dividing n, q odd.

Investigate whether factorization of the point n^2+r yields a finite support-card upper bound stronger than the current generic incidence count.

Possible target:

    activeSupport.card
      <= number of distinct admissible prime factors of n^2+r.

This is tautologically true at one level, so it is useful only if the admissible factor count can be bounded uniformly or by a sharper seat-specific arithmetic quantity.

Compare prime-side and seat-side approaches honestly.

## Phase 6 — block incidence upper bound

For a block [N,N+T), sum the shellwise incidence upper bound:

    sum_{i<T} I_{N+i}
      <= IncidenceUpper(N,T).

The theorem must not assume simultaneous full cover.

Combine it with the already-checked mandatory temporal excess lower bound:

    simultaneous full cover
      -> sum I >= sum A + b(N,T).

Therefore a generic contradiction criterion is:

    IncidenceUpper(N,T) < sum A + b(N,T)
      -> not simultaneous full cover.

Reuse the existing generic consumer from Instruction 006 if possible.

## Phase 7 — reproduce the main block without exact table lookup

The 20-shell block N=20,T=20 is known to fail full cover.

But Instruction 006 used exact finite values such as

    sum I = 418
    sum A = 490.

This task should determine whether a structural incidence upper theorem, rather than exact brute-force evaluation of I, is strong enough to prove the same failure.

Main diagnostic:

    IncidenceUpper(20,20)
      < 490 + b(20,20).

Record the numerical slack.

If the structural bound is too weak, identify exactly which q-waves create the slack.

## Phase 8 — shrink block width

Search finite blocks with decreasing T.

Do not blindly scan huge ranges.

Use the new generic incidence upper bound to test a disciplined sequence such as:

    T = 20, 10, 5, 4, 3, 2, 1

with representative N, and then determine whether the theorem suggests a uniform-in-N result for any fixed T.

The hierarchy of possible achievements is:

1. some explicit block failure;
2. a smaller explicit block failure than 20;
3. every block of width T contains a failure;
4. T=2 uniform;
5. T=1 uniform.

Only level 5 is Legendre.

## Phase 9 — direct uncovered-candidate lower bound

Instead of going through contradiction, use

    U = A + E - I

in natural-number-safe form.

If an upper bound I<=B and lower bound E>=e are available, derive

    U >= A + e - B

with the correct Nat subtraction formulation.

This gives a direct quantitative lower bound on uncovered candidates.

A theorem of the form

    0 < A + e - B
      -> (paritySafeUncoveredCandidates n).Nonempty

or its block analogue is preferable when it cleanly feeds the existing prime consumer.

Do not use integer subtraction unless it materially simplifies a theorem and the coercion boundary is explicit.

## Phase 10 — prime-existence consumers

Whenever U>0 is obtained for one shell, reuse:

    exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty

and the existing SquareCell interval theorem.

For a block theorem, extract an explicit shell witness.

Do not state a prime-existence theorem stronger than the uncovered-candidate statement actually supports.

## Phase 11 — diagnose the remaining obstruction

If the incidence bound does not approach the required threshold, classify the slack by exact production objects.

Likely possibilities:

- a small set of low q waves dominate incidence;
- reduced quotient intervals are too crudely bounded;
- duplicate wave hits need stronger cancellation;
- Möbius/reduced-residue correction is not being used sharply enough;
- temporal information has not been applied to incidence, only persistence.

Give one precise next theorem target.

## Possible outcomes

### Outcome A — block width shrinks

A structural, full-cover-independent incidence upper bound proves a simultaneous cover failure for a strictly smaller block than the previous width 20.

Record the smallest proved width and exact assumptions.

### Outcome B — main block structurally recovered

The new upper bound proves the 20-shell failure without exact incidence evaluation, but no smaller block is yet forced.

This is still a genuine reusable frontier improvement.

### Outcome P — precise incidence-bound bridge remains

The exact decomposition identifies one missing finite packing or reduced-residue inequality whose proof would make the structural bound strong enough.

Use Outcome P only for a sharply stated theorem.

### Outcome C — current incidence upper route is too weak

The best elementary upper bound is far above the required threshold.

Identify the dominant slack and recommend a different currency/provider.

## Non-goals

Do not claim or attempt by default:

    Legendre's conjecture;
    analytic estimates for pi(x);
    PNT or RH machinery;
    unproved asymptotics;
    FLT / ABC consequences;
    a replacement for the mature parity-safe ledger.

Do not use research endpoints carrying sorryAx in production proofs.

Do not prove a finite case only by replacing the new upper theorem with exact decidable evaluation of the incidence count; exact computations are diagnostics and regressions, not the structural result.

## Implementation guidance

If a new production module is justified, prefer:

    DkMath/NumberTheory/Legendre/ParitySafeIncidenceUpper.lean

or another name matching the exact mathematics.

Keep reusable finite packing lemmas in a neutral namespace when appropriate.

Public theorem names should refer to incidence, wave, quotient interval, spacing, or uncovered candidates rather than speculative terms.

## Validation

For all new production declarations:

- focused builds for changed/new modules;
- lake build DkMath.NumberTheory.Legendre;
- lake build DkMath;
- forbidden-token scan;
- #print axioms for all new public declarations;
- git diff --check.

New production results must be free of sorryAx.

## Durable checkpoint protocol

Update findings after:

- incidence representation audit;
- first per-q wave upper bound;
- use of 2q spacing;
- reduced-residue/Möbius sharpening;
- shell incidence upper theorem;
- block incidence upper theorem;
- N=20,T=20 structural test;
- smallest successful block width;
- uncovered-deficit lower bound;
- final A/B/P/C decision.

Preserve failed upper-bound candidates and exact counterexamples.

## Final report

Answer explicitly:

1. What is the strongest full-cover-independent upper bound on one q-wave?
2. Does 2q spacing improve the quotient-interval bound?
3. What is the resulting shell incidence upper bound?
4. What is the resulting block incidence upper bound?
5. Can the N=20,T=20 cover failure be recovered structurally without exact I=418?
6. What is the smallest block width proved to contain a cover failure?
7. Does the method yield a positive lower bound on uncovered candidates?
8. Which q-waves or residue classes dominate the remaining slack?
9. How far is the current theorem from the T=1 Legendre target?

End with exactly one judgment:

    Outcome A — BLOCK WIDTH SHRINKS
    Outcome B — MAIN BLOCK STRUCTURALLY RECOVERED
    Outcome P — PRECISE INCIDENCE-BOUND BRIDGE REMAINS
    Outcome C — CURRENT INCIDENCE UPPER ROUTE TOO WEAK