# Instruction 013 — Legendre sqrt-cutoff rough moments / pair-triple balance

## Mission

Continue from Instruction 012.

Instruction 012 proved two facts that should now be used together:

1. `canonicalRoughWave` gives the exact full rough incidence currency

       roughI(n,P) = sum over rough seats r of activeSupport(n,r).card;

2. at the independent cutoff

       P = Nat.sqrt n,

   every rough candidate satisfies

       activeSupport.card <= 3.

The second fact turns the rough shell into a finite moment problem with only
support cardinalities 0,1,2,3.

The purpose of this task is to exploit that truncation exactly.

Do not replace the existing rough/head/tail ledgers.

Add only the pair and triple moments needed to recover the zero-support seats.

## Central local identities

For a finite support of size k<=3, the following identities hold:

    1_{k=0} + k + choose(k,3) = 1 + choose(k,2),

and

    (k-1 truncated at 0) + choose(k,3) = choose(k,2).

Therefore, at the sqrt cutoff, the desired global identities are

    uncovered.card + roughI + M3 = roughSeats.card + M2,

and

    tail + M3 = M2.

These must be proved Nat-safely, without integer subtraction in the public API.

The first identity gives the exact moment criterion

    uncovered.Nonempty
      iff
    roughI + M3 < roughSeats.card + M2,

for positive anchors after the exact uncovered/rough-empty identification.

This criterion is weaker than the old sufficient condition

    roughI < roughSeats.card,

because pair credit M2 is recovered and only triple cost M3 is repaid.

## Required source audit

Audit at minimum:

    DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootTail
    DkMath.NumberTheory.Legendre.ParitySafeCanonicalRoughCount
    DkMath.NumberTheory.Legendre.ParitySafePrimeAnchorCap
    DkMath.NumberTheory.Legendre.PairOverlap
    DkMath.NumberTheory.Legendre.Internal.PairCombinatorics
    DkMath.NumberTheory.Legendre.ParitySafeTripleProductGate
    DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveRoughCofactor
    DkMath.NumberTheory.Legendre.ParitySafeReducedResidue
    DkMath.NumberTheory.Legendre.ParitySafeMobiusOddCorrection

and any existing finite triple / `Nat.choose _ 3` combinatorics already in Mathlib or DkMath.

Record exact reusable theorem names before adding abstractions.

## Phase 1 — rough empty seats are exactly uncovered candidates

`mem_uncovered_iff_no_activeSupport` and the private rough-inclusion fact already
show both directions conceptually.

Promote the smallest useful public statement:

    rough candidates with empty active support
      = paritySafeUncoveredCandidates n.

This should hold for every cutoff P.

Equivalently prove the exact cardinal statement if a set equality is awkward.

This is needed so that the moment zero-class is the existing uncovered object,
not a new notion.

## Phase 2 — local pair/triple moment algebra

Prove a neutral finite-cardinality lemma for k<=3:

    (if k=0 then 1 else 0) + k + Nat.choose k 3
      = 1 + Nat.choose k 2.

Also prove:

    (k-1) + Nat.choose k 3 = Nat.choose k 2

for k<=3, where Nat subtraction has the intended truncated meaning.

Prefer a small finite `interval_cases k` proof over algebraic coercions.

Preserve a regression showing the identities fail in the truncated form once
k=4 if appropriate; the sqrt support bound is a real hypothesis.

## Phase 3 — define rough pair and triple moments

Use the existing rough candidate carrier.

Preferred numerical definitions are:

    M2(n,P) = sum over r in canonicalRoughCandidates n P
                Nat.choose (activeSupport n r).card 2,

    M3(n,P) = sum over r in canonicalRoughCandidates n P
                Nat.choose (activeSupport n r).card 3.

Names are implementation choices.

Do not define moments from factorization or direct primeFactor evaluation.

## Phase 4 — exact sqrt-cutoff conservation

Using `sqrtCutoff_support_card_le_three`, prove the exact global identities:

    paritySafeUncoveredCandidates.card + roughI_sqrt + M3_sqrt
      = canonicalRoughCandidates(n,sqrt n).card + M2_sqrt,

and

    canonicalRootTail(n,sqrt n).card + M3_sqrt = M2_sqrt.

Here `roughI_sqrt` should be the existing sum of `canonicalRoughWave` cards,
rewritten through `roughWave_sum_eq_support_sum` when useful.

Do not numerically evaluate whole E or I.

## Phase 5 — exact moment consumer

Export a direct consumer:

    roughI_sqrt + M3_sqrt
      < roughSeats_sqrt.card + M2_sqrt
      -> paritySafeUncoveredCandidates n is Nonempty.

Then consume through the existing square-cell prime theorem for n>0.

Also prove the converse at the cardinal level if it follows cleanly:

    uncovered.card > 0
      iff
    roughI_sqrt + M3_sqrt < roughSeats_sqrt.card + M2_sqrt.

This should be an exact combinatorial equivalence, not a heuristic.

## Phase 6 — pair-incidence realization of M2

Build the minimal finite pair carrier whose cardinality is exactly M2.

Preferred representation:

    (r,(p,q))

with:

- r a sqrt-rough candidate;
- p,q in actual active support at r;
- p<q.

Reuse `upperPairs` if it avoids duplicate combinatorics.

Prove:

    pairIncidences.card = M2_sqrt.

Then regroup by the active pair `(p,q)` and define/identify its seat fiber.

## Phase 7 — triple-incidence realization of M3

Similarly build the exact unordered triple carrier for M3:

    (r,(p,q,s))

with

    p<q<s

and all three labels in actual support.

Prove:

    tripleIncidences.card = M3_sqrt.

Reuse existing triple combinatorics if already present.

Do not identify this object with an old residual triple ledger unless exact
membership equality is proved.

## Phase 8 — product-wave bridges

For each supported rough pair p<q prove:

    p*q divides n^2+r.

Conversely, for active p,q, a sqrt-rough candidate with p*q dividing its point
belongs to the rough pair seat fiber.

Thus the pair fiber is exactly:

    canonicalRoughCandidates(n,sqrt n)
      filtered by p*q | n^2+r.

Do the analogous statement for triples and p*q*s.

These should be min-free and canonical-root-free.

## Phase 9 — sqrt-cutoff product scale

Let P=Nat.sqrt n and L=P+1.

Prove the elementary scale facts:

    n < L^2,

and for distinct rough support labels p,q:

    n < p*q.

For three rough support labels p,q,s, prove:

    2*n < p*q*s

for the natural range where needed; handle tiny n separately rather than
silently assuming positivity.

Consequences to connect to existing wave APIs:

- every rough pair product has at most two raw shell-wave seats;
- every rough triple product has at most one raw shell-wave seat.

Candidate/rough fibers are subsets, so inherit the same upper bounds.

Use existing `card_squareWaveOffsets_eq_div_add_carry`,
`squareWaveCarry_le_one`, and far-wave lemmas where appropriate.

## Phase 10 — exact triple-seat factorization at sqrt cutoff

Investigate and, if correct, prove the stronger consequence of the already
proved fourth-power threshold.

For a sqrt-rough candidate with exactly three distinct active support labels
p<q<s:

    p*q*s | n^2+r,

and every label is at least L.

Since

    n^2+2n < L^4

the complementary quotient after dividing by p*q*s is <L.

Any nontrivial prime divisor of that quotient would be <=P and would contradict
sqrt-roughness.

Target:

    n^2+r = p*q*s.

Audit endpoint/coprimality details carefully.

If this exact factorization fails, preserve the smallest counterexample and
state the corrected quotient theorem.

## Phase 11 — two-support quotient classification

Only if Phase10 succeeds cleanly, inspect the analogous support-card2 case.

For support exactly {p,q}, p<q, the quotient after p*q is strictly below L^2.

Determine whether the point must be one of

    p*q,
    p^2*q,
    p*q^2,

or whether a factor outside the active-prime universe can occur.

Do not assert this classification without proof.

Preserve any first counterexample.

This phase is diagnostic and must not block the moment bridge.

## Phase 12 — structural pair/triple wave formulas

Regroup M2 and M3 over active labels:

    M2 = sum_{p<q, p,q>P} roughPairWave(p,q).card,

    M3 = sum_{p<q<s, p,q,s>P} roughTripleWave(p,q,s).card.

Keep the actual active-prime universe and cutoff filters explicit.

For prime anchors, connect each fixed pair/triple fiber to the existing
candidate product-wave floor/carry machinery as far as possible.

Do not introduce analytic prime counting.

## Phase 13 — calibration checkpoints

Kernel-check the moment identities and product-wave regrouping at:

    n=211,503,1009,1013.

Also choose at least one prime anchor >1013 for which runtime is reasonable.

For each report:

    P=sqrt n,
    roughSeats,
    roughI,
    M2,
    M3,
    uncovered.card as recovered from the moment identity,
    direct margin roughSeats-roughI,
    moment margin roughSeats+M2-(roughI+M3).

The last margin should equal uncovered.card by theorem, not merely by external arithmetic.

Numerical checks may use kernel-decided finite objects in calibration modules,
but structural prime proofs must use the proved moment/product-wave path.

## Phase 14 — find where pair credit matters

Perform a bounded diagnostic scan over prime anchors, with a justified finite
range compatible with runtime.

Search for the first anchor where:

    roughI >= roughSeats

so the old direct sufficient criterion fails, but

    roughI + M3 < roughSeats + M2

so the exact moment criterion still succeeds.

If such an anchor is found, make it a mandatory kernel regression and prove
its square-cell prime structurally through the moment consumer.

If none is found in the tested range, report that fact exactly and do not infer
uniform direct-rough sufficiency.

## Phase 15 — isolate the remaining uniform arithmetic obligation

After the exact moment bridge, determine which quantity is hardest to control
uniformly:

- rough singleton-support seats;
- rough pair moment M2 from long product waves;
- triple cost M3;
- or the rough seat carrier itself.

Note that the exact identity rewrites rough covered seats as

    roughCovered + M2 = roughI + M3.

Thus a uniform proof may proceed by bounding the RHS-minus-pair-credit rather
than by forcing average support below1.

State one precise next theorem contract.

## Phase 16 — optional connection to old far product/triple machinery

Only after the new rough pair/triple maps are proved, audit whether existing
modules such as

    ParitySafeTripleProductGate
    ParitySafeFarProductWaveRoughCofactor
    ParitySafeFarProductWaveSelector

can consume the sqrt-rough pair/triple carriers without changing their meaning.

Do not import old capacities solely because names look similar.

Require an exact map or subset theorem first.

## Possible outcomes

### Outcome A — rough moment balance adds quantitative leverage

The exact pair/triple moment conservation is formalized, product-wave carriers
are connected, and at least one structural result is obtained that is not
available from the old `roughI < roughSeats` criterion alone.

### Outcome B — exact moment bridge complete, no new finite leverage

The conservation law and pair/triple product-wave representations are complete,
but the tested direct rough criterion already succeeds everywhere and no
stronger uniform estimate is yet obtained.

### Outcome P — one precise pair/triple counting bridge remains

The exact combinatorial moment identities are complete, but one explicit
product-wave or rough-filter counting theorem blocks structural use.

### Outcome C — moment reformulation adds no useful arithmetic currency

The exact identities are mostly tautological and pair/triple waves do not
improve the quantitative frontier. Identify the next provider.

## Non-goals

Do not claim:

    Legendre's conjecture;
    uniform T=1;
    PNT/RH;
    analytic sieve estimates;
    FLT/ABC consequences.

Do not evaluate whole E or whole I as the proof of a structural endpoint.

Do not introduce a graph/hypergraph framework unless existing finite-set APIs
are demonstrably inadequate.

Do not use sorryAx-bearing endpoints in production.

## Implementation guidance

A focused module such as

    DkMath/NumberTheory/Legendre/ParitySafeSqrtRoughMoments.lean

is justified if the moment carriers and conservation laws are substantial.

Prefer reusing:

    ParitySafeCanonicalRootTail
    ParitySafeCanonicalRoughCount
    ParitySafePrimeAnchorCap
    PairOverlap

rather than duplicating their definitions.

Keep neutral k<=3 combinatorics outside the Legendre namespace where useful.

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

- rough-empty/uncovered equality;
- local k<=3 identities;
- global moment conservation;
- exact moment consumer;
- pair incidence card=M2;
- triple incidence card=M3;
- pair/triple product-wave bridges;
- sqrt product-period bounds;
- triple exact-factorization attempt;
- bounded search for direct-failure/moment-success;
- final A/B/P/C judgment.

Preserve failed quotient classifications and smallest counterexamples.

## Final report

Answer explicitly:

1. What exact k<=3 local identities were proved?
2. Is the global identity
       uncovered + roughI + M3 = roughSeats + M2
   proved at cutoff sqrt n?
3. Is `tail + M3 = M2` proved exactly?
4. What finite pair and triple carriers realize M2 and M3?
5. Are their fibers exactly rough candidate product waves?
6. What period/occupancy bounds follow from p,q,s>sqrt n?
7. Does a three-support rough seat factor exactly as p*q*s?
8. What do the required calibration anchors show?
9. Was a prime found where direct rough comparison fails but moment comparison succeeds?
10. What exact uniform theorem remains after the moment reformulation?

End with exactly one judgment:

    Outcome A — ROUGH MOMENT BALANCE ADDS QUANTITATIVE LEVERAGE
    Outcome B — EXACT MOMENT BRIDGE COMPLETE, NO NEW FINITE LEVERAGE
    Outcome P — PRECISE PAIR/TRIPLE COUNTING BRIDGE REMAINS
    Outcome C — MOMENT REFORMULATION ADDS NO USEFUL CURRENCY