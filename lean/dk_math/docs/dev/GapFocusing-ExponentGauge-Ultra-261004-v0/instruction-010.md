# Instruction 010 — Legendre merged CRT families / demand-scaling audit

## Mission

Continue from Instruction 009.

Instruction 009 completed several important provider layers:

- congruence-to-support transport;
- parity-adjusted short-window CRT witnesses;
- prime-anchor candidate construction;
- indexed distinct-seat charge aggregation;
- same-modulus period families;
- an infinite prime-anchor excess provider;
- adaptive certificate consumers.

The remaining question is now quantitative:

> Can multiple CRT witness families be combined so that guaranteed support-excess charge grows fast enough to meet
>
>     D(n) = B2(n) - A(n) + 1
>
> on the hard shells?

A single fixed family Q={3,5,7} scales too slowly: for example n=107 has demand39 while that family only guarantees charge2.

The next task must therefore test **demand scaling**, not merely add more isolated shell certificates.

The central new abstraction is:

> Multiple CRT families may land on the same actual seat. Such collisions must not be double-counted; instead, merge all witness labels realized at that seat and charge the union support once.

## Current hard-shell diagnostics

From report-009, unresolved shells in 2..100 are:

    47,53,58,59,61,62,64,67,68,71,73,74,76,79,80,82,83,86,88,89,92,94,97,98,100.

Representative required charges:

    n=68 : D=7
    n=58 : D=8
    n=97 : D=30

and for prime n=107 outside the diagnostic range:

    D(107)=39.

These are mandatory scaling checkpoints.

## Required source audit

Audit at minimum:

    DkMath.NumberTheory.Legendre.ParitySafeCRTSeat
    DkMath.NumberTheory.Legendre.ParitySafeExcessCertificate
    DkMath.NumberTheory.Legendre.ParitySafeIncidenceUpper
    DkMath.NumberTheory.Legendre.ParitySafeIncidenceBalance
    DkMath.NumberTheory.Legendre.ParitySafeReducedResidue
    DkMath.NumberTheory.Legendre.ParitySafeBlockLocalization

and current Mathlib Finset union/image, Nat.ModEq, CRT, product, coprimality APIs.

Record exact theorem names before extending production.

## Phase 1 — merged-seat witness union

Suppose an indexed family j carries:

    seat(j) : Nat
    Q(j)    : Finset Nat

with every Q(j) realized in the actual active support at seat(j).

Several j may share the same seat.

Define or construct, preferably locally unless a reusable definition is justified, the merged witness set

    W(r) = union of Q(j) over all j with seat(j)=r.

Prove:

    W(r) subset paritySafeActiveSupport n r.

Then prove the merged global charge inequality:

    sum over actual image seats r of (W(r).card - 1)
      <= paritySafeSupportExcess n.

This theorem must not require seat injectivity.

Do not double-count a witness prime that appears in several Q(j) landing at the same seat.

## Phase 2 — compare injective vs merged charge

Show that when seat is injective, the merged theorem reduces to or implies the existing

    sum_indexed_modEq_charge_le_supportExcess.

Also preserve a counterexample to the naive noninjective sum

    sum_j (Q(j).card-1) <= supportExcess

if false.

The report must distinguish:

- family-index charge;
- merged-seat charge;
- actual support-excess charge.

## Phase 3 — overlap can be productive

Investigate exact local behavior when two witness sets Q1,Q2 land on one seat.

If both are support subsets, then

    Q1 union Q2 subset activeSupport.

Therefore the correct local charge is

    |Q1 union Q2| - 1.

Compare this with

    (|Q1|-1) + (|Q2|-1).

Classify when merging loses charge due to overlap and when it creates a larger high-support certificate than either family alone.

Formalize the smallest useful Finset cardinal identity/inequality.

## Phase 4 — family collection provider

Build a reusable theorem taking a finite collection of witness families and producing a merged-seat excess lower bound.

Desired inputs:

    J : Finset iota
    seat : iota -> Nat
    Q : iota -> Finset Nat

with candidate and support-realization hypotheses.

Desired conclusion:

    mergedCharge(J,seat,Q) <= paritySafeSupportExcess n.

A public mergedCharge definition is optional; use one only if it materially simplifies later theorems.

## Phase 5 — generate many prime-anchor period families

For prime anchor n, the current theorem handles one fixed Q with period

    2 * product(Q).

Now consider a finite collection of small admissible witness sets Q_j.

Generate all actual period-family seats in the shell window for each Q_j, then merge them by actual seat.

Suggested first witness-set pool:

    all 2-prime subsets from a small odd-prime basis;
    all 3-prime subsets whose product is not excessively large;

with the basis itself bounded and explicit.

Do not use all primes below n by default; start with a controlled finite basis such as {3,5,7,11,13,17,19} when active.

Kernel-check the resulting finite construction for selected prime anchors.

## Phase 6 — demand-scaling quantity

For diagnostics define conceptually

    C(n;F) = merged guaranteed charge from a chosen finite family pool F.

Do not create C as production unless useful.

Compare C with

    D(n)=B2(n)-A(n)+1.

For each checkpoint report:

    A(n), B2(n), D(n), merged charge C, and C-D.

Mandatory checkpoints:

    47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 107.

The purpose is to learn scaling behavior on prime anchors.

## Phase 7 — solve n=58 and n=68

Use the merged-family machinery to attempt the first low-demand mixed-anchor survivors.

Targets:

    n=68 with D=7,
    n=58 with D=8.

Allow at least four actual candidate seats if needed.

Certificates may use different witness-set sizes.

Do not require all families to arise from the same modulus.

Prove actual uncovered-candidate and square-cell-prime theorems if the charge meets demand.

## Phase 8 — parity/coprimality-aware CRT for mixed anchors

For anchors of the form

    n = 2^a * p^k

with odd prime p and witness primes excluding 2 and p, investigate the proposed combined CRT system:

    n^2 + r ≡ 0 mod m
    n^2 + r ≡ 1 mod 2*p

where

    m = product(Q).

Since gcd(m,2p)=1 under the stated hypotheses, CRT applies.

Formalize the cleanest theorem possible:

- congruence modulo m realizes all Q support labels;
- congruence modulo2p forces oddness and excludes p from the point;
- derive candidate coprimality with n;
- obtain a positive representative in a period of size 2*p*m.

Then identify the sufficient short-window criterion for a representative in 1..2n.

Do not claim necessity.

## Phase 9 — mixed-anchor counted family

If Phase8 succeeds, derive a same-modulus lift family analogous to

    prime_anchor_period_family_charge_le_supportExcess

for n=2^a p^k.

Expected period is based on 2*p*m or a divisor thereof if normalization improves it.

Prove:

- all lifted seats are actual candidates;
- seats are distinct;
- Q remains in active support;
- a counted charge lower bound follows.

Then test on:

    58,62,68,74,76,80,82,86,88,92,94,98,100.

## Phase 10 — survivor reduction under adaptive family pools

Revisit the25 unresolved shells from report-009.

Use explicit finite family pools and merged-seat counting.

Classify:

    solved;
    unresolved because merged charge < demand;
    unresolved because no candidate/window theorem applies;
    unresolved only because the current search pool is bounded.

Every claimed solved shell must be kernel checked.

Do not turn heuristic family search into production proof without explicit witness data/theorems.

## Phase 11 — asymptotic-style scaling audit without analytic prime estimates

Do not invoke PNT or asymptotics as proof.

But structurally compare how the proved lower charge formulas grow with n.

For a fixed witness set Q on prime anchors:

    charge_Q(n) ~ ((n-1)/product(Q))*(|Q|-1)

is only an interpretation; the theorem is the exact floor formula.

For a finite family pool F, sum/merge the exact floor-based contributions and compare with D(n) on increasing prime checkpoints.

Determine whether the ratio

    merged guaranteed charge / D(n)

appears to improve, stay bounded away from1, or deteriorate.

State only checked finite conclusions.

## Phase 12 — prove one nontrivial scaling theorem if available

If the merged-family construction admits an exact lower bound of the form

    c * n - O(1) <= guaranteed excess

with explicit natural-number constants and no analytic prime theorem, formalize it for a fixed family pool.

Only do this if the overlap structure is controlled rigorously.

Examples:

- pairwise seat-disjoint family pools;
- same-period families with modularly separated residue classes;
- nested witness sets whose merged charge is explicitly computable.

Do not force a linear theorem if overlaps prevent a clean proof.

## Phase 13 — determine whether CRT remains the main route

At the end, answer the strategic question:

> Does merged CRT charge plausibly scale at the same order as D(n), using the exact proved finite data and formulas?

If yes, state the next precise provider theorem.

If no, identify what currency/provider must replace or supplement it.

Possible alternatives include:

- sharper B2 incidence caps;
- higher-order anchor exclusions for applicable classes;
- direct factorization multiplicity lower bounds;
- a different seat-generation mechanism not tied to short CRT periods.

Do not answer this strategically from intuition alone; base it on the checked diagnostics.

## Possible outcomes

### Outcome A — merged CRT scales and solves new hard shells

Merged-seat counting is formalized, n=58 and n=68 are solved, survivor count drops materially, and finite scaling diagnostics show the merged charge can track demand on at least a meaningful class.

### Outcome B — merged CRT formalized, limited scaling

Merged-seat charge and mixed-anchor CRT are formally useful, but demand grows faster than the guaranteed charge on hard checkpoints.

### Outcome P — one exact mixed/merge bridge remains

The family merge theory is complete but one precise theorem blocks mixed-anchor counted families or demand comparison.

### Outcome C — CRT scaling is insufficient

Formal merged-family diagnostics show that this provider cannot plausibly meet demand on the hard class with the current incidence cap. Identify the next provider/currency.

## Non-goals

Do not claim:

    Legendre's conjecture;
    uniform T=1;
    analytic prime-counting estimates;
    PNT/RH;
    FLT/ABC consequences.

Do not use whole-shell exact incidence evaluation as a substitute for structural upper bounds.

Do not use sorryAx-bearing endpoints in production.

## Implementation guidance

Likely production homes:

    DkMath.NumberTheory.Legendre.ParitySafeCRTSeat

for merged CRT family mathematics, and existing excess/incidence modules for consumers.

Create a new module only if the merge abstraction becomes substantial enough to deserve one.

Keep generic finite-set union/cardinality lemmas in a neutral namespace where appropriate.

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

- merged-seat witness theorem;
- noninjective counterexample or reduction to injective case;
- family-collection charge provider;
- prime-anchor merged-family diagnostics;
- n=58 and n=68 attempts;
- mixed-anchor CRT candidate theorem;
- mixed-anchor counted family;
- survivor recount;
- demand-scaling checkpoint table;
- final A/B/P/C judgment.

Preserve failed scaling conjectures and smallest counterexamples.

## Final report

Answer explicitly:

1. What exact merged-seat charge theorem was proved?
2. How does it relate to the old injective indexed-family theorem?
3. Can shared-seat witness families be merged without double counting?
4. Are n=58 and n=68 solved structurally?
5. What mixed-anchor CRT theorem was proved for n=2^a p^k?
6. How many of the25 survivors remain after merged-family certificates?
7. On prime checkpoints up to and beyond107, how does guaranteed merged charge compare with D(n)?
8. Is there an exact reusable scaling lower bound for a fixed family pool?
9. Does merged CRT remain a credible route toward uniform A+e>B2?
10. What is the next exact theorem if uniformity is still missing?

End with exactly one judgment:

    Outcome A — MERGED CRT SCALES AND SOLVES NEW HARD SHELLS
    Outcome B — MERGED CRT FORMALIZED, LIMITED SCALING
    Outcome P — PRECISE MERGE/MIXED BRIDGE REMAINS
    Outcome C — CRT SCALING IS INSUFFICIENT