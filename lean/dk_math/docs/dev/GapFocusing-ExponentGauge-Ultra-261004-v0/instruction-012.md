# Instruction 012 — Legendre canonical root head / rough tail cancellation

## Mission

Continue from Instruction 011.

Instruction 011 established an exact canonical-root decomposition of the existing support excess:

    E(n) = sum_p |canonicalRootFiber(n,p)|

and exact small-root charges for prime anchors n>7:

    C3 = |root fiber 3|,
    C5 = |root fiber 5|,
    C7 = |root fiber 7|.

It broke the fixed-basis CRT barrier:

    n=211: C3+C5 = 105 >= D=98,
    n=503: C3+C5+C7 = 336 >= D=312.

The next question is not merely whether root11 adds more charge.

The next structural target is:

> After removing the contribution owned by roots up to a cutoff P, what exact object remains?

The intended transformation is

    B2(n) - HeadCharge(n,P) < A(n)

in place of

    HeadCharge(n,P) >= B2(n)-A(n)+1.

Equivalently, understand whether the remaining demand after canonical-root cancellation can be identified with a rough large-root tail and bounded directly.

## Core principle

A canonical root larger than P means that the shell point n^2+r has no active prime divisor <=P.

Therefore the tail after roots <=P should be interpretable as a finite small-prime-rough object.

This task should make that statement exact before seeking a bound.

Do not introduce another support-excess ledger.

## Required source audit

Audit at minimum:

    DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootFiber
    DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootSieve
    DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootCharge
    DkMath.NumberTheory.Legendre.ParitySafeIncidenceUpper
    DkMath.NumberTheory.Legendre.ParitySafeReducedResidue
    DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveRoughCofactor
    DkMath.NumberTheory.Legendre.ParitySafeNearFirstPrimeWaveCapacity
    DkMath.NumberTheory.Legendre.PairOverlap
    DkMath.NumberTheory.Legendre.ParitySafeMobiusOddCorrection

and current production consumers for uncovered candidates / square-cell primes.

Record exact existing theorem names before adding code.

## Phase 1 — exact head/tail partition of canonical excess

For a cutoff P define, locally or publicly only if useful:

    RootHead(n,P) = incidences with canonical root <= P,
    RootTail(n,P) = incidences with canonical root > P.

Prove the exact partition:

    E(n) = card(RootHead(n,P)) + card(RootTail(n,P)).

Also prove:

    card(RootHead(n,P))
      = sum_{p in active(n), p<=P} |canonicalRootFiber(n,p)|.

Do not rebuild E; filter the existing canonical incidence set.

## Phase 2 — characterize the tail by roughness

Prove the exact seat-level condition:

    canonicalRoot(n,r) > P

if and only if, under the appropriate covered/candidate hypotheses,

    no active prime a<=P divides n^2+r.

Be careful about:

- empty support;
- roots not themselves active;
- P below the first odd active prime;
- <= versus < endpoint conventions.

Preferred formulation uses the actual active-prime filter

    {a in squareAnchorOddActivePrimes n | a <= P}.

Then lift this to an exact membership characterization of RootTail.

## Phase 3 — tail as candidate rough-incidence object

Create the smallest useful finite object representing tail incidences by:

    candidate seat r,
    secondary active label q,
    q in activeSupport(n,r),
    and no active a<=P divides n^2+r.

Prove this is exactly RootTail after the existing canonical coordinate is eliminated.

The goal is to expose the tail without referring to min' in later counting theorems.

## Phase 4 — secondary-q decomposition of head and tail

Instruction 011 decomposed E first by root p, then by secondary q.

Now also regroup by secondary q where useful.

Target an exact finite identity of the form

    HeadCharge(n,P)
      = sum_q HeadOwnedAtSecondary(n,P,q),

with

    HeadOwnedAtSecondary(n,P,q)
      = sum_{p<=P, p<q} |canonicalRootPairOffsets(n,p,q)|.

Then expose

    B2(n) - HeadCharge(n,P)

as a sum or bounded sum over the same active-q index whenever Nat subtraction permits.

Do not force termwise subtraction unless a pointwise inequality is proved.

## Phase 5 — pointwise demand cancellation audit

For each active secondary q, compare:

    paritySafeTwoPrimeWaveUpper n q

against

    sum_{p<=P, p<q} canonical root-p pair charge at q.

Investigate whether the difference has an exact or bounded interpretation as:

- q-incidences whose canonical root>P;
- a rough reduced-quotient interval;
- or an upper bound for such a tail.

Preferred result:

    TailIncidenceAtQ(n,P,q)
      <= paritySafeTwoPrimeWaveUpper n q - HeadChargeAtQ(n,P,q)

or the reverse orientation actually supported by definitions.

Do not assume B2 is exact incidence; remember B2 is only an upper bound.

Preserve the distinction between:

    actual incidence I,
    canonical excess E,
    upper cap B2.

## Phase 6 — root11 exact sieve

Implement root11 as the first calibration beyond 3,5,7.

For prime anchor n>11, root11 excludes active roots3,5,7.

Use exact finite inclusion-exclusion over the three smaller roots where practical.

Do not use a sequential Nat subtraction formula unless proved correct.

The exact combinatorics should include:

- three single exclusions;
- three pairwise intersections;
- one triple intersection;

all on candidate product waves.

Derive an exact root11 pair-card formula and a root11 total charge over all secondary q>11.

If a generic 3-exclusion neutral theorem is cleaner, add it.

## Phase 7 — generic finite inclusion-exclusion boundary

Audit how far exact inclusion-exclusion should be generalized.

At minimum provide a reusable theorem for three exclusions.

Do not automatically implement arbitrary powerset inclusion-exclusion unless it is clearly justified by later use.

Compare:

    exact IE for small roots

against

    canonicalRootSieveLower

which already supplies a generic union-bound lower estimate.

Record the exact credit lost by the generic union bound on calibration shells.

## Phase 8 — prime-anchor cutoff charges

For prime anchors define or derive cumulative exact charges:

    C<=3, C<=5, C<=7, C<=11.

Required exact checkpoints:

    n = 47, 97, 127, 211, 503.

Also test at least:

    n = 1009

and one larger prime if runtime is reasonable.

For each report:

    A(n), B2(n), D(n),
    cumulative charge through each cutoff,
    least tested cutoff meeting demand.

All production proofs must come from floor/product-wave formulas, not direct whole-E evaluation.

## Phase 9 — rough-tail cardinal diagnostics

For the same checkpoints, kernel-check:

    actual RootTail card after P=3,5,7,11

as diagnostic equalities if feasible.

These may evaluate the filtered canonical incidence object because this phase is diagnostic.

Do not use those exact tail evaluations as dependencies of structural prime theorems.

Compare:

    tail actual card,
    remaining demand D - head charge,
    any structural rough-tail upper/lower bounds.

## Phase 10 — direct rough-tail counting by finite small-prime avoidance

For prime anchor n and cutoff P, a rough tail seat avoids every active prime <=P.

Explore a direct finite count on candidate shell points:

    r in squareAnchorOddPointCoprimeOffsets n
    with
    forall a in active(n), a<=P -> a does not divide n^2+r.

Use exact odd/candidate wave formulas and finite inclusion-exclusion for P=3,5,7,11 where tractable.

Determine whether this seat count controls RootTail incidence count or only the number of tail seats.

Important:

    one rough seat may contribute several secondary q labels.

So a seat-count bound alone is not an incidence-tail bound unless support multiplicity is also controlled.

Do not conflate these two quantities.

## Phase 11 — rough tail multiplicity

Study the per-seat secondary multiplicity when canonical root>P.

At such a seat, all active support primes exceed P.

Use the product constraint

    product of distinct support labels divides n^2+r < (n+1)^2

to derive any elementary support-card bound available from the cutoff.

Candidate target:

    if k distinct active primes all exceed P divide n^2+r,
    then (nextPrimeAboveP)^k <= n^2+2n.

Do not introduce logarithms unless necessary.

Prefer a Nat-safe product lower bound.

This could turn rough-seat count into rough-tail incidence count.

## Phase 12 — head plus rough-tail inequality

Combine the head exact charge and any rough-tail multiplicity/counting result.

Seek a theorem of one of these forms:

    B2(n) < A(n) + HeadCharge(n,P),

or

    RemainingCap(n,P) < A(n),

or

    RootTail(n,P) <= TailBound(n,P)

together with a demand comparison sufficient for uncovered candidates.

Do not claim a cancellation theorem unless the algebra between B2 and head charge is rigorous.

## Phase 13 — determine whether cutoff growth is controlled

Using checked prime checkpoints, ask:

> How large must P be before the cumulative canonical-root charge meets demand?

Report the least tested cutoff.

Then compare it with simple structural scales:

    constant cutoff;
    P <= sqrt(n);
    P^2 <= n;
    P <= n;

only as finite diagnostics unless a theorem is proved.

Do not infer asymptotics from the table.

## Phase 14 — exact next uniform theorem

If head/tail decomposition gives real leverage, state the smallest missing uniform theorem.

Preferred shape:

    for prime n>n0, choose an explicit cutoff P(n),
    prove cumulative canonical-root structural charge through P(n)
      >= B2(n)-A(n)+1.

Or, if easier:

    prove a structural upper bound on the rough tail after P(n)
    that implies the same demand inequality.

The function P(n) must be specified independently of evaluating full E.

If the rough tail approach fails, identify the exact failure:

- tail seat count is small but multiplicity large;
- finite IE becomes too weak;
- B2 is too loose;
- cutoff must grow too rapidly;
- or another obstruction.

## Possible outcomes

### Outcome A — head/tail cancellation yields new structural leverage

Root11 is exact, the canonical tail is characterized as a rough object, and a head/tail theorem gives a stronger route than simply appending roots. Preferably new large prime checkpoints are solved structurally.

### Outcome B — root hierarchy advances, tail bound still weak

Root11 and exact head/tail partition are formalized and more checkpoints are solved, but no useful structural rough-tail bound controls the remaining demand.

### Outcome P — one precise rough-tail multiplicity/count bridge remains

The exact head/tail reformulation is complete, but one explicit theorem relating rough seats to tail incidence multiplicity blocks the quantitative result.

### Outcome C — head/tail reformulation gives no new leverage

The tail characterization is exact but does not improve demand comparison beyond adding more exact roots. Identify the next provider/currency.

## Non-goals

Do not claim:

    Legendre's conjecture;
    uniform T=1;
    PNT/RH;
    analytic sieve estimates;
    FLT/ABC consequences.

Do not use full E or full I direct evaluation as a structural proof.

Do not create duplicate exact support-excess ledgers.

Do not use sorryAx-bearing endpoints in production.

## Implementation guidance

Prefer extending:

    DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootFiber
    DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootSieve
    DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootCharge.

If the tail abstraction is substantial, a focused module such as

    DkMath/NumberTheory/Legendre/ParitySafeCanonicalRootTail.lean

is justified.

Keep neutral finite inclusion-exclusion lemmas outside the Legendre namespace when appropriate.

## Validation

For all new production declarations:

- focused builds;
- lake build DkMath.NumberTheory.Legendre;
- lake build DkMath;
- forbidden-token scan;
- #print axioms for every new public declaration;
- git diff --check.

All new production declarations must remain free of sorryAx.

Keep the existing project convention for file headers and import-adjacent

    #print "file: ..."

markers on every modified/new Lean file.

## Durable checkpoint protocol

Update findings after:

- exact head/tail partition;
- tail roughness characterization;
- secondary-q regrouping;
- first pointwise B2-vs-head comparison;
- exact root11 sieve;
- 3-exclusion inclusion-exclusion theorem;
- 1009 checkpoint;
- rough-tail seat count;
- rough-tail multiplicity bound;
- final A/B/P/C judgment.

Preserve false termwise-cancellation formulas and smallest counterexamples.

## Final report

Answer explicitly:

1. What exact head/tail partition of the existing canonical incidence was proved?
2. Is root>P exactly equivalent to avoiding all active primes <=P at the shell point?
3. Can head charge and B2 be regrouped over the same secondary-q index without invalid Nat subtraction?
4. What exact root11 inclusion-exclusion formula was proved?
5. What cumulative charges are obtained at47,97,127,211,503,1009 and any larger tested primes?
6. What least root cutoff meets demand at each checkpoint?
7. What exact rough-tail seat or incidence bound was proved?
8. Can support multiplicity of a rough tail seat be bounded from the cutoff P?
9. Does head/tail cancellation improve structurally on merely adding more canonical roots?
10. What exact uniform theorem remains?

End with exactly one judgment:

    Outcome A — HEAD/TAIL CANCELLATION GAINS NEW LEVERAGE
    Outcome B — ROOT HIERARCHY ADVANCES, TAIL BOUND WEAK
    Outcome P — PRECISE ROUGH-TAIL BRIDGE REMAINS
    Outcome C — HEAD/TAIL REFORMULATION ADDS NO LEVERAGE