# Instruction 009 — Legendre adaptive excess certificate / CRT seat family

## Mission

Continue from Instruction 008.

Instruction 008 completed the consumer side of the hybrid method:

    incidenceCount(n) <= B2(n)

and reusable local support witness aggregation:

    local support witness subsets
      -> lower bound on paritySafeSupportExcess n.

Together with the exact uncovered-deficit ledger, this yields the criterion

    B2(n) < A(n) + e
    and
    e <= paritySafeSupportExcess n

therefore

    paritySafeUncoveredCandidates n is nonempty

and hence a prime in the square cell.

The remaining problem is now provider-side:

> Given the required charge
>
>     D(n) := B2(n) - A(n) + 1,
>
> construct enough candidate seats carrying enough admissible active-prime
> witnesses so that the total local support-excess charge is at least D(n).

Do not create D(n) as a production definition unless it materially improves
reusable theorem statements.

The first mandatory calibrations are n=41 and n=91.

## Current explicit targets

Instruction 008 produced the following unimplemented witness candidates.

For n=41:

    r=2   with witnesses {3,11,17}
    r=24  with witnesses {5,11,31}
    r=44  with witnesses {3,5,23}

For n=91:

    r=38  with witnesses {3,47,59}
    r=44  with witnesses {3,5,37}
    r=68  with witnesses {3,11,23}.

Each witness set has cardinality 3, so each seat should contribute at least 2
to support excess. Three distinct seats should therefore give excess >=6.

Both shells require at least charge 5 according to report-008.

## Required source audit

Audit at minimum:

    DkMath.NumberTheory.Legendre.ParitySafeIncidenceUpper
    DkMath.NumberTheory.Legendre.ParitySafeExcessCertificate
    DkMath.NumberTheory.Legendre.ParitySafeIncidenceBalance
    DkMath.NumberTheory.Legendre.ParitySafeReducedResidue
    DkMath.NumberTheory.Legendre.ParitySafePrimeSupport
    DkMath.NumberTheory.Legendre.ParitySafeBlockLocalization
    DkMath.NumberTheory.Primitive

and the existing CRT / modular arithmetic / Finset APIs in Mathlib already
available in the project.

Record exact theorem names before introducing any new abstraction.

## Phase 1 — formalize n=41 three-seat certificate

For each proposed seat r in {2,24,44}, prove:

- r is an actual parity-safe candidate for shell 41;
- every proposed q is prime;
- q <= 41;
- q != 2;
- q does not divide 41;
- q divides 41^2 + r;
- therefore q belongs to paritySafeActiveSupport 41 r.

Use the existing witness-subset API from Instruction 008 rather than
computing the full active support.

Then derive:

    6 <= paritySafeSupportExcess 41.

Use the generic hybrid uncovered theorem to prove:

    paritySafeUncoveredCandidates 41 is nonempty

and then:

    exists p, Prime p and 41^2 < p < 42^2.

The proof must not use direct evaluation of the full incidence count.

## Phase 2 — formalize n=91 three-seat certificate

Repeat the same structure for seats {38,44,68} and the proposed witness sets.

Derive:

    6 <= paritySafeSupportExcess 91,

then an uncovered candidate and a square-cell prime:

    exists p, Prime p and 91^2 < p < 92^2.

Again, do not replace the structural proof by whole-shell evaluation.

## Phase 3 — generic k-seat support-witness aggregation

Instruction 008 already has finite-set aggregation.

Audit whether it is ergonomic enough for adaptive certificate generation.

If needed, add a reusable theorem with inputs:

    R : Finset Nat
    P : Nat -> Finset Nat

such that:

- R is a subset of actual candidates;
- for each r in R, P(r) is a subset of actual active support;
- the seat set R is duplicate-free by Finset construction;

and conclude:

    sum_{r in R} (P(r).card - 1)
      <= paritySafeSupportExcess n.

Prefer reusing the exact Instruction 008 theorem if it already has this form.

The goal is to make a CRT-generated witness family directly consumable.

## Phase 4 — abstract one-seat CRT construction

Let Q be a finite set of odd primes satisfying the active-prime side
conditions relative to n:

    q <= n,
    q != 2,
    q does not divide n.

A seat r carrying all q in Q must satisfy

    r ≡ -n^2 (mod q)

for every q in Q.

Because the q are distinct primes, CRT gives a unique residue modulo

    m = product q in Q.

Formalize the cleanest reusable statement available in the current stack:

    if r is congruent to -n^2 modulo every q in Q,
    then Q subset paritySafeActiveSupport n r

provided r is an actual parity-safe candidate.

This direction is more important than constructing the canonical CRT residue
immediately.

Separate:

1. divisibility/support transport from congruence;
2. candidate-window existence.

Do not entangle them into one large theorem too early.

## Phase 5 — candidate conditions for CRT seats

A CRT residue is useful only if some representative r satisfies the actual
square-shell candidate conditions.

Audit the exact candidate definition and derive the minimal conditions needed
for:

    1 <= r <= 2*n
    Nat.Coprime n r
    Odd (n^2 + r).

Exploit consequences of the CRT congruences where possible.

In particular, if every q in Q is odd then q-divisibility alone does not
force the parity-safe condition. Treat parity separately and honestly.

Investigate whether adding modulus 2 to the CRT system gives a clean parity
selector for r.

## Phase 6 — windowed CRT seat existence

The central provider problem is not CRT solvability modulo m; that is easy.
It is whether a useful representative lies in the short window 1..2n.

Study the following progressively stronger targets.

Target A — exact residue consumer:

    given an explicitly supplied r in the window satisfying the congruences,
    build the support witness certificate.

Target B — one-period criterion:

    if product(Q) <= 2*n,
    then every CRT residue class has a representative in a window of length
    2*n.

Check endpoint and positivity details exactly.

Target C — parity-adjusted period:

    if parity is included, determine whether modulus 2*product(Q) changes the
    usable window criterion.

Do not assert a short-window CRT theorem if the period exceeds the window.

## Phase 7 — local charge from a CRT witness set

If Q subset activeSupport(n,r), then

    Q.card - 1 <= local support excess at r.

Combine this with the candidate theorem.

Produce a reusable theorem of the shape:

    candidate r
    + finite witness set Q of admissible primes
    + all q in Q divide n^2+r
      -> Q.card - 1 <= local excess contribution.

This theorem should make explicit witness certificates cheap to state.

## Phase 8 — multiple CRT seats and distinctness

To accumulate the required charge D(n), one needs multiple candidate seats.

Investigate how to generate pairwise-distinct seats from different witness
sets Q_j.

Possible mechanisms:

- distinct CRT residue classes;
- same modulus but different parity-compatible lifts;
- deliberately different prime subsets;
- different representatives in the shell window.

Do not assume distinct witness prime sets imply distinct seats.

Prove distinctness at the seat level.

## Phase 9 — adaptive certificate criterion

Build or reuse a generic consumer:

    if
      B2(n) < A(n) + sum_j (Q_j.card - 1),
    and the Q_j are realized on distinct actual candidate seats,
    then uncoveredCandidates(n) is nonempty.

Then consume to a square-cell prime.

This is the formal version of the adaptive required-charge strategy.

## Phase 10 — bounded diagnostic extension

Revisit the 30 unresolved shells from report-008.

Use a controlled certificate budget larger than the previous two-seat budget.

Suggested first budget:

- up to 3 candidate seats;
- up to 3 witness primes per seat;
- total available charge up to 6.

Do not scan unbounded ranges.

At minimum test all previous Class2 shells in 2..100.

Classify:

    solved with charge <=5,
    solved with charge 6,
    still unresolved.

Kernel-check every claimed shell theorem or certificate dataset.

Do not treat Python search output as proof.

## Phase 11 — arithmetic classification of survivors

For any shells still unresolved after charge 6, report:

    B2(n),
    A(n),
    required D(n),
    best found certificate charge,
    arithmetic type of n,
    whether failure is due to no suitable multi-support seats,
    or merely due to the current bounded search.

Pay special attention to:

    n prime,
    n = 2^a,
    n = 2^a p^k.

These were the dominant unresolved classes in report-008.

## Phase 12 — first structural provider class

If the CRT analysis yields a nontrivial sufficient condition, formalize one
infinite arithmetic class.

Examples to investigate, not assume:

1. If there exists a finite family of odd-prime sets Q_j with
   2*product(Q_j) <= 2*n and the corresponding CRT representatives are
   candidate seats, then the total charge is available.

2. If n is prime and several small primes q<n can be grouped into triples
   whose products are <= n, then each triple may generate a charge-2 seat.

3. If n=2^a p^k, use primes not dividing n and group them similarly.

Only state a class theorem if the actual candidate-window/parity conditions
are proved, not inferred heuristically.

## Phase 13 — identify the true uniform obstruction

The key question is whether the missing uniform theorem is now:

    enough small admissible primes exist below n,

or instead:

    their CRT residue classes fail to land in the short shell window,

or:

    the required charge D(n) grows too quickly.

Give a precise theorem statement for the first genuinely missing provider.

Do not summarize this merely as 'need more number theory'.

## Possible outcomes

### Outcome A — adaptive certificate provider advances materially

Both n=41 and n=91 are solved structurally, the charge-6 diagnostic budget
reduces the unresolved set, and at least one reusable CRT/support theorem is
added.

### Outcome B — explicit shells solved, CRT abstraction limited

41 and 91 are solved by three-seat certificates, but the CRT short-window
provider does not yet yield a useful reusable class theorem.

### Outcome P — precise CRT window bridge remains

The congruence-to-support and adaptive aggregation layers are complete, but
one explicit short-window CRT/candidate theorem remains before the provider
can generate certificates.

Use Outcome P only if that theorem can be stated exactly.

### Outcome C — CRT seat generation is the wrong provider

Short-window/parity/coprimality constraints make CRT-generated seats too sparse
or too expensive. Identify the alternative provider suggested by the data.

## Non-goals

Do not claim or attempt by default:

    Legendre's conjecture;
    uniform T=1;
    analytic prime-counting estimates;
    PNT or RH;
    FLT/ABC consequences.

Do not replace structural certificates by whole-shell direct evaluation.

Do not use sorryAx-bearing research endpoints in production proofs.

## Implementation guidance

Likely production homes:

    DkMath.NumberTheory.Legendre.ParitySafeExcessCertificate

for reusable witness aggregation, and a small new module such as

    DkMath/NumberTheory/Legendre/ParitySafeCRTSeat.lean

only if the CRT-to-support/candidate results are genuinely reusable.

Keep generic CRT lemmas in a neutral namespace when appropriate.

## Validation

For all new production declarations:

- focused builds;
- lake build DkMath.NumberTheory.Legendre;
- lake build DkMath;
- forbidden-token scan;
- #print axioms for all new public declarations;
- git diff --check.

All new production declarations must remain free of sorryAx.

## Durable checkpoint protocol

Update findings after:

- n=41 three-seat certificate;
- n=91 three-seat certificate;
- generic finite witness-family aggregation audit;
- congruence-to-active-support theorem;
- parity/candidate CRT audit;
- short-window CRT theorem or counterexample;
- adaptive charge consumer;
- charge-6 classification of previous unresolved shells;
- any infinite structural provider class;
- final A/B/P/C decision.

Preserve failed CRT window claims and smallest counterexamples.

## Final report

Answer explicitly:

1. Are the proposed three-seat certificates for 41 and 91 valid in production support?
2. What excess lower bounds and square-cell prime theorems result?
3. What generic theorem turns CRT congruences into active-support witnesses?
4. What exact conditions are required for a CRT residue to be an actual parity-safe candidate seat?
5. Is there a useful short-window existence theorem in terms of product(Q)?
6. Can multiple distinct CRT seats be generated with a proved total charge?
7. How many of the 30 previously unresolved shells are solved with charge <=6?
8. Which shells remain unresolved and what required charges do they have?
9. Is there a reusable infinite arithmetic-class provider?
10. What exact theorem remains between the adaptive certificate method and a uniform proof?

End with exactly one judgment:

    Outcome A — ADAPTIVE CERTIFICATE PROVIDER ADVANCES
    Outcome B — EXPLICIT SHELLS SOLVED, CRT GENERALIZATION LIMITED
    Outcome P — PRECISE CRT WINDOW BRIDGE REMAINS
    Outcome C — CRT SEAT GENERATION IS NOT THE RIGHT PROVIDER