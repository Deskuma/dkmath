# Instruction 008 — Legendre hybrid provider: two-prime exclusion + local excess certificates

## Mission

Continue from Instruction 007.

Instruction 007 produced a full-cover-independent structural incidence upper bound

    I(n) <= B(n)

and a generic uncovered-deficit consumer

    A(n) + e(n) - B(n) <= U(n)

whenever e(n) is an independently proved lower bound on support excess.

For shell 21, B(21) < A(21) already gives U>0 with e=0.

For shell 29, however,

    B(29) = 31
    A(29) = 28,

so the upper-bound route alone does not force an uncovered candidate.

Instruction 007 identified two concrete local seats suggesting

    e(29) >= 4:

    29^2 + 14 = 855 = 3^2 * 5 * 19,
    29^2 + 56 = 897 = 3 * 13 * 23.

The purpose of this task is to build a reusable hybrid provider:

    sharpen B by multi-prime reduced-residue exclusion,
    and/or
    supply e by local multi-support certificates,

then prove

    A(n) + e(n) > B(n)

for new shells.

The first mandatory calibration is n=29.

## Required source audit

Audit at minimum:

    DkMath.NumberTheory.Legendre.ParitySafeIncidenceUpper
    DkMath.NumberTheory.Legendre.ParitySafeReducedResidue
    DkMath.NumberTheory.Legendre.ParitySafeMobiusOddCorrection
    DkMath.NumberTheory.Legendre.ParitySafeIncidenceBalance
    DkMath.NumberTheory.Legendre.ParitySafeFreshCost
    DkMath.NumberTheory.Legendre.ParitySafeBlockLocalization
    DkMath.NumberTheory.Legendre.ParitySafePrimeSupport
    DkMath.NumberTheory.Primitive

and any existing prime-factor / Finset APIs already used in production.

Record exact theorem names and types before adding new abstractions.

## Phase 1 — two-prime inclusion-exclusion for reduced quotient intervals

Instruction 007 used one odd prime divisor d of n to remove odd quotient values divisible by d.

Now let d and e be distinct odd primes dividing n.

For one q-wave, write the odd raw quotient interval count as O and the odd-multiple exclusion counts as Delta_d, Delta_e, and Delta_de.

Prove the Nat-safe inclusion-exclusion bound corresponding to

    reducedQuotient.card
      <= O - |multiples of d union multiples of e|

with

    |D union E| = Delta_d + Delta_e - Delta_(d*e).

An equivalent subtraction-normalized form is acceptable.

Do not assume exact equality with the reduced quotient interval; other prime divisors of n may exclude additional points.

Prefer a generic finite-set theorem first, then specialize to the quotient interval.

## Phase 2 — pairwise exclusion upper cap

For each active q, define or derive a two-prime exclusion cap by minimizing over admissible distinct odd prime divisors d,e of n.

Then combine it with the existing caps:

    spacing cap,
    odd-endpoint cap,
    one-prime exclusion cap.

The resulting per-wave cap should be the minimum of all proved upper bounds.

Call the new shell incidence upper bound B2(n) only if a new definition is actually useful.

Required theorem shape:

    paritySafeIncidenceCount n <= B2(n).

Also prove

    B2(n) <= B(n)

where B is the Instruction 007 upper bound.

A strict inequality for at least one regression shell is required before calling this a genuine upper-bound gain.

## Phase 3 — explain the residual overestimation from Instruction 007

Use the six overestimated waves recorded in report-007 as diagnostics.

In particular inspect:

    (n,q) = (21,5)
    (30,11)
    (35,3)
    (39,7)
    (39,11)
    (39,17).

Determine which are corrected by two-prime exclusion and which remain loose.

Do not use actual wave cardinalities in production proofs of the generic cap.

Exact wave evaluation is allowed only as regression/diagnostic evidence.

## Phase 4 — reusable local excess certificate

Build the smallest useful theorem for proving a lower bound on

    paritySafeSupportExcess n

from finitely many candidate seats with known active-support cardinality lower bounds.

A desired local fact is:

    if r is a candidate and activeSupport.card >= k+1,
    then its local excess contribution is >= k.

Then aggregate over a pairwise-distinct finite seat set R:

    sum_{r in R} local lower costs <= paritySafeSupportExcess n.

Do not introduce a duplicate global excess ledger.

If an existing Finset sum-subset theorem is sufficient, reuse it.

## Phase 5 — n=29 excess certificate

Formalize the two explicit seats from report-007 using actual production active support:

    r = 14:
      point = 855,
      admissible support should contain 3,5,19;

    r = 56:
      point = 897,
      admissible support should contain 3,13,23.

Check all production conditions exactly:

    candidate membership,
    prime,
    q <= 29,
    q != 2,
    q does not divide 29,
    q divides 29^2 + r.

Then prove each seat contributes at least 2 support excess and derive

    4 <= paritySafeSupportExcess 29.

Do not replace the proof by direct evaluation of the entire excess sum.

## Phase 6 — hybrid uncovered theorem for n=29

Combine:

    A(29) = 28,
    structural incidence upper bound (prefer the new B2),
    e(29) >= 4,

with the generic uncovered-deficit theorem.

Target:

    0 < (paritySafeUncoveredCandidates 29).card.

Then consume it through the existing prime-square-cell bridge to obtain

    exists p, Prime p and 29^2 < p < 30^2.

This theorem must not depend on direct evaluation of the actual incidence count I(29).

## Phase 7 — define the hybrid gap only if useful

For diagnostics it is useful to think in terms of

    G(n) = A(n) + e(n) - B2(n).

Do not create a production definition G unless it materially simplifies reusable theorems.

The theorem-level criterion should be something like:

    if B2(n) < A(n) + e and e <= supportExcess(n),
    then uncoveredCandidates(n).Nonempty.

Prefer this generic implication over hard-coding any shell.

## Phase 8 — bounded diagnostic classification

Use a moderate finite range only as diagnostics, for example shells 2 through 100 or another range justified by runtime.

For each n classify whether it is defeated by:

    Class 0: B2(n) < A(n) with e=0;
    Class 1: B2(n) >= A(n), but a small explicit local excess certificate closes the gap;
    Class 2: still unresolved by these providers.

Do not turn a finite scan into a theorem about all n.

Record the unresolved n and their arithmetic types:

    prime n,
    prime power,
    product of two odd primes,
    highly composite,
    powers of 2 times odd part,
    or another exact classification suggested by the data.

The purpose is to discover which provider is missing for uniform Legendre.

## Phase 9 — provider theorem for a structural arithmetic class

If the diagnostics reveal a natural infinite arithmetic class for which the hybrid method always works, attempt a theorem.

Examples to investigate, not assume:

    n having at least two distinct odd prime divisors;
    n with a sufficiently small odd divisor;
    n with a candidate seat forced to have three admissible active primes;
    n where the two-prime exclusion cap alone gives B2<A.

Only formalize a class theorem if its hypotheses are explicit and the proof is elementary within the current stack.

Do not overgeneralize from the finite scan.

## Phase 10 — prime / prime-power obstruction audit

Two-prime divisor exclusion weakens when n has few odd prime divisors.

Explicitly inspect the hard structural classes:

    n prime;
    n = p^k;
    n = 2^a;
    n = 2^a p^k.

Determine whether local excess certificates can compensate, or whether a different reduced-residue exclusion source is needed.

Give one precise missing theorem if these classes remain the uniform obstruction.

## Possible outcomes

### Outcome A — hybrid provider gains new shells

n=29 is proved by structural upper bound plus local excess, and at least one reusable hybrid theorem or strictly sharper B2 upper bound is added.

Preferably the unresolved finite diagnostic set shrinks materially.

### Outcome B — n=29 solved, but provider does not generalize

The explicit excess certificate proves the n=29 shell, but no meaningful structural class or improved general cap emerges.

### Outcome P — one exact provider bridge remains

The two-prime cap and local excess machinery are formalized, but one explicit theorem is still missing to prove n=29 or the first intended class.

Use Outcome P only if the missing theorem can be stated precisely.

### Outcome C — hybrid route is not the right next abstraction

Two-prime exclusion and local excess certificates remain too shell-specific to improve the uniform frontier.

Identify the stronger invariant/provider suggested by the failures.

## Non-goals

Do not claim:

    Legendre's conjecture;
    uniform T=1;
    analytic prime estimates;
    PNT/RH machinery;
    FLT/ABC consequences.

Do not use exact whole-shell incidence evaluation as a substitute for the structural upper theorem.

Do not use sorryAx-bearing research endpoints in production proofs.

## Implementation guidance

Likely homes:

    DkMath.NumberTheory.Legendre.ParitySafeIncidenceUpper

for multi-prime quotient exclusions, and either

    DkMath.NumberTheory.Legendre.ParitySafeIncidenceBalance

or a small new module such as

    DkMath/NumberTheory/Legendre/ParitySafeExcessCertificate.lean

for reusable local excess aggregation.

Only create a new production module if it contains reusable mathematics.

## Validation

For all new production declarations:

- focused builds;
- lake build DkMath.NumberTheory.Legendre;
- lake build DkMath;
- forbidden-token scan;
- #print axioms for all new public declarations;
- git diff --check.

All new production declarations must be free of sorryAx.

## Durable checkpoint protocol

Update findings after:

- two-prime inclusion-exclusion finite-set lemma;
- per-wave two-prime cap;
- comparison B2<=B;
- six-wave diagnostic audit;
- reusable local excess certificate;
- n=29 explicit two-seat certificate;
- n=29 uncovered/prime theorem;
- bounded classification of remaining shells;
- any structural arithmetic-class provider;
- final A/B/P/C decision.

Preserve failed cap formulas and minimal counterexamples.

## Final report

Answer explicitly:

1. What exact two-prime inclusion-exclusion inequality was proved?
2. How much does B2 improve the Instruction 007 upper bound?
3. Which of the six previously loose waves are corrected?
4. What reusable theorem turns local support-card lower bounds into global support excess?
5. Is e(29)>=4 proved structurally from r=14 and r=56?
6. Is shell 29 proved to contain an uncovered candidate and a prime in (29^2,30^2)?
7. In the diagnostic range, which shells remain unresolved by B2 plus small local excess certificates?
8. What arithmetic classes characterize the unresolved shells?
9. Is there a reusable infinite-class provider, or what exact theorem is still missing?
10. How far is the hybrid criterion from a uniform proof of A(n)+e(n)>B2(n)?

End with exactly one judgment:

    Outcome A — HYBRID PROVIDER GAINS NEW SHELLS
    Outcome B — N=29 SOLVED, LIMITED GENERALIZATION
    Outcome P — PRECISE HYBRID PROVIDER BRIDGE REMAINS
    Outcome C — HYBRID ROUTE IS TOO SHELL-SPECIFIC