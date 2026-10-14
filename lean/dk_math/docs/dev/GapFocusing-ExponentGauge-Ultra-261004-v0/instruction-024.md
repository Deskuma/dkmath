# Instruction 024 - Terminal prime product and source multiplicity bound

## Mission

Continue from Instruction 023.

Instruction 023 completed the deterministic packing and handoff route semantically:

- left retained seats are simultaneous maxima in all supporting prime fibers
- right retained seats are simultaneous minima
- missing directions are exactly directions with outgoing handoffs
- max handoffs strictly increase fiber maximum
- min handoffs strictly decrease fiber minimum
- both handoff relations are acyclic
- fixed-column continuation is unique under the existing vertical sparsity hypotheses
- branching is still possible
- better-of-two packing is exact
- no new universal loss bound follows from acyclicity or destination uniqueness alone

The exact route limitation is now clear:

The current theory does not bound how many distinct source primes can terminate at one deleted seat and hand off through one or more continuing primes.

Instruction 024 must attack that source multiplicity using the arithmetic size of the complete point.

For an operational initial world:

  S = primeScalesUpTo P

let a be a full-town seat.

Split the actual support at a into:

  terminal source primes:
    primes q whose fiber maximum is a

and:

  continuing primes:
    primes p whose fiber contains a and also a strictly larger seat.

At a left-deleted seat, the continuing set is nonempty and every terminal source prime is a missing active direction.

Because all support primes are distinct outside primes greater than P and all divide the same positive complete point:

  n^2 + a

their finite product divides that point.

The primary local target is stronger than the report-023 single-continuing-prime proposal:

  (P+1) ^ support(a).card
  <= product of support(a)
  <= n^2+a
  < (n+1)^2.

At a deleted seat:

  terminal.card + continuing.card = support(a).card
  continuing.card >= 1

so in particular:

  (P+1) ^ (terminal.card + 1) <= n^2+a.

This gives a genuine point-size upper bound on source branching.

The checkpoint must then aggregate terminal source counts over deleted seats and judge whether the local product bound yields any new symbolic or finite global loss bound beyond the existing support-excess accounting.

Do not assume it does.

All new instruction, findings, logs, and report artifacts must remain parser-safe plain text. Avoid backslash notation and LaTeX control sequences.

## Phase 0 - broad source audit

Audit at minimum:

DkMath.NumberTheory.Legendre.CoarseTownPrimeHandoff
DkMath.NumberTheory.Legendre.CoarseTownRetainedDirections
DkMath.NumberTheory.Legendre.CoarseTownSymmetricDeletion
DkMath.NumberTheory.Legendre.CoarseTownDeletionConservation
DkMath.NumberTheory.Legendre.CoarsePrimeWorldVerticalCapacity
DkMath.NumberTheory.Legendre.CoarsePrimeWorldFullTown
DkMath.NumberTheory.Legendre.Basic

DkMath.NumberTheory.PrimorialUniverse.FinitePrimeSynchronization
DkMath.NumberTheory.PrimitiveSet.RealLog
DkMath.Petal.ABCBridge

Search Mathlib and DkMath for:

- finite product lower bound from a pointwise lower bound
- product of pairwise coprime divisors divides a common multiple
- product of distinct prime divisors divides a natural number
- finite prime basis product divides a common multiple
- power monotonicity in the exponent
- Nat log or clog only if a clean exact API exists
- support cardinality from a power threshold
- sum of cards over a unique fiber partition
- maximum-fiber source partition
- terminal direction grouped by endpoint seat

Important reuse:

DkMath.NumberTheory.PrimitiveSet already contains:

  natProductDvdOn_of_pairwise_coprime_dvd
  natProductBoundOn_of_pairwise_coprime_dvd

DkMath.NumberTheory.PrimorialUniverse already contains:

  finitePrimeBasisProduct_dvd_of_commonMultiple

DkMath.Petal.ABCBridge contains a local 2^card product lower-bound pattern.

Do not import Petal into Legendre merely to reuse that local theorem.

If a generic base^card finite-product lemma is missing, place it in a neutral arithmetic or combinatorics location.

Record source-inventory-024.md before substantial production changes.

## Phase 1 - terminal source carrier at one seat

Define the left terminal-source carrier for one full-town seat a.

Suggested semantics:

  coarseTownTerminalPrimesAt S n a

is the subset of squareOffsetPrimeSupport n a consisting of q such that:

  coarseTownFiberMaximumAt S n q a.

Using actual support as the source carrier is preferred because it automatically keeps distinctness.

Prove exact membership:

  q in terminalAt(a)
  iff
  q in squareOffsetPrimeSupport n a
  and
  fiberMaximumAt q a.

For certified S and a in fullTown prove:

- terminalAt(a) subset coarseFullTownActivePrimes S n
- terminalAt(a) subset coarseOutsidePrimes S n.

## Phase 2 - continuing carrier equals deletion witnesses

Reuse:

  coarseTownDeletionWitnessPrimes S n a

as the continuing-prime carrier.

For a in fullTown prove exact support partition:

  terminalAt(a) union deletionWitnessPrimes(a)
  =
  squareOffsetPrimeSupport n a.

Prove disjointness.

Reason:

For each support prime q at a, either a is the maximum of its finite fiber or there exists a larger fiber seat.

Do not assume a is deleted for this partition.

Derive the exact card identity:

  terminal.card + continuing.card = support.card.

## Phase 3 - deleted-seat specialization

For certified S prove:

  a in coarseTownDeletionVertices S n
  iff
  continuing(a).Nonempty.

This should reuse:

  mem_coarseTownDeletionVertices_iff_multiplicity_pos

and the definition of deletionMultiplicity.

For a deleted seat prove:

- continuing.card >= 1
- every terminal prime at a is in coarseTownUnrepresentedActivePrimes S n.

The second theorem must use:

  terminal q has maximum at a
  a is deleted
  coarseTownMax_unrepresented_iff_deleted.

## Phase 4 - every missing direction has one terminal seat

For q in coarseTownUnrepresentedActivePrimes S n, its active fiber has a unique maximum a.

Prove:

- a belongs to coarseTownDeletionVertices S n
- q belongs to terminalAt(a).

Conversely, terminal primes at a deleted seat are missing.

Define a finite endpoint incidence if useful:

  coarseTownTerminalSourcePairs S n

containing pairs (a,q) where:

- a is deleted
- q is terminal at a.

Prove both projections have the exact intended semantics.

## Phase 5 - exact global source count by terminal seats

Prove the terminal fibers partition the missing active directions.

Primary exact identity:

  unrepresentedActive.card
  =
  sum over a in deletionVertices of terminalAt(a).card.

Use uniqueness of each active prime fiber maximum.

Do not replace this with an inequality.

If a biUnion equality is cleaner, prove:

  biUnion over deleted a of terminalAt(a)
  =
  unrepresentedActive

and prove the terminalAt sets for distinct seats are disjoint.

Then derive the cardinality sum.

This theorem is a central bridge from local source multiplicity to the global missing term in the 023 loss decomposition.

## Phase 6 - generic finite product lower bound

Audit before adding a new theorem.

If no suitable generic theorem exists, prove a neutral lemma:

For a Finset A of naturals, if:

  B <= x

for every x in A, then:

  B ^ A.card <= A.prod id.

No primality assumption should be needed.

Prefer Finset induction.

Do not reuse the Petal-local theorem through a reverse dependency.

Optionally provide a function-valued version only if useful elsewhere.

## Phase 7 - actual support is a finite prime basis

For any n and a prove or reuse:

Every q in squareOffsetPrimeSupport n a is prime.

Package:

  IsFinitePrimeBasis (squareOffsetPrimeSupport n a)

if that API is convenient.

Also prove every member divides:

  n^2+a.

Then reuse:

  finitePrimeBasisProduct_dvd_of_commonMultiple

or the PrimitiveSet pairwise-coprime product theorem to obtain:

  product of squareOffsetPrimeSupport n a divides n^2+a.

Prefer the existing finitePrimeBasisProduct theorem if its product is definitionally the support product.

Do not write a second induction proof unless dependency direction requires it.

## Phase 8 - exact support product bound

For a genuine square offset a prove positivity:

  0 < n^2+a.

From Phase 7 derive:

  product support(a) <= n^2+a.

For a in squareOffsets n also prove the standard shell upper bound:

  n^2+a < (n+1)^2.

Reuse SquareOffset arithmetic.

Package:

  product support(a) <= n^2+a < (n+1)^2.

The strict upper endpoint must remain exact.

## Phase 9 - initial-world lower bound on every support prime

Specialize to:

  S = primeScalesUpTo P.

For:

  a in coarsePrimeWorldFullTown S n

and:

  q in squareOffsetPrimeSupport n a

prove:

  P < q

and hence:

  P+1 <= q.

Use:

  coarseFullTown_survivor
  coarse_survivor_support_outside
  mem_primeScalesUpTo.

Do not use a next-prime theorem.

## Phase 10 - local exponent product bound

Combine Phases 6, 8 and 9.

For an initial world and a in fullTown prove:

  (P+1) ^ support(a).card
  <=
  product support(a)
  <=
  n^2+a
  <
  (n+1)^2.

This theorem is unconditional in full-cover status.

It is only a local arithmetic bound on one full-town seat.

## Phase 11 - terminal plus continuing product bound

Use the exact support partition to expose:

  support.card = terminal.card + continuing.card.

Then prove:

  (P+1) ^ (terminal.card + continuing.card)
  <= n^2+a.

For a deleted seat derive:

  (P+1) ^ (terminal.card + 1)
  <= n^2+a.

This is the strengthened form of the report-023 proposal.

Also prove the weaker explicit single-continuation form if useful:

If p belongs to continuing(a), then:

  p * product terminal(a) divides n^2+a.

And therefore:

  p * (P+1) ^ terminal.card <= n^2+a.

The full-support power inequality remains the preferred theorem.

## Phase 12 - exact terminal product divisibility

Independently of the lower bound, prove the exact divisibility statement:

  product terminal(a) * product continuing(a)
  divides n^2+a.

If the exact support partition gives equality to the full support product, reuse it.

For one continuing p prove:

  p * product terminal(a)
  divides n^2+a.

This exact divisibility is important evidence that the cardinality bound is not an accidental estimate.

## Phase 13 - power-threshold source-card bound

Avoid real logarithms in the primary theorem.

For natural k, derive a theorem of the following kind.

If:

  a is a deleted full-town seat
  (n+1)^2 <= (P+1)^(k+1)

then:

  terminalAt(a).card < k+1

or an equivalent clean bound such as:

  terminalAt(a).card <= k-1

under the exact boundary assumptions needed.

Choose the Nat statement that avoids awkward truncated subtraction.

Require enough hypotheses to make the power base strictly greater than 1.

For operational initial worlds, P may be 0 or 1 in tiny cases, so separate the boundary exactly.

Do not silently assume P+1 >= 2.

## Phase 14 - optional exact integer exponent gauge

Audit Mathlib Nat.log or Nat.clog APIs.

Only if the API is lightweight and exact, define a derived local source-capacity number whose semantics are proved by a power threshold.

Do not reuse StructuralArithmetic.PowerGauge for this purpose.

That existing module is exponent-mod-period projection and is semantically unrelated.

Do not introduce Real.log merely to state a finite Nat cardinality theorem.

A power-threshold theorem is sufficient.

## Phase 15 - global missing-direction bound from local capacities

Combine the exact source-count sum:

  missing.card
  =
  sum over deleted a of terminalAt(a).card

with a uniform local threshold bound.

If every deleted seat has:

  terminal.card <= k

derive:

  missing.card <= deletionVertices.card * k.

Also expose a nonuniform exact sum bound if a seat-dependent capacity is available.

Do not claim this improves the 023 loss bound until compared formally.

## Phase 16 - compare against support-excess accounting

The previous route already knows:

  left loss
  =
  missing.card + retainedSupportExcess.

Determine how the new source-product bound compares with the trivial local support relation:

  terminal.card + continuing.card = support.card.

In particular, at a deleted seat:

  terminal.card <= support.card - 1.

Summing this recovers an excess-like upper bound.

The new product theorem is only genuinely stronger where point size and the lower prime cutoff force:

  terminal.card

strictly below:

  support.card - 1

or below a bound obtainable from the existing incidence ledger.

Prove at least one theorem-level implication or strictness witness if available.

Do not claim novelty from a rephrased support-card bound.

## Phase 17 - operational world calibration

Run diagnostics over the same 602 operational worlds.

For each deleted seat record:

- n
- world and cutoff P
- seat a
- complete point n^2+a
- support card
- terminal source card
- continuing card
- product of terminal primes
- product of continuing primes
- full support product
- lower power (P+1)^support.card
- source threshold bound
- whether product-size improves the trivial support-card-minus-one bound

Aggregate per world:

- missing direction count
- maximum terminal source card
- number of multi-source terminal seats
- sum of terminal source cards
- product-derived global upper bound
- existing left loss
- better loss
- survivor capacity result.

Mandatory anchors:

  29
  297
  1031.

Preserve the 297 branching example where source 113 has multiple outgoing handoffs.

## Phase 18 - kernel regression of shared terminal seats

Kernel-check several actual shared-source or branching seats.

At minimum include:

- one smallest scanned seat with at least two terminal source primes if one exists
- n=297 source-sharing or branching calibration
- n=1031 a seat with large terminal multiplicity if available.

For each kernel regression verify actual:

- terminal carrier
- continuing carrier
- support partition
- exact product divisibility
- power lower bound.

Do not trust diagnostic factor lists without kernel reconstruction.

## Phase 19 - right minimum mirror audit

The local support product theorem is orientation-independent.

For right deletion, define a minimum-terminal source carrier only if needed:

  primes whose fiber minimum is a.

Prove the mirror partition with right deletion witnesses.

If this is cheap, derive the same product and threshold bounds for right missing directions.

If it duplicates a large amount of code, extract a neutral extremal-endpoint lemma or defer the full mirror.

Because better-of-two uses both orientations, a compact symmetric API is preferred if practical.

## Phase 20 - global better-of-two test

If both left and right source-capacity bounds are available, determine whether they give a symbolic upper bound on:

  coarseTownBetterLoss.

Remember:

  better loss
  =
  min(left loss,right loss).

The new product theorem directly controls only missing directions, not retained support excess.

Therefore a universal better-loss theorem also needs to account for retained excess.

Do not drop that term.

Test whether source multiplicity plus existing retained-excess identities yields any new strict survivor-capacity criterion.

## Phase 21 - possible stronger distinct-prime lower bound

The simple lower bound:

  every outside prime >= P+1

may be weak because the source primes are distinct.

Audit, but do not overbuild, a stronger finite bound using the actual smallest distinct primes above P.

Possible form:

For a finite set Q of distinct primes all above P, compare:

  product Q

with a canonical product of the first Q.card eligible primes above P.

Only implement this if an existing PrimeWorld or primorial API makes it light.

Do not introduce prime enumeration or analytic prime estimates solely for this checkpoint.

The simple power bound is the required baseline.

## Phase 22 - factor-budget relation to complete point support

Investigate whether the terminal and continuing partition gives more than a cardinality bound.

Possible exact consequences:

- every deleted seat contains at least one continuing prime and at least zero terminal primes
- a seat with t terminal sources and c continuing directions contains at least t+c distinct outside prime factors
- the complete point has a squarefree divisor equal to the full actual support product
- high source multiplicity consumes a large squarefree factor budget.

Compare with existing rough factorization census from Instructions 013 to 016.

Do not claim the rough sqrt-support bound applies to every full-town seat.

If a clean bridge to an existing factorization stratum exists, record it.

## Phase 23 - universal-provider judgment

This phase is mandatory and skeptical.

Determine whether the product bound yields any genuinely new symbolic statement of one of these forms:

A. a uniform upper bound on terminal source multiplicity that is stronger than support-card accounting and useful in the global missing-direction sum

B. a strict upper bound on missing active directions

C. a new bound on better loss after adding retained excess

D. a new deterministic survivor-capacity obstruction for anchors not already detected by 023

E. only a local arithmetic bound with no global improvement

Do not classify a finite restatement as a universal provider.

## Possible outcomes

Outcome A - TERMINAL PRODUCT YIELDS A NEW SYMBOLIC SOURCE BOUND

The point-size product theorem produces a genuinely stronger source-multiplicity or missing-direction bound that improves the symbolic loss frontier.

Outcome B - TERMINAL PRODUCT ADDS NEW FINITE CAPACITY POWER

The local product and source-count theorems are exact and produce new kernel-certified finite capacity results or stronger certificates, but no universal loss bound closes.

Outcome C - TERMINAL PRODUCT IS EXACT BUT GLOBALLY TOO WEAK

The local arithmetic theorem is correct, but aggregation collapses to or is weaker than existing support-excess accounting and adds no new capacity frontier.

Outcome P - ONE DISTINCT-PRIME PRODUCT BRIDGE REMAINS

The terminal-source semantics close, but one precise product-divisibility, power-threshold, or aggregation theorem blocks the judgment.

## Non-goals

Do not claim:

- Legendre conjecture
- that a product of arbitrary divisors divides their common multiple without coprimality
- that all support primes occur with valuation one
- that terminal source primes are consecutive primes above P
- a PNT or Bertrand estimate
- a universal logarithmic source bound without an exact Nat theorem
- that local source multiplicity alone controls retained support excess
- that the 023 deterministic packing limitation has already been overcome
- that StructuralArithmetic.PowerGauge is the same as this product-size exponent bound

Do not resume the Instruction 018 prime-power floor sum unless the product theorem explicitly requires valuation multiplicity. It should not.

## Suggested implementation surface

Possible modules:

DkMath/Combinatorics/FinsetProductBounds.lean
DkMath/NumberTheory/Legendre/CoarseTownTerminalProduct.lean
DkMath/NumberTheory/Legendre/CoarseTownSourceMultiplicity.lean

If existing PrimorialUniverse or PrimitiveSet product lemmas cover the generic layer cleanly, keep the new Legendre modules thin.

Keep finite calibration data in DkMathTest.

Update the Legendre facade only after focused builds are green.

## Validation

For all new production declarations:

- focused builds
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- forbidden-token scan
- print axioms for every new public declaration
- git diff --check

For finite calibrations:

- kernel-check actual carriers and products
- record computation cost
- reject any sorryAx dependency

Existing unrelated root sorry warnings may remain.

## Durable checkpoint protocol

Update findings after:

- source audit
- terminal carrier
- support terminal-continuing partition
- missing-direction endpoint partition
- exact global source-count sum
- generic product lower bound
- support product divisibility
- initial-world power lower bound
- deleted-seat source bound
- global aggregation
- finite diagnostics
- right mirror audit
- universal-provider judgment

Preserve false conjectures and smallest counterexamples.

## Final report

Answer explicitly:

1. What is the exact terminal-source carrier at one seat?
2. Is support exactly the disjoint union of terminal and continuing primes?
3. Is a seat deleted exactly when its continuing carrier is nonempty?
4. Are all terminal primes at a deleted seat missing active directions?
5. Does every missing active direction occur at exactly one deleted terminal seat?
6. Is missing.card exactly the sum of terminal-source cards over deleted seats?
7. Which existing product-divisibility theorem was reused?
8. Is the full actual support product proved to divide n^2+a?
9. Is the exact local inequality (P+1)^support.card <= n^2+a < (n+1)^2 proved for initial worlds?
10. Is the stronger deleted-seat inequality (P+1)^(terminal.card+1) <= n^2+a proved?
11. Is p times product terminal proved to divide n^2+a for a continuing p?
12. What exact Nat power-threshold theorem bounds terminal.card?
13. Was a logarithmic gauge avoided or used?
14. What global missing-direction bound follows after summing over terminal seats?
15. Is that bound genuinely stronger than terminal.card <= support.card-1 and the previous support-excess accounting?
16. What happens at n=297 and n=1031?
17. Was the right-minimum mirror implemented?
18. Does the product bound improve better-of-two loss or survivor capacity?
19. What smallest counterexample or limitation prevents a stronger aggregation if Outcome C?
20. What single theorem should be attempted next?

End with exactly one judgment:

Outcome A - TERMINAL PRODUCT YIELDS A NEW SYMBOLIC SOURCE BOUND
Outcome B - TERMINAL PRODUCT ADDS NEW FINITE CAPACITY POWER
Outcome C - TERMINAL PRODUCT IS EXACT BUT GLOBALLY TOO WEAK
Outcome P - ONE DISTINCT-PRIME PRODUCT BRIDGE REMAINS
