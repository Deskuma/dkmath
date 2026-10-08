# Instruction 022 - Survivor-world capacity and prime-fiber deletion conservation

## Mission

Continue from Instruction 021.

Instruction 021 completed:

- exact first-endpoint deletion carrier D
- exact deterministic remainder R
- V.card = R.card + D.card
- kernel endpoint at n=1031 from the deterministic deletion route
- kernel endpoint at n=297 from an explicit 63-seat certificate
- optional explicit 233-seat certificate at n=1031
- a Boolean checker that recomputes actual bounded divisibility

The next checkpoint must explain why deterministic deletion succeeds, rather than merely add more explicit certificates.

A new structural observation is mandatory:

Every seat of coarsePrimeWorldFullTown S n is an S-survivor.

Therefore every actual bounded old-prime support of such a seat is contained not merely in primeScalesUpTo n, but in the smaller world:

  T = coarseOutsidePrimes S n
    = primeScalesUpTo n minus S.

Hence a pairwise old-support-disjoint family contained in the full town has full-cover capacity at most T.card, not merely primeScalesUpTo n.card.

This sharper survivor-world capacity was not exposed in Instructions 020 or 021.

It immediately gives a new acceptance target:

At n=297 with the operational initial world S=primeScalesUpTo 10:

  V.card = 96
  right deletion remainder card = 60
  old prime count = 62
  outside prime count = 58

Thus the old capacity comparison 60 <= 62 did not contradict full cover, but the correct survivor-world comparison 60 > 58 should.

Instruction 022 must first formalize this sharper capacity.

Then it must expose the prime-fiber conservation underlying first-endpoint deletion.

The preferred exact additive conservation is:

  R.card + X = U.card + A.card + O

where:

  V = coarsePrimeWorldFullTown S n
  R = deterministic first-endpoint packing remainder
  U = seats in V with empty actual old support
  A = active outside primes with nonempty full-town fiber
  X = seat-side support excess
  O = deletion multiplicity overlap

Under full cover, U.card = 0, giving:

  R.card + X = A.card + O.

Do not use Nat subtraction as the primary theorem when an additive equality is available.

The research question is:

Does the overlap O forced by PrimeWorld periodic geometry systematically compensate for support excess X strongly enough to create a symbolic full-cover obstruction?

Let Lean judge.

All new instruction, findings, logs, and report artifacts must remain parser-safe plain text. Avoid backslash notation and LaTeX control sequences.

## Phase 0 - broad source audit

Audit at minimum:

DkMath.NumberTheory.Legendre.CoarseTownDeletionCapacity
DkMath.NumberTheory.Legendre.CoarseTownSupportPacking
DkMath.NumberTheory.Legendre.CoarsePrimeWorldVerticalCapacity
DkMath.NumberTheory.Legendre.CoarsePrimeWorldFullTown
DkMath.NumberTheory.Legendre.CoarsePrimorialTown
DkMath.NumberTheory.Legendre.OldSupportCapacity
DkMath.NumberTheory.Legendre.OldSupportCapacityCertificate
DkMath.NumberTheory.Legendre.Wave
DkMath.NumberTheory.Legendre.PairOverlap
DkMath.NumberTheory.Legendre.ParitySafeIncidenceBalance
DkMath.Combinatorics.FinsetSupportPacking

Search repository-wide for:

- generic pairwise-disjoint family capacity inside a smaller support universe
- support incidence equals sum of fiber cards
- support excess conservation
- nonempty fiber count
- active prime count
- double counting of finite relations
- max or sup of a nonempty Finset
- filter below maximum
- card of all nonmaximum elements
- deletion multiplicity
- overlap excess
- incidence minus active directions
- left and right endpoint deletion comparisons

Record exact reusable theorem names in source-inventory-022.md.

Do not duplicate an existing incidence or excess API if a thin full-town adapter suffices.

## Phase 1 - generic finite support-universe capacity lemma

Prefer a neutral theorem rather than duplicating OldSupportCapacity arithmetic.

For finite:

  R : Finset alpha
  f : alpha -> Finset beta
  T : Finset beta

assume:

- every f r is nonempty for r in R
- every f r is a subset of T
- the family f over R is pairwise disjoint

Prove:

  R.card <= T.card.

The proof should use the disjoint biUnion cardinality exactly.

If an equivalent Mathlib or DkMath theorem already exists, reuse it.

This is a finite combinatorial capacity theorem, independent of Legendre.

## Phase 2 - survivor-world capacity inside the full town

Specialize Phase 1 to:

  V = coarsePrimeWorldFullTown S n
  f a = squareOffsetPrimeSupport n a
  T = coarseOutsidePrimes S n.

Assume:

  hS : KnownPrimeScales S
  R subset V
  PairwiseOldSupportDisjointSquareSeatFamily n R
  SquareOffsetsFullyCovered n.

Use:

  coarseFullTown_survivor
  coarse_survivor_support_outside

to prove:

  R.card <= (coarseOutsidePrimes S n).card.

Suggested theorem shape:

  card_fullTown_pairwiseOldSupportDisjoint_le_outsidePrimes_of_fullyCovered

Do not fall back to primeScalesUpTo n.card in the proof.

## Phase 3 - survivor-world capacity consumers

Derive the strict obstruction:

If:

  R subset fullTown
  PairwiseOldSupportDisjointSquareSeatFamily n R
  coarseOutsidePrimes S n.card < R.card

then:

  not SquareOffsetsFullyCovered n.

For positive n, route to the existing Frontier escape theorem or OldSupportCapacity prime endpoint:

  exists p, Nat.Prime p and SquareCell n p.

Prefer one small specialized consumer built from the new generic support-universe capacity lemma.

Do not duplicate prime existence arithmetic.

## Phase 4 - stronger deletion-deficit criterion

Apply Phase 3 to the deterministic left remainder.

Using:

  V.card = R.card + D.card

derive:

If:

  T.card + D.card < V.card

then:

  not SquareOffsetsFullyCovered n.

For positive n derive a square-cell prime endpoint.

This theorem is strictly stronger than the 021 criterion:

  primeScalesUpTo n.card + D.card < V.card

whenever S contains at least one old prime.

Prove the implication from the old criterion to the new one using:

  T subset primeScalesUpTo n.

Preserve strictness witnesses.

## Phase 5 - right deletion specialization

Instruction 021 proved the generic right-endpoint deletion packet.

Expose the Legendre specialization if not already public:

  coarseTownRightDeletionVertices S n
  coarseTownRightPackingRemainder S n.

Prove:

- right remainder subset fullTown
- PairwiseOldSupportDisjointSquareSeatFamily
- exact partition V.card = Rright.card + Dright.card
- survivor-world deletion-deficit consumer using T.card

Do not create a second collision relation.

## Phase 6 - deterministic n=297 endpoint from survivor-world capacity

Use:

  n = 297
  S = primeScalesUpTo 10.

Kernel-check the required production quantities.

Expected diagnostic values:

  M = 210
  K = 2
  V.card = 96
  T.card = 58
  left remainder card = 57
  right remainder card = 60
  right deletion card = 36.

Then prove a separately named endpoint using only:

- production full-town geometry
- generic right deletion
- survivor-world capacity
- kernel-evaluated finite cards

Conclusion:

  exists p, Nat.Prime p and SquareCell 297 p.

This must be independent of the explicit 63-seat search certificate from Instruction 021.

Preserve both proof routes by name.

This is a primary acceptance target.

## Phase 7 - deterministic n=1031 survivor-world endpoint

Reprove or add a thin stronger-route calibration at:

  n = 1031
  S = primeScalesUpTo 10.

Expected:

  T.card = 169
  left remainder card = 216.

The existing old-world endpoint already uses 173 as the capacity.

Show the sharper survivor-world consumer closes with 169.

Keep the original 021 endpoint intact for provenance.

This calibration is cheap once the cardinalities are available.

## Phase 8 - optional better-of-two deletion packet

If clean, define a transparent deterministic choice between left and right remainder based only on their cardinalities.

Possible semantics:

  choose the remainder with larger card

or equivalently:

  choose the deletion carrier with smaller card.

Prove:

- chosen remainder subset V
- pairwise support-disjointness
- chosen remainder card = max(left.card, right.card)
- chosen deletion cost = min(leftDeletion.card, rightDeletion.card)

Do not claim optimality among all support packings.

Use this packet only if it simplifies capacity statements.

## Phase 9 - active outside prime carrier

Define:

  coarseFullTownActivePrimes S n

as outside primes q in T whose:

  coarseFullTownPrimeFiber S n q

is nonempty.

Prove exact membership:

  q in Active
  iff
  q in T and coarseFullTownPrimeFiber S n q is nonempty.

Prove:

  Active subset T
  Active.card <= T.card.

Do not define activity over all naturals.

## Phase 10 - full-town uncovered seats

Define:

  coarseFullTownUncoveredSeats S n

as seats a in V with:

  squareOffsetPrimeSupport n a = empty

or equivalent support card zero.

Prove exact membership and:

Under:

  SquareOffsetsFullyCovered n

the uncovered carrier is empty.

Conversely, because every fullTown seat is a genuine SquareOffset, empty support means that seat is not covered.

If useful, prove:

  uncovered empty
  iff
  every fullTown seat is covered

but do not confuse this with full cover of the entire shell.

## Phase 11 - full-town support excess

Define:

  coarseFullTownSupportExcess S n
  =
  sum over a in V of
    squareOffsetPrimeSupport n a.card - 1.

Nat subtraction at zero contributes zero.

Reuse the pattern from squareCoverOverlapExcess or ParitySafeIncidenceBalance if available.

Prove the exact seat-side conservation:

  coarseFullTownIncidence S n
  + uncovered.card
  =
  V.card
  + supportExcess.

This is the local full-town analogue of the existing incidence/excess ledgers.

Prefer a pointwise identity by support card 0 versus positive.

## Phase 12 - nonmaximum prime-fiber seats

For each outside prime q define the seats of its fiber that are not maximal in seat order.

Prefer an exact definition using the existing fiber:

  Fq = coarseFullTownPrimeFiber S n q.

Possible representation:

  Fq.filter (fun a => exists b in Fq, a < b)

This avoids max-default boundary issues.

Prove:

If Fq is nonempty:

  nonmaximumFiberSeats.card + 1 = Fq.card.

If Fq is empty:

  nonmaximumFiberSeats.card = 0.

Package an unconditional additive identity:

  nonmaximumFiberSeats.card
  + indicator(Fq nonempty)
  =
  Fq.card.

Use Bool or if-expression only if it keeps summation clean.

## Phase 13 - deletion witness primes at one seat

For each full-town seat a define:

  coarseTownDeletionWitnessPrimes S n a

as outside primes q such that:

- a belongs to Fq
- there exists b in Fq with a < b.

Define:

  coarseTownDeletionMultiplicity S n a
  =
  card of that witness-prime set.

Prove:

  a in coarseTownDeletionVertices S n
  iff
  0 < deletionMultiplicity a.

Also prove equivalence to the existing fiber-compressed deletion carrier from Instruction 021.

This is an exact semantic theorem, not a new deletion algorithm.

## Phase 14 - deletion incidence double count

Define, if useful, a finite relation carrier of pairs:

  (a,q)

where q is a deletion witness prime for a.

Double-count it in two directions.

Seat side:

  card = sum over a in V of deletionMultiplicity a.

Prime side:

  card = sum over q in T of nonmaximumFiberSeats(q).card.

Using Phase 12, derive the exact additive identity:

  deletionMass + Active.card = coarseFullTownIncidence S n

where:

  deletionMass
  =
  sum over a in V of deletionMultiplicity a.

Do not state this as incidence minus Active in the primary API.

## Phase 15 - deletion overlap excess

Define:

  coarseTownDeletionOverlap S n
  =
  sum over a in coarseTownDeletionVertices S n of
    deletionMultiplicity a - 1.

Because deleted seats have positive multiplicity, prove:

  D.card + deletionOverlap = deletionMass.

This is the exact compression gain from union-counting repeated deletion witnesses.

Interpretation:

- deletionMass counts prime-by-prime nonmaximum incidences
- D.card counts distinct deleted seats
- deletionOverlap measures repeated deletion charges landing on the same seat

Do not confuse deletionOverlap with support collision edge count.

## Phase 16 - prime-fiber deletion conservation

Combine Phases 14 and 15 to prove:

  D.card + deletionOverlap + Active.card
  =
  coarseFullTownIncidence S n.

This is one central target theorem.

Use only exact finite counting.

## Phase 17 - master remainder conservation

Combine:

1. exact deletion partition:
   V.card = R.card + D.card

2. seat incidence conservation:
   incidence + U.card = V.card + X

3. prime-fiber deletion conservation:
   D.card + O + A.card = incidence

Cancel the common D term and prove the additive master identity:

  R.card + X
  =
  U.card + A.card + O.

This theorem should be unconditional.

Suggested conceptual name:

  coarseTownPackingRemainder_add_supportExcess_eq_uncovered_add_active_add_deletionOverlap

A shorter repository-consistent name is acceptable.

Do not hide any term through Nat subtraction.

## Phase 18 - full-cover specialization

Under:

  SquareOffsetsFullyCovered n

prove U.card = 0 and therefore:

  R.card + X = A.card + O.

This is the exact structural explanation of deterministic deletion under hypothetical full cover.

Also prove:

  A.card <= T.card.

Hence a sufficient contradiction criterion is:

  T.card + X < A.card + O.

Under this inequality full cover is impossible.

For positive n route to a square-cell prime.

This criterion may be more useful symbolically than direct computation of D.card.

## Phase 19 - slack decomposition

Define or derive a report-level exact relation between survivor-world capacity slack and overlap versus excess.

Under full cover:

  R.card <= T.card

and:

  R.card + X = A.card + O.

Therefore:

  O <= X + (T.card - A.card)

in a Nat-safe additive form.

Prefer:

  A.card + O <= T.card + X.

Prove this as a necessary full-cover inequality.

Then expose its strict negation as an obstruction:

  T.card + X < A.card + O
  implies not full cover.

This is the main symbolic frontier produced by the conservation law.

## Phase 20 - compare with direct deletion deficit

Determine whether the conservation obstruction is exactly equivalent to:

  T.card + D.card < V.card

or merely sufficient.

Because all terms are exact and derived from the same deterministic remainder, an exact equivalence may be available after eliminating R.

Audit carefully.

If equivalent, prove the equivalence and explain that the conservation theorem changes the arithmetic coordinates rather than strengthening the deterministic selector by itself.

That is still valuable because it isolates the missing term:

  deletion overlap versus support excess plus inactive outside directions.

Do not falsely claim a stronger obstruction if it is only a reparameterization.

## Phase 21 - finite diagnostics for conservation terms

Extend the existing 602-row scan.

For each world record at least:

- V.card
- T.card
- Active.card
- U.card
- incidence
- support excess X
- Dleft.card
- Rleft.card
- deletion mass
- deletion overlap O
- inactive outside count T.card - Active.card
- O - X where meaningful in signed diagnostics
- conservation residual, which must be exactly zero

For right deletion, optionally record the analogous minimum-fiber overlap terms if implemented.

Mandatory anchors:

  5
  11
  19
  29
  297
  1031

Use integers in diagnostics for signed slack only; production theorems should remain Nat-safe.

## Phase 22 - kernel calibrations of the conservation law

Kernel-check the full master identity numerically at several anchors.

At minimum:

- one collision-free example
- one example with deletion overlap zero
- one example with positive deletion overlap
- n=297 initial
- n=1031 initial

Do not kernel-evaluate every 602-row identity if unnecessary.

The 32GB build environment is available, so finite checks may use substantial memory when justified.

Still prefer symbolic rewriting over brute-force expansion where possible.

## Phase 23 - structural analysis of n=1031 overlap

For n=1031 initial, report the exact or kernel-checked values if affordable:

- Active.card
- U.card
- incidence
- X
- deletion mass
- O
- D.card
- R.card.

Explain exactly how:

  R.card + X = U.card + A.card + O

balances.

Determine whether the observed half-town remainder R.card=216 comes from a simple equality among these terms or is accidental.

Do not promote a half-town theorem without evidence.

## Phase 24 - structural analysis of n=297

For n=297 initial:

- left deterministic remainder has 57 seats
- right deterministic remainder has 60
- explicit greedy certificate has 63
- T.card is expected to be 58

Kernelize the right-deletion survivor-world endpoint first.

Then analyze why left deletion misses while right succeeds.

If a simple min/max fiber asymmetry explains the difference, record it as a candidate theorem.

Do not let the search-found 63-seat family obscure the deterministic 60-seat result.

## Phase 25 - optional symmetric right-fiber conservation

Left deletion retains fiber maxima.

Right deletion retains fiber minima.

If the left conservation is clean, mirror it for right deletion only if the additional code is small.

The active-prime and support-excess terms are common.

The only changed term is the right deletion overlap.

This may allow a better-of-two conservation criterion:

  choose the larger of the two overlap terms

or equivalently the smaller deletion cost.

Do not overgeneralize to arbitrary orientations yet.

## Phase 26 - next universal-provider judgment

The report must determine which symbolic term is now the actual frontier.

Possible next targets:

A. Lower bound deletion overlap O from periodic column geometry.

B. Upper bound support excess X from vertical wave occupancy.

C. Bound inactive outside directions T.card - A.card.

D. Cross-column theorem forcing repeated deletion witnesses on the same seats.

E. Better deterministic fiber selector beyond maxima and minima.

The preferred next theorem should attack the exact inequality exposed by Phase 19.

Do not return to the Instruction 018 prime-power floor sum unless it controls one of these terms directly.

## Possible outcomes

Outcome A - SURVIVOR-WORLD CAPACITY ADDS NEW DETERMINISTIC ENDPOINTS

The outside-prime capacity is formalized and adds at least one new deterministic kernel endpoint, with n=297 as the primary target. The conservation law also closes.

Outcome B - PRIME-FIBER CONSERVATION EXPOSES A NEW SYMBOLIC FRONTIER

The exact survivor-world capacity and conservation law are proved, but no new deterministic endpoint beyond existing certificates is obtained.

Outcome C - CONSERVATION IS EXACT BUT ONLY REPARAMETERIZES DELETION

The identities are correct but provide no useful new capacity coordinate or endpoint.

Outcome P - ONE DOUBLE-COUNTING BRIDGE REMAINS

Survivor-world capacity closes, but one precise incidence, active-fiber, or overlap identity blocks the master conservation.

## Non-goals

Do not claim:

- Legendre conjecture
- optimality of left or right deletion
- maximum independent set
- that all outside primes are active
- that deletion overlap is automatically large
- that support excess is automatically small
- independence of prime waves
- asymptotic density estimates
- PNT, RH, Bertrand, or analytic sieve bounds
- that the conservation obstruction is stronger than deletion deficit unless equivalence or strictness is proved

Do not replace actual support with precomputed labels.

Do not use Python diagnostics as theorem premises.

## Suggested implementation surface

Possible modules:

DkMath/Combinatorics/FinsetSupportPacking.lean
  only for the neutral support-universe capacity lemma if it belongs there

DkMath/NumberTheory/Legendre/CoarseTownSurvivorCapacity.lean
DkMath/NumberTheory/Legendre/CoarseTownDeletionConservation.lean

Reuse:
CoarseTownDeletionCapacity
CoarsePrimeWorldVerticalCapacity
OldSupportCapacity

Keep large finite calibrations under DkMathTest according to repository convention.

Update the Legendre facade only after focused builds are green.

## Validation

For all new production declarations:

- focused builds
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- forbidden-token scan
- print axioms for every new public declaration
- git diff --check

For n=297 and n=1031 deterministic calibrations:

- record exact card evaluations
- record proof route
- reject any sorryAx dependency

Existing unrelated root sorry warnings may remain.

## Durable checkpoint protocol

Update findings after:

- generic support-universe capacity
- full-town survivor-world capacity
- left deletion outside-world consumer
- right deletion specialization
- n=297 deterministic endpoint
- active prime carrier
- uncovered carrier
- support excess
- nonmaximum fiber seats
- deletion witness multiplicity
- deletion double count
- deletion overlap
- master conservation
- full-cover specialization
- conservation obstruction
- bounded diagnostics
- final A/B/C/P judgment

Preserve false conjectures and smallest counterexamples.

## Final report

Answer explicitly:

1. What generic support-universe capacity theorem was proved?
2. Why is T=coarseOutsidePrimes S n the correct capacity universe for fullTown families?
3. What sharper full-cover bound replaces R.card <= primeScalesUpTo n.card?
4. What exact left-deletion deficit theorem uses T.card?
5. Was the right-deletion specialization exposed?
6. Was n=297 kernel-certified by deterministic right deletion without the explicit 63-seat search certificate?
7. What is the corresponding deterministic n=1031 survivor-world endpoint?
8. How are Active, Uncovered, SupportExcess, deletionMultiplicity, and deletionOverlap defined?
9. Was deletionMass + Active.card = incidence proved exactly?
10. Was D.card + deletionOverlap = deletionMass proved exactly?
11. Was the master identity R.card + X = U.card + A.card + O proved?
12. What does it become under full cover?
13. What necessary full-cover inequality involving T, X, A, and O was proved?
14. Is that conservation obstruction equivalent to the direct deletion deficit or genuinely stronger?
15. What are the exact conservation values at n=297 and n=1031?
16. Did the right versus left asymmetry reveal a useful structural rule?
17. What single symbolic inequality should be attacked next?

End with exactly one judgment:

Outcome A - SURVIVOR-WORLD CAPACITY ADDS NEW DETERMINISTIC ENDPOINTS
Outcome B - PRIME-FIBER CONSERVATION EXPOSES A NEW SYMBOLIC FRONTIER
Outcome C - CONSERVATION IS EXACT BUT ONLY REPARAMETERIZES DELETION
Outcome P - ONE DOUBLE-COUNTING BRIDGE REMAINS
