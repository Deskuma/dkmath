# Instruction 023 - Retained-direction loss and symmetric fiber handoff

## Mission

Continue from Instruction 022.

Instruction 022 established two important facts.

First, the correct support-capacity universe for the full-period town is:

  T = coarseOutsidePrimes S n

rather than all primeScalesUpTo n.

This produced a new deterministic n=297 endpoint from the right deletion remainder.

Second, the exact left-deletion conservation is:

  R + X = U + A + O

with:

  R = left deterministic remainder card
  X = full-town support excess
  U = uncovered town seats
  A = active outside-prime directions
  O = left deletion overlap.

Lean also proved unconditionally:

  O <= X.

Therefore the proposed uncovered-free inequality cannot become a provider.

Define the exact left loss:

  L = X - O.

Then:

  R + L = U + A

and the direct survivor-world deficit is exactly:

  L + (T - A) < U.

The next checkpoint must explain L structurally.

The key expected interpretation is:

  left loss
  =
  unrepresented active directions
  +
  support excess remaining inside the retained family.

For each active prime q, consider the maximum seat of its full-town fiber.

A left-retained seat is exactly a seat that is maximal in every prime fiber supporting it.

If the maximum q-seat is deleted, then some other prime p also supports that seat and continues to a strictly larger seat.

This gives a directional handoff:

  q -> p

whose fiber maximum strictly increases.

The right deletion has the mirror picture using fiber minima and decreasing handoffs.

Instruction 023 must formalize these semantics, expose a transparent better-of-two selector, and test whether handoff geometry gives a genuinely new symbolic bound or only a new coordinate system.

Do not claim a universal Legendre provider merely from the exact identities.

All new instruction, findings, logs, and report artifacts must remain parser-safe plain text. Avoid backslash notation and LaTeX control sequences.

## Phase 0 - source audit

Audit at minimum:

DkMath.NumberTheory.Legendre.CoarseTownDeletionConservation
DkMath.NumberTheory.Legendre.CoarseTownSurvivorCapacity
DkMath.NumberTheory.Legendre.CoarseTownDeletionCapacity
DkMath.NumberTheory.Legendre.CoarsePrimeWorldVerticalCapacity
DkMath.NumberTheory.Legendre.CoarsePrimeWorldFullTown
DkMath.NumberTheory.Legendre.OldSupportCapacity
DkMath.Combinatorics.FinsetSupportPacking

Search repository-wide for:

- retained support union
- support biUnion cardinality
- finite fiber maximum and minimum
- maximum element membership
- directed acyclic finite relations
- rank-increasing finite relation
- terminal vertices
- functional graph or successor chains
- min and max endpoint packing
- max-card choice between two Finsets
- card max and min identities
- cross-column repeated-prime gap theorems

Record reusable declarations and avoided duplicates in source-inventory-023.md.

## Phase 1 - retained supported seats

For the left deterministic remainder define:

  coarseTownRetainedSupportedSeats S n

as the seats in:

  coarseTownPackingRemainder S n

with nonempty squareOffsetPrimeSupport.

Prove exact membership.

Prove the remainder splits exactly into:

- uncovered retained seats
- supported retained seats.

Because every uncovered full-town seat has empty support, it cannot be a collision endpoint and therefore must belong to the left remainder.

Target exact carrier theorem:

  coarseFullTownUncoveredSeats S n
  subset
  coarseTownPackingRemainder S n.

Then prove the exact card identity:

  R.card = U.card + retainedSupported.card.

Use disjoint union, not subtraction, as the primary theorem.

## Phase 2 - represented active directions

Define the left represented direction carrier as the union of actual supports over the left remainder:

  coarseTownRepresentedPrimes S n
  =
  biUnion over a in left remainder of squareOffsetPrimeSupport n a.

Prove:

- represented primes are contained in coarseFullTownActivePrimes
- represented primes are contained in T
- every represented prime occurs in exactly one retained seat because the remainder supports are pairwise disjoint.

Define:

  coarseTownUnrepresentedActivePrimes S n
  =
  coarseFullTownActivePrimes S n minus coarseTownRepresentedPrimes S n.

Prove the exact active partition:

  represented.card + unrepresented.card = active.card.

Prefer exact disjoint union semantics first.

## Phase 3 - retained support excess

Define:

  coarseTownRetainedSupportExcess S n
  =
  sum over a in left remainder of support(a).card - 1.

Because uncovered retained seats contribute zero, prove:

  represented.card
  =
  retainedSupported.card + retainedSupportExcess.

This should follow from:

- pairwise-disjoint retained supports
- card of their biUnion
- pointwise support cardinality split into nonempty baseline plus excess.

Do not duplicate the global support-excess proof if a generic local lemma can be reused.

## Phase 4 - exact left loss decomposition

Use:

  R + L = U + A
  R = U + retainedSupported
  A = represented + unrepresented
  represented = retainedSupported + retainedSupportExcess

to prove the exact additive identity:

  coarseTownSupportLoss S n
  =
  unrepresentedActive.card + retainedSupportExcess.

This is a primary theorem.

It must be unconditional in full-cover status.

Interpretation:

- one part of the loss is an active direction whose fiber endpoint is not represented by the retained family
- the other part is multiple represented directions coalescing on one retained seat.

Do not use signed arithmetic in the public statement.

## Phase 5 - left fiber maximum semantics

For q in coarseFullTownActivePrimes, its fiber is nonempty.

Provide a clean API for its maximum seat.

Prefer not to introduce a defaulted global maximum on empty fibers.

Possible approach:

  theorem with q active and F.max' h.

Define a predicate if useful:

  coarseTownFiberMaximumAt S n q a

meaning:

- a belongs to the q fiber
- every b in that fiber satisfies b <= a.

Prove existence and uniqueness for active q.

Prove equivalence with Finset.max' under a nonempty proof.

## Phase 6 - retained seat is simultaneous fiber maximum

Prove the exact left-selector characterization.

For a in fullTown:

  a belongs to coarseTownPackingRemainder S n

iff

  for every q in squareOffsetPrimeSupport n a,
  a is the maximum seat of the q fiber.

Uncovered seats satisfy the right side vacuously and must be retained.

This theorem should be derived from the exact deletion-by-nonmaximum-fibers semantics already proved.

Do not reprove collision-edge packing from scratch.

## Phase 7 - represented prime iff its maximum is retained

For active q prove:

  q belongs to coarseTownRepresentedPrimes S n

iff

  the maximum seat of q's fiber belongs to coarseTownPackingRemainder S n.

Equivalent predicate-based forms are acceptable.

Then prove:

  q is unrepresented active

iff

  its maximum fiber seat is deleted.

This gives exact endpoint semantics to the abstract active partition.

## Phase 8 - left prime handoff relation

Define a finite relation on active outside primes.

Suggested semantics:

  coarseTownMaxHandoff S n q p

holds when there exists a seat a such that:

- a is the maximum seat of q's fiber
- a belongs to p's fiber
- there exists a strictly larger seat b in p's fiber.

Equivalently:

- the q maximum is a nonmaximum p seat.

Prove:

- q and p are active outside primes
- q != p
- maxSeat(q) < maxSeat(p).

The strict maximum increase is mandatory.

## Phase 9 - lost direction iff outgoing handoff

Prove for active q:

  q is unrepresented
  iff
  there exists p with coarseTownMaxHandoff S n q p.

Thus represented directions are exactly terminal directions of the handoff relation.

If theorem naming with terminal is useful, expose:

  represented iff no outgoing max handoff.

This is the conceptual heart of the checkpoint.

## Phase 10 - acyclicity by maximum-seat rank

Because every handoff strictly increases fiber maximum, prove at minimum:

- no self-loop
- no two-cycle
- no finite directed cycle if a lightweight finite relation API is available.

Do not import a heavy graph library merely to state acyclicity.

A sufficient production theorem is:

  along every handoff q -> p,
  maxSeat(q) < maxSeat(p).

Then record acyclicity as a corollary or report-level consequence if transitive-closure infrastructure is expensive.

If a simple finite-chain theorem is available, prove that every repeated handoff chain terminates at a represented active direction.

Do not use nonconstructive infinite graph arguments when the active carrier is finite.

## Phase 11 - handoff step arithmetic

Suppose q -> p through q maximum seat a and a later p seat b.

Prove:

  p divides n^2 + a
  p divides n^2 + b
  p divides b-a
  0 < b-a.

Because a and b both lie in fullTown, expose their grid coordinates where useful:

  a = r + j*M
  b = s + k*M.

Then reuse the existing signed cross-column theorem to obtain:

  p divides the appropriate phased offset and street-index gap.

If r=s, use the same-column theorem.

## Phase 12 - uniform vertical sparsity consequence

Under the familiar hypothesis:

  K <= p

for every outside p,

same-column repeated p occurrences are impossible.

Therefore every max handoff must move to a different base column.

Prove this exact consequence.

Do not claim that different-column handoffs are unique globally.

This is the first geometry restriction on the lost-direction relation.

## Phase 13 - fixed cross-column continuation uniqueness

Reuse:

  coarseCrossColumn_compatible_index_unique

or the strongest existing phased uniqueness theorem.

For fixed outside p and fixed destination base column s, under K<=p, prove there is at most one street index k in that column that can continue p.

Translate this into a handoff statement if clean:

For fixed source maximum seat and fixed p and destination column, at most one destination seat realizes the continuation.

Do not infer a global bound on the number of lost q without controlling source multiplicity.

## Phase 14 - right retained supported seats

Mirror the semantic layer for:

  coarseTownRightPackingRemainder.

Define:

- right retained supported seats
- right represented active primes
- right unrepresented active primes
- right retained support excess.

Use the existing right deletion by fiber minima.

Avoid copying proofs when a generic orientation lemma can be extracted cheaply.

## Phase 15 - right loss and right overlap

Implement the minimum-fiber analogue of the left deletion witness ledger.

Define only the necessary objects:

- right deletion witness primes
- right deletion multiplicity
- right deletion mass
- right deletion overlap
- right support loss.

Prove exact mirrors:

  Dright + Oright = MdelRight
  MdelRight + A = incidence
  Rright + X = U + A + Oright
  Oright <= X
  Rright + Lright = U + A.

Then prove the right loss decomposition:

  Lright
  =
  rightUnrepresentedActive.card
  + rightRetainedSupportExcess.

This phase is required unless a generic min/max abstraction clearly removes duplication.

## Phase 16 - right minimum handoff

Define the mirror relation:

  coarseTownMinHandoff S n q p

where the minimum q seat is a nonminimum p seat.

Prove:

- minSeat(p) < minSeat(q)
- q is right-unrepresented iff it has an outgoing min handoff
- right represented directions are terminal for the decreasing relation.

Again, a rank-decrease theorem is enough if full relation acyclicity infrastructure is expensive.

## Phase 17 - left and right orientation identities

Because both orientations use the same:

- U
- A
- incidence
- X

prove exact comparison identities.

Required:

  Rleft + Lleft = Rright + Lright.

Also prove the report-022 overlap identity:

  Rright + Oleft = Rleft + Oright.

Check orientation carefully against the n=297 calibration:

  Rleft = 57
  Rright = 60
  Oleft = 9
  Oright = 12

so both sides equal 69.

Do not reverse this equality.

## Phase 18 - transparent better-of-two selector

Define a deterministic selector that chooses the larger of:

  left remainder
  right remainder.

Possible form:

  if left.card <= right.card then right else left.

Define or derive its associated loss as:

  min(leftLoss, rightLoss).

Prove:

- selected remainder subset fullTown
- selected remainder is PairwiseOldSupportDisjointSquareSeatFamily
- selected remainder card = max(left.card,right.card)
- selected loss = min(leftLoss,rightLoss)
- selected remainder card + selected loss = U.card + A.card.

Do not claim optimal packing.

## Phase 19 - better survivor-world capacity

Under full cover prove:

  betterRemainder.card <= T.card.

Therefore obtain the deterministic better-of-two deficit:

  T.card < betterRemainder.card
  implies not full cover.

Also prove the exact loss coordinate:

  min(leftLoss,rightLoss) + (T.card - A.card) < U.card

iff the better-of-two survivor capacity deficit.

This remains a finite exact frontier.

Do not imply that it avoids the need for positive U.

## Phase 20 - finite orientation diagnostics

Extend the 602-row diagnostics with:

- left represented card
- left unrepresented active card
- left retained support excess
- left loss decomposition residual
- right analogues
- left handoff edge count
- right handoff edge count
- max handoff chain depth if cheaply computed
- min handoff chain depth
- better remainder card
- better loss
- survivor capacity result

Preserve exact zero residuals for all conservation identities.

Mandatory anchors:

  29
  297
  1031.

## Phase 21 - kernel calibration at n=297

Kernel-check the left and right loss decomposition.

Expected existing cards:

  U = 29
  A = 40
  Rleft = 57
  Lleft = 12
  Rright = 60.

Therefore:

  Lright = 9.

Check:

  57 + 12 = 29 + 40
  60 + 9 = 29 + 40.

Kernel-check:

- left unrepresented plus retained excess = 12
- right unrepresented plus retained excess = 9
- better selector chooses right
- survivor capacity 58 < 60 gives the deterministic endpoint.

Preserve the existing n=297 endpoint theorem rather than replacing it.

## Phase 22 - kernel calibration at n=1031

Expected:

  U = 144
  A = 128
  Rleft = 216
  Lleft = 56
  Rright = 210.

Therefore:

  Lright = 62.

Kernel-check enough terms to confirm:

  216 + 56 = 144 + 128
  210 + 62 = 144 + 128.

Better selector must choose left.

Record the represented and unrepresented direction decomposition if affordable.

The 32GB build environment is available; substantial finite kernel checks are acceptable when they validate a structural theorem.

## Phase 23 - evaluate handoff geometry as a provider

This phase is skeptical and mandatory.

Test whether the max/min handoff relations give any new upper bound on:

  unrepresentedActive.card

or:

  min(leftLoss,rightLoss)

that is not already a direct consequence of:

  loss <= supportExcess.

Candidate tools:

- strict rank increase or decrease
- column change under K<=outside prime
- fixed destination-column uniqueness
- bounded number of street indices
- support cardinality at a handoff seat.

Do not assume a forest has bounded branching.

Do not convert acyclicity alone into a useful cardinality bound.

If every candidate bound collapses to an existing support-excess estimate, state that explicitly.

## Phase 24 - retained direction gap theorem search

For a lost max direction q handing off to p at seat a:

- q ends at a
- p continues beyond a.

Investigate whether q and p satisfy an additional arithmetic relation beyond sharing the complete point.

Examples to test:

- relation between p and q from the factorization of n^2+a
- whether p*q divides a difference to a later p seat
- whether full-period width M forces p*q or lcm constraints across a chain
- whether multiple lost directions at the same seat force a support-depth penalty already counted by retained excess.

Do not introduce new cyclotomic machinery unless a concrete theorem appears.

## Phase 25 - exact route-limit judgment

At the end decide whether deterministic endpoint packing remains a plausible symbolic route to a universal provider.

Possible conclusions:

A. Handoff geometry yields a new symbolic loss bound.

B. Better-of-two yields new finite endpoints but no new universal bound.

C. Loss decomposition proves the deterministic packing route is only a certificate framework unless one independently proves uncovered seats.

D. One precise cross-column handoff bound remains.

Do not hide a route limitation.

If the exact identities show that every capacity contradiction is equivalent to positive uncovered mass plus a finite loss comparison, say so directly.

## Possible outcomes

Outcome A - HANDOFF GEOMETRY YIELDS A NEW SYMBOLIC LOSS BOUND

A new theorem bounds unrepresented directions or better loss using full-period geometry beyond the existing support-excess bound.

Outcome B - SYMMETRIC FIBER PACKING ADDS NEW DETERMINISTIC POWER

The max/min ledgers and better selector are exact and add kernel-certified finite endpoints or stronger deterministic certificates, but no new universal loss bound follows.

Outcome C - RETAINED-DIRECTION THEORY CLOSES THE PACKING ROUTE

The exact loss decomposition and handoff semantics are proved, but they show that deterministic packing remains a finite certificate method and supplies no independent universal provider.

Outcome P - ONE HANDOFF GEOMETRY BRIDGE REMAINS

The semantic and symmetric ledgers close, but one explicit cross-column handoff theorem blocks the loss-bound judgment.

## Non-goals

Do not claim:

- Legendre conjecture
- optimality of the better-of-two selector
- that the handoff relation is a tree
- bounded branching without proof
- that acyclicity alone gives a capacity deficit
- that active primes all have distinct terminal seats
- independence of prime waves
- that positive U has been proved universally
- PNT, RH, Bertrand, or analytic sieve estimates

Do not return to the Instruction 018 valuation floor sum unless a handoff theorem actually consumes it.

## Suggested implementation surface

Possible modules:

DkMath/NumberTheory/Legendre/CoarseTownRetainedDirections.lean
DkMath/NumberTheory/Legendre/CoarseTownSymmetricDeletion.lean
DkMath/NumberTheory/Legendre/CoarseTownPrimeHandoff.lean

Extract a neutral generic min/max packing lemma only if it reduces duplication.

Keep finite calibration data in DkMathTest.

Update the Legendre facade after focused builds are green.

## Validation

For all new production declarations:

- focused builds
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- forbidden-token scan
- print axioms for every new public declaration
- git diff --check

For n=297 and n=1031 calibrations:

- record exact kernel-checked cards
- record left/right orientation
- reject any sorryAx dependency

Existing unrelated root sorry warnings may remain.

## Durable checkpoint protocol

Update findings after:

- retained supported seats
- represented active directions
- left loss decomposition
- left maximum semantics
- max handoff relation
- handoff rank increase
- right mirrored conservation
- min handoff relation
- left/right identities
- better-of-two selector
- survivor capacity
- n=297 calibration
- n=1031 calibration
- handoff geometry provider test
- final A/B/C/P judgment

Preserve false conjectures and smallest counterexamples.

## Final report

Answer explicitly:

1. What are the exact left retained-supported and represented-prime carriers?
2. Is every uncovered full-town seat retained?
3. Is represented.card = retainedSupported.card + retainedSupportExcess proved?
4. Is left loss exactly unrepresentedActive.card + retainedSupportExcess?
5. Is a left-retained seat exactly simultaneous maximum in every supporting prime fiber?
6. Is an active prime represented exactly when its fiber maximum is retained?
7. What is the exact max-handoff relation?
8. Does every unrepresented active prime have an outgoing handoff?
9. Does every handoff strictly increase fiber maximum?
10. What cross-column arithmetic does a handoff satisfy?
11. What changes under the uniform K<=q hypothesis?
12. Was the full right minimum-fiber conservation implemented?
13. Is right loss exactly right-unrepresented plus right retained excess?
14. Were the identities Rleft+Lleft=Rright+Lright and Rright+Oleft=Rleft+Oright proved?
15. What exact better-of-two selector was implemented?
16. What is its exact loss frontier?
17. What are the left/right loss decompositions at n=297 and n=1031?
18. Did handoff geometry yield any genuinely new symbolic loss bound?
19. Does deterministic packing remain a plausible universal route, or is it now classified as a finite certificate framework?
20. What single theorem should be attempted next?

End with exactly one judgment:

Outcome A - HANDOFF GEOMETRY YIELDS A NEW SYMBOLIC LOSS BOUND
Outcome B - SYMMETRIC FIBER PACKING ADDS NEW DETERMINISTIC POWER
Outcome C - RETAINED-DIRECTION THEORY CLOSES THE PACKING ROUTE
Outcome P - ONE HANDOFF GEOMETRY BRIDGE REMAINS
