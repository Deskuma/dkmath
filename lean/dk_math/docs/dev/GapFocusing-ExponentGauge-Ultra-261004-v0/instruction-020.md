# Instruction 020 - Full-period coarse town and support-packing judgment

## Mission

Continue from Instruction 019.

Instruction 019 proved an exact two-street coarse PrimeWorld packet inside one fixed square shell:

  r
  r + M

where:

  M = primeWorldModulus S

and r ranges over the phased survivor base:

  coarsePrimeWorldBase S n.

It also proved:

- square-anchor phase is preserved under the M shift
- both complete points are coprime
- under full cover, each side requires distinct covering primes outside S
- fixed ordered outside-prime pairs obey product-period sparsity
- the width-M near/far split gives a new exact assignment frontier
- no uniform capacity contradiction was obtained

The next question is whether using only two period copies threw away the main combinatorial leverage.

Inside the open square shell there are generally many complete copies of the same PrimeWorld period.

Let:

  K = (2*n) / M

for positive M.

For every:

  r in coarsePrimeWorldBase S n
  j < K

the offset:

  r + j*M

lies in the open square shell.

Instruction 020 must build this full complete-period grid and let Lean judge whether its support geometry yields a genuine global capacity obstruction.

The intended grid coordinate is:

  (r,j) -> r + j*M

and the complete point is:

  n^2 + r + j*M.

The key possible collision law is:

If an outside prime q divides two complete points in the same column r at street indices j and k, then:

  q divides j-k

because q does not divide M.

This may force strong vertical support separation when the street count K is smaller than the available outside primes.

Do not assume this yields Legendre.
Do not assume the proposed packing inequality is strong enough.
Formalize the exact finite structure first and classify the result.

All new instruction, findings, and report artifacts must remain parser-safe plain text. Avoid backslash notation and LaTeX control sequences.

## Phase 0 - broad audit before implementation

Audit at minimum:

DkMath.NumberTheory.Legendre.CoarsePrimorialTown
DkMath.NumberTheory.Legendre.PrimeWorldPacketBridge
DkMath.NumberTheory.Legendre.OldSupportCapacity
DkMath.NumberTheory.Legendre.OldSupportGcd
DkMath.NumberTheory.Legendre.PacketCross
DkMath.NumberTheory.Legendre.CoprimePacket
DkMath.NumberTheory.Primitive.PeriodicPrimeWorld
DkMath.NumberTheory.Primitive.PrimeWorldRefinement
DkMath.NumberTheory.Primitive.PrimeWorldResidues
DkMath.NumberTheory.Primitive.CrossPeriod

Also search repository-wide for:

- finite graph independent set bounds
- vertex cover or edge deletion bounds
- pairwise disjoint Finset family extraction
- support packing
- incidence upper bounds
- arithmetic progression divisibility counts
- card filter by modular residue
- child-index occupancy
- finite sieve or wave capacity
- existing complete-period shell decompositions

Do not introduce a graph abstraction if a simpler Finset argument already exists.

Record source-inventory-020.md before substantial production work.

## Phase 1 - positive modulus and complete-period count

For a certified finite prime world S, reuse or prove:

  0 < primeWorldModulus S.

Let:

  M = primeWorldModulus S
  K = (2*n) / M.

Under:

  M <= n

prove at least:

  2 <= K.

Also prove:

  K*M <= 2*n
  2*n < (K+1)*M

where appropriate from Nat division.

Keep zero-modulus branches explicit if generic definitions are introduced outside the KnownPrimeScales context.

## Phase 2 - full complete-period grid carrier

Define a finite pair carrier for complete period copies, for example:

  coarsePrimeWorldGridPairs S n
  =
  coarsePrimeWorldBase S n product range K

or the equivalent orientation.

Define the seat map:

  coarsePrimeWorldGridSeat S n (r,j)
  =
  r + j*M.

Prove for every grid pair:

  SquareOffset n (r + j*M).

The key bound is:

  r <= M
  j < K
  therefore
  r + j*M <= (j+1)*M <= K*M <= 2*n.

Prove the pair-to-seat map is injective.

Do not rely on modulo alone without handling the representative endpoint r=M exactly.

If convenient, use Euclidean quotient and remainder after shifting the representative convention.

## Phase 3 - full-period town as a Finset of offsets

Define:

  coarsePrimeWorldFullTown S n

as the image of the grid pair carrier under the seat map.

Prove:

  coarsePrimeWorldFullTown S n subset squareOffsets n.

Prove exact cardinality:

  card(fullTown)
  =
  K * card(coarsePrimeWorldBase S n)
  =
  K * Nat.totient M.

Retain the existing two-street town as the K=2 initial portion, not as a competing definition.

If K=2, prove the full town equals the existing coarsePrimeWorldTown when the definitions line up exactly.

If endpoint conventions prevent literal equality, prove the exact inclusion or image relation instead.

## Phase 4 - all period copies preserve PrimeWorld address and survival

For every base r and every j:

  squareShellWheelProjection S n (r+j*M)
  =
  squareShellWheelProjection S n r.

Also prove:

  SupportDisjointFrom S (n^2+r+j*M)
  iff
  SupportDisjointFrom S (n^2+r).

Therefore every seat of the full town is an S-survivor.

This should delegate to existing PeriodicPrimeWorld with multiplier j.

Do not reprove divisibility periodicity.

## Phase 5 - column decomposition

For a fixed base representative r define the full column:

  coarsePrimeWorldColumn S n r
  =
  image of j in range K under r+j*M.

Prove:

- the column lies in fullTown
- its card is K
- different j give different seats
- every seat in one column has the same PrimeWorld address
- every seat is S-surviving

If useful, prove fullTown is a disjoint union of these columns over the base.

The disjointness must use the injectivity from Phase 2.

## Phase 6 - exact same-column common-prime collision law

Let q be prime with q notin S.

Suppose:

  j < k < K
  q divides n^2 + r + j*M
  q divides n^2 + r + k*M.

Prove:

  q divides k-j.

Expected route:

- q divides (k-j)*M from the point difference
- prime_outside_not_dvd_coarseModulus gives not q divides M
- prime divisibility of a product forces q divides k-j

Package a symmetric version if useful.

Then derive:

If:

  k-j < q

the two complete points cannot share q.

## Phase 7 - vertical support-disjointness criterion

Every actual old support prime of a full-town seat lies in:

  coarseOutsidePrimes S n

because the seat is an S-survivor.

Prove a clean sufficient condition:

If every q in coarseOutsidePrimes S n satisfies:

  K <= q

then, for each base r, the K seats in its column have pairwise disjoint actual old-prime supports.

Target theorem shape:

  PairwiseOldSupportDisjointSquareSeatFamily n (coarsePrimeWorldColumn S n r)

under the uniform outside-prime lower-bound hypothesis.

This theorem should use the exact old-support difference criterion where useful.

Do not strengthen to complete-point pairwise coprimality unless it follows.

## Phase 8 - initial-prime-world specialization

For:

  S = primeScalesUpTo P

prove a simple sufficient condition for the Phase 7 hypothesis.

Candidate:

  K <= P+1

because any prime q <= n outside primeScalesUpTo P must satisfy P < q.

Check exact Nat boundary conditions.

If the clean condition is instead:

  K <= Nat.succ P

use that.

Do not require a next-prime function unless necessary.

This produces an explicit column support-disjointness theorem for initial prime worlds.

## Phase 9 - per-prime occupancy in one column

Do not stop at the K<=q special case.

For an arbitrary outside prime q, determine the exact or sharp finite upper bound on:

  number of j < K
  such that
  q divides n^2+r+j*M.

Because q is coprime to M, the valid j form one residue class modulo q.

Preferred bound:

  occupancy <= ceil(K/q)

in a Nat-safe exact form, for example:

  occupancy <= (K + q - 1) / q.

If exact phase-dependent floor formulas are easy, expose them separately.

Search PrimeWorldRefinement and existing arithmetic-progression card lemmas before implementing new counting machinery.

This is the generic vertical wave-capacity theorem.

## Phase 10 - total per-prime occupancy in the full grid

For fixed outside prime q, sum the column bound over all base representatives.

Target:

  number of fullTown seats supported by q
  <=
  card(base) * ceil(K/q).

In the important K<=q case:

  q supports at most one seat per column
  therefore total q occupancy <= card(base).

Use actual squareOffsetPrimeSupport membership, not only raw divisibility, where possible.

This is a global wave-capacity upper bound.

## Phase 11 - full-cover incidence lower bound

Under:

  SquareOffsetsFullyCovered n

every fullTown seat has nonempty old support.

Therefore total support incidence over the full town is at least:

  card(fullTown)
  =
  K * card(base).

Transpose this incidence by prime.

Combine with Phase 10 to obtain a necessary capacity inequality.

Preferred generic shape:

  K * card(base)
  <=
  card(base) * sum over q in outsidePrimes of ceil(K/q).

When card(base)>0, derive the cancelled form if Nat arithmetic allows it cleanly:

  K
  <=
  sum over q in outsidePrimes of ceil(K/q).

For the uniform K<=q branch, derive:

  K <= card(coarseOutsidePrimes S n).

This is an exact necessary condition under full cover.

Do not claim it is sufficient.

## Phase 12 - test the vertical capacity frontier

Run bounded diagnostics for the new necessary inequalities.

At minimum inspect:

  n = 3
  n = 5
  n = 8
  n = 19
  n = 29
  n = 297
  n = 1031

and the near-miss anchors from 016 if available.

For each selected coarse world record:

- M
- K
- base card
- fullTown card
- outside-prime card
- minimum outside prime
- sum of ceil(K/q)
- actual support incidence
- whether K <= every outside prime
- whether K <= outside-prime card
- whether the generic capacity inequality has slack or fails

If a strict failure occurs, kernelize the corresponding prime-square-cell endpoint through an existing consumer where possible.

Do not infer a universal law from diagnostics.

## Phase 13 - support collision graph

Independently of the incidence route, define the actual collision relation on fullTown:

Two distinct seats a,b collide if:

  squareOffsetPrimeSupport n a
  intersects
  squareOffsetPrimeSupport n b

nontrivially.

Prefer a finite edge carrier with a canonical orientation a<b, for example:

  coarseTownSupportCollisionEdges S n.

Do not use a graph library unless it materially simplifies proofs.

Prove exact edge membership semantics.

Preserve the n=3 reuse regression from 019.

## Phase 14 - generic edge-deletion packing lemma

Formalize the report-019 proposed finite combinatorial fact in a neutral location if no existing theorem already supplies it.

For a finite vertex set V and a finite collision edge set E representing every non-disjoint pair, prove existence of R subset V such that:

- R is collision-free
- V.card <= R.card + E.card

A simple proof may choose at most one endpoint from every collision edge and remove the chosen vertices.

Do not overstate optimality.

This is a weak independent-set lower bound:

  R.card >= V.card - E.card

in additive Nat-safe form.

If a stronger existing theorem is readily available and has a lightweight dependency, reuse it.

## Phase 15 - apply packing to actual old support

Apply Phase 14 to fullTown.

Produce:

  exists R subset fullTown,
  PairwiseOldSupportDisjointSquareSeatFamily n R,
  fullTown.card <= R.card + collisionEdges.card.

Then derive the existing capacity-consumer criterion:

If:

  (primeScalesUpTo n).card + collisionEdges.card
  <
  fullTown.card

then:

  not SquareOffsetsFullyCovered n

and hence for positive n:

  exists p, Nat.Prime p and SquareCell n p.

Route the final step through OldSupportCapacity or Frontier.

Do not create a duplicate Legendre consumer.

## Phase 16 - prime-fiber decomposition of collision edges

The raw edge count may be too large.

Decompose collisions by common support prime q where useful.

For each q in coarseOutsidePrimes S n, define the seats in fullTown supported by q.

A q-fiber of size c contributes at most:

  choose(c,2)

unordered collision edges.

Because one edge can share more than one prime, the sum of q-edge counts is an upper bound, not necessarily equality.

Use the vertical occupancy theorem to bound c.

Seek a production inequality of the form:

  collisionEdges.card
  <=
  sum over outside q of choose(qFiberBound(q),2)

or a sharper column-aware version.

Do not silently count a multi-prime edge once.

## Phase 17 - exploit column geometry in edge counting

The same-column collision law is stronger than a generic q-fiber count.

If K<=q, q creates no edge inside any one column.

Therefore all q-collision edges lie across distinct columns.

Investigate whether the phased base addresses restrict how many cross-column edges a fixed q can create.

For two base representatives r and s, a shared q between streets j and k implies:

  q divides (s-r) + (k-j)*M.

Since M is invertible mod q, for fixed r,s,j there is at most one k modulo q.

When K<=q, this gives at most one compatible k in the street range.

Formalize the strongest clean uniqueness theorem available.

This may yield a significantly sharper collision-edge upper bound than the raw choose(c,2) estimate.

## Phase 18 - relation to PrimeWorldRefinement

Compare the full-period column coordinate:

  r + j*M

with the existing:

  primeWorldChild S r j.

They have the same arithmetic shape.

Determine the exact theorem-level relationship.

Important distinction:

- PrimeWorldRefinement usually uses j<q for one newly inserted prime q
- the shell fullTown uses j<K determined by shell width

For an outside fresh prime q, if K<=q, the shell column is a prefix of the q-child family.

Then existing:

  existsUnique_child_dvd_new_prime
  reservedChildIndices_eq_singleton
  card_survivingChildIndices

may imply the vertical occupancy theorem almost for free.

Reuse them if the base-coordinate hypotheses can be aligned with the square-point phase.

Do not identify the raw offset r with the PrimeWorld parent if the actual parent coordinate must be the phased residue or complete point modulo M.

Document the exact adapter.

## Phase 19 - canonical fitting primorial remains optional

Instruction 019 found no production maximal-fitting primorial selector.

Do not let that block the generic theorem layer.

Keep the main API parameterized by S and the hypothesis:

  primeWorldModulus S <= n.

For diagnostics, use the same operational initial and odd worlds as 019.

Only add a production selector if:
- it is small and natural,
- its maximality is needed by a proved theorem,
- and no equivalent existing object is found.

## Phase 20 - compare with two-street frontier

Prove exact inclusion:

  coarsePrimeWorldTown S n subset coarsePrimeWorldFullTown S n

under M<=n.

Compare the two necessary full-cover inequalities.

Determine whether the full-period theorem is strictly stronger for any kernel-calibrated anchors.

If yes, preserve at least one explicit witness.

If not, state that the extra streets add no provable capacity leverage under the current bounds.

## Phase 21 - interaction with Instruction 018

Keep this skeptical.

Test whether the centered odd-gap world or order-four fold norm improves:

- the lower bound on outside primes
- the per-column occupancy
- collision-edge counts
- a support-disjoint family extraction

Do not force an interaction.

The 018 prime-power floor-sum remains deferred unless it becomes an actual input to a new fullTown capacity theorem.

## Phase 22 - finite fullTown discovery scan

Extend the 019 diagnostics with exact full-period quantities.

For every tested anchor/world record:

- K
- full complete-period seat count
- partial tail size 2*n - K*M
- fullTown support incidence
- per-prime q-fiber cards
- maximum q-fiber card
- maximum same-column q occupancy
- collision edge count
- weak packing lower bound fullTown.card - edge.card
- greedy or exact small-range independent support family size
- old prime count
- whether existing OldSupportCapacity would fire
- vertical capacity slack
- edge-packing capacity slack

Use exact independent-set search only for small ranges if exponential cost is controlled.

Do not require exact maximum independent set for large anchors.

## Phase 23 - optional partial tail

The complete-period grid intentionally uses only K full blocks and leaves a tail of length:

  2*n - K*M.

Do not complicate the main theorem with the tail initially.

If the complete-block frontier is close to a strict contradiction, add a separate tail packet and determine whether it strengthens the count.

Otherwise preserve the tail as an explicit omitted remainder.

## Phase 24 - final Lean judgment

Classify the mathematical result, not the amount of code.

Outcome A - FULL-PERIOD TOWN YIELDS A NEW FULL-COVER OBSTRUCTION

A uniform or nontrivial theorem proves a strict capacity failure for a genuine class of anchors, or gives new unconditional square-cell prime endpoints through existing consumers.

Outcome B - FULL-PERIOD TOWN YIELDS A NEW GLOBAL CAPACITY FRONTIER

The K-period grid, vertical collision law, occupancy bounds, and a strictly stronger necessary full-cover inequality are proved, but no uniform contradiction follows.

Outcome C - FULL-PERIOD TOWN COLLAPSES TO PERIODIC BOOKKEEPING

The grid is exact, but all resulting bounds reduce to existing wave or incidence bookkeeping and give no stronger full-cover constraint.

Outcome P - ONE PRECISE SUPPORT-PACKING BRIDGE REMAINS

The full-period grid and vertical capacity close, but one explicit collision-edge or support-disjoint-family theorem blocks connection to OldSupportCapacity.

## Non-goals

Do not claim:

- Legendre conjecture
- PNT or RH
- Bertrand
- generic Jacobsthal bounds
- random independence of prime waves
- global uniqueness of a covering prime
- global uniqueness of an ordered prime pair
- pairwise support disjointness across different columns without proof
- that K copies exhaust the shell when there is a nonzero tail
- that K<=q holds automatically for all outside primes
- that a greedy diagnostic family is a production theorem
- that the weak edge bound is optimal

Do not implement the 018 prime-power floor-sum unless an actual theorem in this checkpoint consumes it.

## Suggested implementation surface

Likely modules:

DkMath/NumberTheory/Legendre/CoarsePrimeWorldFullTown.lean
DkMath/NumberTheory/Legendre/CoarseTownSupportPacking.lean

If the edge-deletion lemma is genuinely generic, place it in a neutral finite combinatorics module with no Legendre dependency.

Extend CoarsePrimorialTown only for very small adapters.
Avoid turning one file into a monolith.

## Validation

For all new production declarations:

- focused builds
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- forbidden-token scan
- print axioms for every new public declaration
- git diff --check

All new production declarations must remain free of sorryAx.

Preserve current file-header and file-marker conventions.

## Durable checkpoint protocol

Update findings after:

- source audit
- full-period count K
- grid carrier and injectivity
- fullTown cardinality
- survival and address preservation
- same-column collision law
- column support-disjointness criterion
- per-prime occupancy
- full-cover incidence frontier
- collision graph
- edge-deletion packing
- prime-fiber edge bound
- PrimeWorldRefinement adapter
- 018 interaction test
- bounded diagnostics
- final A/B/C/P judgment

Preserve false conjectures, smallest counterexamples, and prior negative audits.

## Final report

Answer explicitly:

1. What is the exact full complete-period carrier inside squareOffsets n?
2. Is its cardinality exactly K*totient(M)?
3. Is every seat an S-survivor with the same address along each column?
4. What exact theorem describes a common outside prime on two seats in one column?
5. Under what condition is an entire column an OldSupportCapacity-compatible pairwise-disjoint family?
6. What is the exact per-prime vertical occupancy bound?
7. What global incidence inequality does full cover force on the K-period town?
8. Does that inequality strictly improve the two-street frontier?
9. What collision-edge carrier was defined?
10. Was the generic V <= R+E packing theorem proved?
11. What upper bound on collision edges follows from prime fibers and column geometry?
12. Can a support-disjoint family large enough for the existing capacity consumer be constructed?
13. Does PrimeWorldRefinement directly supply any of the vertical occupancy theorem?
14. Does Instruction 018 contribute a genuine new restriction?
15. Was the partial tail needed?
16. What is the narrowest remaining theorem if no full-cover contradiction was obtained?

End with exactly one judgment:

Outcome A - FULL-PERIOD TOWN YIELDS A NEW FULL-COVER OBSTRUCTION
Outcome B - FULL-PERIOD TOWN YIELDS A NEW GLOBAL CAPACITY FRONTIER
Outcome C - FULL-PERIOD TOWN COLLAPSES TO PERIODIC BOOKKEEPING
Outcome P - ONE PRECISE SUPPORT-PACKING BRIDGE REMAINS
