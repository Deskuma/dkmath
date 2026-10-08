# Report 020 - Full-period town and support packing

Instruction 020 is implemented. Four new production modules expose 68
public declarations, the Legendre facade imports the three specialized
modules, and 17 public regression declarations preserve finite calibration
and negative examples. The scope is exact finite geometry, conditional
capacity, and kernel-certified square-cell prime endpoints at bounded
anchors. No universal Legendre theorem is obtained.

Source decisions are in [source-inventory-020.md](source-inventory-020.md).
Milestones are in [findings-020.md](findings-020.md).
Build and complete declaration evidence are in
[validation-020.md](validation-020.md).

## 1. Exact complete-period carrier

Let M=primeWorldModulus S, K=(2*n)/M, and
B=coarsePrimeWorldBase S n. The pair carrier is B product range K;
the seat map sends (r,j) to r+j*M. The full town is its image.
KnownPrimeScales S implies M>0. Division proves K*M<=2*n and
2*n<(K+1)*M; M<=n implies 2<=K.

All seats are in squareOffsets n. Injectivity uses r-1 as the canonical
representative below M, retaining the endpoint r=M. Outside certification,
a zero-modulus wrapper records K=0. Regression checks S={0}, and the
empty certified world M=1 includes the endpoint representative and all
six offsets at n=3.

Implementation: [CoarsePrimeWorldFullTown.lean](../../../DkMath/NumberTheory/Legendre/CoarsePrimeWorldFullTown.lean).

## 2. Exact cardinality

card(fullTown)=K*totient(M), using the exact phased base cardinality and
the injective image of the product. The column at r is the image of
range K under j -> r+j*M and has exactly K seats. Distinct base columns
are disjoint, and their union is fullTown. Under M<=n the old two-street
town is contained in fullTown; if K=2 the carriers are literally equal.
The n=8, S={2,3} equality is kernel-calibrated.

## 3. Address and survival

For every j the square-shell address at r+j*M equals that at r.
SupportDisjointFrom S at n*n+r+j*M is equivalent to that at n*n+r.
These adapters delegate to the existing multiplier periodicity API.
Every seat in fullTown is an S-survivor for certified S. Its actual old
support is contained in T=coarseOutsidePrimes S n.

## 4. Same-column common-prime law

For a prime q outside S dividing both complete points, the production
API proves Nat.ModEq q j k and consequently q divides k-j. If j<k
and k-j<q, such a common divisor is impossible. Modulus-coprimality
comes from the existing PrimeWorldRefinement theorem. The signed
cross-column law also proves that q divides
(s-r)+(k-j)*M in the integers.

## 5. OldSupportCapacity-compatible columns

If every q in T satisfies K<=q, each entire column is a
PairwiseOldSupportDisjointSquareSeatFamily n. Actual old support, rather
than complete-point coprimality, is the interface used. For
S=primeScalesUpTo P, the sufficient cutoff condition is K<=P+1.

At n=1031 the operational initial world is primeScalesUpTo 10={2,3,5,7};
M=210, K=9, and each column satisfies this production family theorem.
The town has 432 seats. These statements are kernel-calibrated.
The uniform criterion does not imply disjointness across columns:
n=3, S={3} satisfies it but the town reuses q=2. That negative
regression and the original 019 reuse regression both remain checked.

## 6. Per-prime vertical occupancy

For any outside prime q, coarseColumnWaveIndices filters j<K by
divisibility of the complete point. Its cardinality is at most
(K+q-1)/q. This is the exact Nat ceiling upper bound; the actual phase
can make occupancy smaller. A proof injects valid indices into quotient
buckets j/q, using congruence for equal remainders.

For K<=q the existing unique-child theorem gives at most one index in
the prefix, after aligning the complete-point phase. The actual full-town
q-fiber is a union of these column images, so its cardinality is at most
base.card*ceil(K/q), and at most base.card in the uniform case.
No exact phase-dependent floor formula was added.

Implementation: [CoarsePrimeWorldVerticalCapacity.lean](../../../DkMath/NumberTheory/Legendre/CoarsePrimeWorldVerticalCapacity.lean).

## 7. Global incidence frontier

The actual incidence is both the sum of support cardinalities over seats
and the sum of q-fiber cardinalities over T. Full cover forces

  K*base.card <= incidence <= base.card*sum_q ceil(K/q).

Positive totient permits cancellation, giving

  K <= sum_q ceil(K/q).

In the uniform K<=q case this implies K<=T.card. Both are necessary
conditions only. A strict violation proves non-full-cover and yields an
existential prime in the square cell through the existing Frontier API.

The scan uses the exact 019 operational initial and odd worlds, for all
n=1..300 and n=1031: 602 rows. The following selected rows show the
vertical quantities. I denotes actual support incidence; slack is
capacity-K. A negative slack is a strict obstruction.

| n | world | M | K | base | seats | T | min q | capacity | I | uniform | slack |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 3 | initial | 2 | 3 | 1 | 3 | 1 | 3 | 1 | 1 | True | -2 |
| 3 | odd | 3 | 2 | 2 | 4 | 1 | 2 | 1 | 2 | True | -1 |
| 5 | initial | 2 | 5 | 1 | 5 | 2 | 3 | 3 | 3 | False | -2 |
| 5 | odd | 3 | 3 | 2 | 6 | 2 | 2 | 3 | 4 | False | 0 |
| 6 | initial | 6 | 2 | 2 | 4 | 1 | 5 | 1 | 0 | True | -1 |
| 6 | odd | 3 | 4 | 2 | 8 | 2 | 2 | 3 | 5 | False | -1 |
| 8 | initial | 6 | 2 | 2 | 4 | 2 | 5 | 2 | 1 | True | 0 |
| 8 | odd | 3 | 5 | 2 | 10 | 3 | 2 | 5 | 8 | False | 0 |
| 11 | initial | 6 | 3 | 2 | 6 | 3 | 5 | 3 | 2 | True | 0 |
| 11 | odd | 3 | 7 | 2 | 14 | 4 | 2 | 8 | 13 | False | 1 |
| 19 | initial | 6 | 6 | 2 | 12 | 6 | 5 | 7 | 8 | False | 1 |
| 19 | odd | 15 | 2 | 8 | 16 | 6 | 2 | 6 | 15 | True | 4 |
| 29 | initial | 6 | 9 | 2 | 18 | 8 | 5 | 10 | 13 | False | 1 |
| 29 | odd | 15 | 3 | 8 | 24 | 8 | 2 | 9 | 24 | False | 6 |
| 297 | initial | 210 | 2 | 48 | 96 | 58 | 11 | 58 | 88 | True | 56 |
| 297 | odd | 105 | 5 | 48 | 240 | 59 | 2 | 61 | 325 | False | 56 |
| 1031 | initial | 210 | 9 | 48 | 432 | 169 | 11 | 169 | 439 | True | 160 |
| 1031 | odd | 105 | 19 | 48 | 912 | 170 | 2 | 182 | 1393 | False | 163 |

## 8. Strict improvement over the two-street frontier

Yes, as a finite necessary numerical test. At n=5, S={2}, the base
contains one seat, the older near/far assignment bound passes, and the
full grid has K=5 while capacity=ceil(5/3)+ceil(5/5)=3. The conjunction
that the old test passes and the new test fails is proved in Lean.
The existential prime endpoint then follows from the new vertical
consumer, without choosing a prime witness by a primality test.

Sixteen diagnostic world/anchor rows have strict vertical deficits;
the two n=1 worlds coincide as the pair (1,empty). All fifteen distinct
pairs are kernel-certified in verticalDeficitCalibrations, and each has
a square-cell prime endpoint through the existing consumer. Their anchors
are 1,2,3,4,5,6,9,10,12,15,16. Seven diagnostic rows pass the old
assignment test while failing the new one. This proves neither universal
strictness nor a uniform asymptotic contradiction.

## 9. Actual collision edges

coarseTownSupportCollisionEdges is the finite carrier of (a,b) in the
town product with a<b and non-disjoint actual squareOffsetPrimeSupport.
It counts each unordered colliding seat pair once, irrespective of how
many common support primes it has. Exact membership semantics are public.
No graph library was introduced.

Implementation: [CoarseTownSupportPacking.lean](../../../DkMath/NumberTheory/Legendre/CoarseTownSupportPacking.lean).

## 10. Generic finite packing

The neutral FinsetSupportPacking module proves existence of R subset V
with pairwise-disjoint supports and V.card<=R.card+E.card. Its construction
removes the image of first endpoints of all oriented collision edges.
The image has cardinality at most E.card, and any remaining collision
would have its first endpoint removed. No optimality is asserted.

Implementation: [FinsetSupportPacking.lean](../../../DkMath/Combinatorics/FinsetSupportPacking.lean).

## 11. Prime-fiber and column bounds on edges

For each q, all strictly ordered pairs in its actual fiber have exactly
choose(fiber.card,2) elements. Every support collision is in at least
one q-edge carrier. Union subadditivity proves

  E.card <= sum_q choose(actualFiber(q).card,2)
         <= sum_q choose(base.card*ceil(K/q),2).

Under uniform sparsity, the explicit upper bound is
T.card*choose(base.card,2). The sum is an upper bound, not an identity:
at n=11, S={3}, the actual edge count is 31 while the fiber sum is 32.
That smallest observed overcount is kernel-calibrated.

Column geometry also gives a signed cross-column difference and uniqueness
of the compatible k<K when K<=q, for fixed right representative and a
divisible right point. Together with a fixed left point this is the
requested at-most-one-compatible-right-index statement. Uniform columns
have no internal q-edges. A stronger aggregate cross-column count has
not been asserted; the production aggregate bound above uses the fibers.

## 12. Extraction and existing capacity consumer

The production packing theorem gives R subset fullTown, the existing
old-support family predicate, and fullTown.card<=R.card+E.card. Therefore

  (primeScalesUpTo n).card+E.card < fullTown.card

proves non-full-cover and, for positive n, a square-cell prime through
OldSupportCapacity. The mathematical packing bridge is complete.

At n=11, S={2,3}, fullTown.card=6, pi(11)=5, and E is empty.
Vertical capacity equals K=3, so the edge route detects a strict
obstruction missed by the generic vertical test. All these quantities
and the existential prime endpoint are kernel-proved.

The discovery scan has 41 strict raw-edge deficits. Its concrete
endpoint-deletion families exceed the old prime count in 504 rows;
its greedy families do so in 591 rows. These counts and large families
are independently verified Python diagnostics, not Lean certificates.
Only the stated finite regression endpoints are claimed kernel-proved.
The table reports weak=max(0,seats-E), remaining endpoint-deletion family size R,
greedy size G, and edge slack=pi(n)+E-seats.

| n | world | max fiber | max column occupancy | E | weak | R | G | pi(n) | edge slack |
|---|---|---|---|---|---|---|---|---|---|
| 3 | initial | 1 | 1 | 0 | 3 | 3 | 3 | 2 | -1 |
| 3 | odd | 2 | 1 | 1 | 3 | 3 | 3 | 2 | -1 |
| 5 | initial | 2 | 2 | 1 | 4 | 4 | 4 | 3 | -1 |
| 5 | odd | 4 | 2 | 6 | 0 | 3 | 3 | 3 | 3 |
| 6 | initial | 0 | 0 | 0 | 4 | 4 | 4 | 3 | -1 |
| 6 | odd | 4 | 2 | 6 | 2 | 5 | 5 | 3 | 1 |
| 8 | initial | 1 | 1 | 0 | 4 | 4 | 4 | 4 | 0 |
| 8 | odd | 4 | 2 | 8 | 2 | 6 | 7 | 4 | 2 |
| 11 | initial | 1 | 1 | 0 | 6 | 6 | 6 | 5 | -1 |
| 11 | odd | 8 | 4 | 31 | 0 | 5 | 7 | 5 | 22 |
| 19 | initial | 3 | 2 | 4 | 8 | 9 | 10 | 8 | 0 |
| 19 | odd | 8 | 1 | 31 | 0 | 9 | 9 | 8 | 23 |
| 29 | initial | 4 | 2 | 11 | 7 | 14 | 14 | 10 | 3 |
| 29 | odd | 13 | 2 | 83 | 0 | 9 | 11 | 10 | 69 |
| 297 | initial | 9 | 1 | 126 | 0 | 57 | 63 | 62 | 92 |
| 297 | odd | 118 | 3 | 7529 | 0 | 61 | 79 | 62 | 7351 |
| 1031 | initial | 39 | 1 | 2565 | 0 | 216 | 233 | 173 | 2306 |
| 1031 | odd | 456 | 10 | 112998 | 0 | 191 | 245 | 173 | 112259 |

All per-prime fiber cardinalities, actual empty-support seats, both
concrete families, tail sizes, and old/new slacks are retained in
[discovery-020.json](evidence/MANIFEST.md#log-6d74fef675bdfcb6). The diagnostic summary is
[discovery-summary-020.txt](evidence/MANIFEST.md#log-9a58aa4eadbe55a4).

## 13. Exact PrimeWorldRefinement adapter

Let A=n*n+r. The shell complete point equals primeWorldChild S A j.
For canonical refinement put a=A mod M and t=A/M. Then

  A+j*M = primeWorldChild S a j + t*M
        = primeWorldChild S a (t+j).

Divisibility by q is equivalent to the child at a,j having target
negative t*M in ZMod q. The existing existsUnique_child_eq_target
therefore supplies a unique divisible j<q. Restricting to j<K<=q
gives the at-most-one-index theorem. At n=5, S={2}, r=2, the correct
canonical parent is 1 and block shift is 13; this adapter is checked.
Raw offset r was never identified with the canonical complete parent.

## 14. Instruction 018 interaction

The whole centeredOddGapPrimeWorld exceeds the fitting modulus at every
scanned anchor n>=2. It supplies K=0 there, so it is not a source of
extra complete-period capacity. The operational fitting odd world is a
different, truncated world, and still includes q=2 among outside waves.
At n=1031 that yields maximum column occupancy 10, compared with 1 for
the initial world. Thus removing two from the coarse world does not
provide a general sparse-column improvement.

The order-four fold norm only restricts primes supporting that norm;
ordinary full-town points need not support it. Diagnostic norm-fiber
probes record this limitation. At n=1031, the old norm direction is 17:
it accounts for 300 of 2565 initial-world edges, and 1431 of 112998
odd-world edges. These restricted subsets cannot replace the actual
edge carrier. No new production restriction from 018 was established,
and its prime-power floor-sum remains deferred.

## 15. Partial tail

The tail is explicitly omitted and its size 2*n-K*M is recorded for
every row, with 0<=tail<M. The full town contains exactly K complete
blocks, not the entire shell unless the tail is zero. The strict n=5
and n=11 certificates already close without a tail. No separate tail
packet or maximal-fitting primorial selector was needed.

## 16. Remaining theorem and proposed next implementation

This checkpoint gives new bounded full-cover obstructions, so there is
no remaining support-packing bridge blocking these endpoints. For a
uniform theorem one still needs a proved family provider exceeding
pi(n), or a uniform strict vertical/packing deficit; neither is supplied
by the present hypotheses. At n=1031, the vertical slack is 160 for the
initial world and the raw-edge slack is 2306. The current universal
bounds do not approach a contradiction there.

The following are implementation proposals, not completed work:

1. Expose the exact first-endpoint deletion carrier already used in the
   neutral proof. Prove D subset V and V.card=R.card+D.card, then add the
   consumer criterion pi(n)+D.card<V.card. This avoids replacing the
   actual deletion cost by E.card. At n=1031 initial, diagnostics give
   R.card=216 against pi(n)=173 even though the raw-edge bound fails;
   a kernel certificate for this specific R would turn that observation
   into an additional endpoint. Keep all set/card computations inside
   a repository-local calibration module before promoting an algorithm.

2. Prove a neutral prime-fiber deletion bound: retain one chosen seat
   per nonempty q-fiber, and delete the other seats, obtaining a family
   with deletion cost at most sum_q max(fiber.card-1,0). Shared deletions
   should be union-counted, rather than charged once per prime. This is
   smaller than the pair-count bound but is not automatically sufficient:
   at n=1031 initial the raw fiber-deletion cost is 311, exceeding the
   available surplus 432-173=259.

3. Implement a computable support-packing certificate checker for an
   explicit R, using actual bounded divisibility and square-offset
   membership. Kernelize selected greedy discoveries such as n=297
   initial (63 seats versus 62 old primes), then n=1031 initial (233
   versus 173). The checker must certify support-disjointness and size;
   it should make no optimality claim about the search algorithm.

4. For symbolic improvement, package compatible right-index uniqueness
   into a cross-column edge bound that uses phased representatives and
   unions actual prime directions. Preserve the multi-prime overcount
   counterexample and distinguish exact compatible indices from coarse
   ceiling occupancy. Add a tail only after this sharper frontier is
   quantitatively close to a strict deficit.

Outcome A - FULL-PERIOD TOWN YIELDS A NEW FULL-COVER OBSTRUCTION
