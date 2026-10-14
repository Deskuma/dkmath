# Checkpoint 023: retained directions, symmetric packing and handoffs

The implemented carrier identities and extremum semantics are exact finite
theorems. The better selector combines the two existing deterministic
orientations. Handoff geometry adds an arithmetic exclusion but supplies no
new quantitative loss bound or independent universal uncovered-seat provider.

Implementation: neutral `FinsetSupportDirections`, application modules
`CoarseTownRetainedDirections`, `CoarseTownSymmetricDeletion` and
`CoarseTownPrimeHandoff`, and three calibration/regression modules in DkMathTest.
The Legendre facade imports the new application modules. Existing 022 endpoint
names and their proofs are preserved. Validation evidence is recorded in
[validation-023.md](validation-023.md); source reuse and limits are recorded in
[source-inventory-023.md](source-inventory-023.md).

Notation: V is the full town, T outside primes, f(a) actual bounded prime
support, F(q) the actual fiber, A active primes, U uncovered seats, I incidence,
X full-town support excess. Rleft and Rright are the existing deterministic
packing remainders. Cardinality is intended when a carrier occurs in a numeric
identity. KnownPrimeScales S is required by the application theorems that
identify actual support directions with outside primes; no full-cover premise
is required for the conservation and loss decompositions.

## 1. Exact retained-supported and represented carriers

Left retained-supported seats are Rleft.filter(f(a).Nonempty). Represented
directions are Rleft.biUnion(f), using the entire actual support at every
retained seat. Missing directions are A minus this represented union.
Retained excess is sum over Rleft of (f(a).card - 1), with natural truncated
subtraction. The right definitions replace Rleft with Rright.

Represented is a subset of A and hence T under KnownPrimeScales. Every
represented prime occurs at exactly one retained seat by pairwise disjointness
of the existing support packing. A is the disjoint union of represented and
missing directions. This does not say that different primes have different
retained seats: several primes may occur at the same retained seat.

## 2. Every uncovered seat is retained

Yes, for both orientations, without a full-cover hypothesis. An uncovered seat
has empty actual support, so no collision can delete it. Each remainder is
the disjoint union of U and its retained-supported seats. In particular,
R.card = U.card + retainedSupported.card.
Both application carrier partitions are directly exported; their cardinality
proofs use the shared exact disjoint-union theorem.

## 3. Represented cardinality and retained support excess

The exact identity represented.card = retainedSupported.card + retainedExcess
is proved for both orientations. The neutral proof combines card_biUnion for
pairwise disjoint supports with the per-seat identity between nonempty support
indicator and truncated excess. It counts primes, not just retained seats.

## 4. Exact left loss decomposition

Yes. Left loss Lleft = X - Oleft satisfies
Lleft = missingLeft.card + retainedExcessLeft.
The proof combines Rleft + Lleft = U + A with the exact retained-seat and
represented-direction partitions. It neither assumes that every prime is
represented nor assumes that each retained seat has one prime.

## 5. Simultaneous maximum semantics

A seat belongs to Rleft exactly when it belongs to V and is maximum in every
actual prime fiber supporting it. The maximum predicate is membership in F(q)
together with the bound b <= a for all b in F(q). Thus no empty-fiber default
is used. Uncovered seats satisfy the all-support condition vacuously.
The corresponding right statement uses simultaneous minima.

## 6. Representation and retained extrema

For active q the fiber is nonempty and has a unique maximum and minimum.
Given maximum a, q is left represented iff a is retained; q is left missing
iff a is deleted. The right theorems use its minimum. Predicate-to-max' and
predicate-to-min' adapters require the active nonempty-fiber proof.
An empty-fiber regression rules out both extremum predicates.

## 7. Exact max-handoff relation

MaxHandoff(q,p) means q and p are active and there exists a such that a is
the maximum of F(q) and a lies in the nonmaximum part of F(p). Equivalently,
p shares q's final seat and has a later actual seat b. The relation retains
both supporting primes, their common actual seat, and a genuine continuation.
MinHandoff uses the minimum of F(q) and the nonminimum part of F(p).

## 8. Missing directions and outgoing handoffs

For active q, missingLeft(q) iff there exists p with MaxHandoff(q,p).
Consequently representedLeft(q) iff q has no outgoing max handoff.
Both minimum-oriented equivalences are also proved. These are endpoint
semantics; they do not equate the number of missing primes with the number
of handoff edges, because one source can have several outgoing edges.

## 9. Strict ranks and cycles

Every max handoff strictly increases the fiber maximum. Every min handoff
strictly decreases the fiber minimum. Distinctness, no self edge and no
two-cycle follow. TransGen chain-rank theorems on the active-prime subtype
prove absence of every directed cycle, without selecting ranks for empty
fibers. Acyclicity alone bounds neither branching nor lost-source mass.

## 10. Cross-column arithmetic

For a max handoff ending q at a and continuing p to b > a:
p divides n^2+a, n^2+b and b-a, and b-a is positive.
The new exclusion is that q does not divide b-a. Otherwise q would support
the later full-town seat b, contradicting maximality at a. Hence p*q does
not divide this continuation gap. The tempting product-gap conjecture is
false in the opposite direction, not an unproved possible provider.

The grid adapter supplies a=r+j*M and b=s+k*M, with actual base membership
and bounded indices. It proves that p divides the signed phased gap
(s-r)+(k-j)*M in integers. It does not discard the residue phase by replacing
this gap with (k-j)*M. No general product or lcm bound across a chain was
obtained from these facts.

## 11. Uniform vertical sparsity

Under K <= p for the continuing outside prime, a strict continuation changes
base column. For fixed destination column and prime p, the destination index
and seat are unique. These results reuse the existing compatible-index
uniqueness theorem and the signed gap bridge.

They do not bound the number of source directions or destinations across
different columns. A kernel regression at n=297 satisfies uniform K <= q
for every outside prime, but source 113 hands off to both 11 and 71 from
seat 44. The continuations can use seats 88 and 328. Thus uniform sparsity
does not make the relation a tree or force out-degree at most one.

## 12. Full right conservation ledger

Implemented: nonminimum fiber seats, right deletion witnesses, multiplicity,
deletion mass, overlap, support loss, retained-supported seats, represented
and missing directions, and retained excess. Witness transpose and the
order-dual finite nonmaximum-count lemma give massRight = massLeft.
The exact right equations are:

- Dright + Oright = massRight.
- massRight + A = I.
- Rright + X = U + A + Oright.
- Oright <= X.
- Rright + Lright = U + A.

The overlap bound is unconditional; the actual outside-prime conservation
adapters carry KnownPrimeScales. Right packing subset and family facts reuse
the existing survivor APIs. No second ad hoc packing construction is added.

## 13. Exact right loss decomposition

Lright = missingRight.card + retainedExcessRight is proved. The complete
right represented and active partitions and the represented cardinality
identity are also proved. Retained excess is necessary: the n=29 initial
diagnostic has no right missing primes or outgoing handoffs but right loss 2.

## 14. Orientation identities

Both Rleft + Lleft = Rright + Lright and
Rright + Oleft = Rleft + Oright are proved under KnownPrimeScales.
At n=297 the first gives 57+12 = 60+9 = 69; the second gives
60+9 = 57+12 = 69. At n=1031 the first gives 216+56 = 210+62 = 272.
Different overlaps explain the different retained cardinalities.

## 15. Transparent better selector

If Rleft.card <= Rright.card, choose Rright; otherwise choose Rleft.
Ties explicitly choose right. The resulting carrier remains a subset of V
and a support packing family. Its cardinality is max(Rleft.card,Rright.card).
Better loss is min(Lleft,Lright), and Rbetter + Lbetter = U + A.
This is selection between two deterministic candidates; no optimization over
all packing families is claimed.

## 16. Exact better loss frontier

Under full cover, Rbetter.card <= T.card. Strict deficit T.card < Rbetter.card
therefore produces an uncovered-seat certificate and the existing prime
square-cell consumer under its operational prime-world hypotheses.
The exact equivalence is
T.card < Rbetter.card iff Lbetter + (T.card - A.card) < U.card.
The subtraction is valid because A is a subset of T. In particular, every
successful better deficit implies that U is nonempty. There is no capacity
contradiction obtained from a universe with U=0.

## 17. Kernel calibrations and finite diagnostics

The new calibration modules kernel-check the entire actual remainder carriers
and their represented support unions, then derive the missing and retained
excess counts using exact production ledgers.

| Initial town | U | A | Orientation | R | represented | missing | retained excess | loss |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 297 | 29 | 40 | left | 57 | 31 | 9 | 3 | 12 |
| 297 | 29 | 40 | right | 60 | 32 | 8 | 1 | 9 |
| 1031 | 144 | 128 | left | 216 | 80 | 48 | 8 | 56 |
| 1031 | 144 | 128 | right | 210 | 75 | 53 | 9 | 62 |

At 297 the selector chooses right and the separately named endpoint uses
58 < 60. At 1031 it chooses left and uses 169 < 216. Existing 022 endpoint
names remain in the dependency audit. Their endpoint strength is preserved;
these new names package the transparent selection and decompositions.

The 602-row diagnostics extend the prior worlds with both represented unions,
missing counts, retained excess, exact loss residuals, handoff edges, chain
depth, mirrored mass and overlap, and better choices. Both residuals are zero
in every row. Capacity counts are left 570, right 572, better 586. Better is
exactly their union, so it adds no world beyond the combined 022 certificates.

At initial n=29, represented counts are 6/6, missing 0/0, retained excess
0/2, loss 0/2 and remainders 14/12; better chooses left. This mandatory anchor
is independently reconstructed in the diagnostics, not newly kernel-certified
by a 023 calibration module. At 297 handoff edges/depth are 13/1 and 10/2;
at 1031 they are 81/2 and 79/2. These edge/depth counts are diagnostic facts.

## 18. Provider test and rejected conjectures

No new symbolic quantitative loss bound stronger than L <= X was obtained.
Strict rank, column change and fixed destination uniqueness do not control
source multiplicity. Counting supported handoff destinations does not provide
an injection of missing directions into those destinations. Shared terminal
seats also prevent replacing represented cardinality by supported cardinality.
Charging all collision incidences falls back to existing excess accounting.

The discovery file preserves the smallest counterexamples in its scanned
worlds, and kernel regressions establish their actual finite claims:

- n=6, odd world S={3}: max handoff 5->2, so acyclicity does not force loss zero.
- n=6, same world: a=4, b=8, p=2, q=5; 10 does not divide gap 4.
- n=7, odd world S={3}: right terminal primes 2 and 5 share minimum seat 1.
- n=8, odd world S={3}: source 5 hands off to both 2 and 7.

The 297 uniform branching regression separately rules out repairing the
branching argument by adding only uniform K <= outside prime. Smallest means
smallest encountered in the recorded scan, not a universal minimality theorem.
The q-not-dividing-gap theorem is new arithmetic information, but it is not a
cardinality estimate and does not qualify as a new loss bound.

## 19. Exact route limit

The deterministic method is now an exact finite certificate framework.
Its stronger semantics explain what it preserves and loses. The frontier
requires positive uncovered mass together with a finite loss comparison;
the current packing and handoff identities do not independently prove that
mass exists for every operational town. Selecting the better direction
improves either fixed orientation, while recovering precisely the already
available union of the two finite certificate sets.

This closes the claim that acyclicity or destination uniqueness alone supplies
a universal provider. It does not prove that every future arithmetic estimate
involving these carriers is impossible. No Legendre proof, analytic prime
estimate, terminal-seat injection, or universal positive-U theorem is claimed.

## 20. Single next theorem and implementation proposal

Attempt a source-multiplicity product bound at one handoff seat. In an
operational world S=primeScalesUpTo(P), let a be an actual full-town seat,
p an outside prime with a nonmaximum in F(p), and Q the finite set of active
directions whose fiber maximum is a. Propose:

p * (P+1)^Q.card <= n^2+a.

Each q in Q is a distinct prime above P dividing n^2+a. Also p is not in Q,
since p continues beyond a. Thus p times the product of Q divides the
positive complete point n^2+a; lower-bounding each q by P+1 should yield the
displayed inequality. Every q in Q is missing because its maximum a is
deleted by p. This directly targets multiplicity of lost source directions
at one seat, which fixed destination-index uniqueness does not control.

Implement first a generic finite distinct-prime product divisibility lemma
only if no existing Mathlib API fits, then an application adapter using actual
fiber membership, operational outside-prime lower bounds and full-town seat
positivity. Calibrate it on shared source seats before attempting aggregation.
It needs no cyclotomic machinery or valuation floor sum. This is a concrete
proposal, not a theorem implemented in 023, and even a proof would not by
itself produce universal uncovered mass or a global loss frontier.

Outcome C - RETAINED-DIRECTION THEORY CLOSES THE PACKING ROUTE
