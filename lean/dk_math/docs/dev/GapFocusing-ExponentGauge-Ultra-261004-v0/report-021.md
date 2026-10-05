# Report 021 - Exact deletion capacity certificates

This checkpoint exposes exact deterministic deletion and a computable
checker for the existing OldSupportCapacity predicate. It preserves
actual bounded support semantics, adds separately named finite endpoints,
and does not provide a universal Legendre family provider.

Source audit: [source-inventory-021.md](source-inventory-021.md).
Milestones: [findings-021.md](findings-021.md).
Validation: [validation-021.md](validation-021.md).

## 1. Public generic definitions

supportCollisionDeletionVertices V f is the image of Prod.fst on the
unchanged supportCollisionEdges V f. supportPackingRemainder V f is
V with these vertices removed. The exact deletion membership theorem
says a is deleted exactly when some edge (a,b) exists. Remainder
membership says a is in V and is not deleted.

Implementation: [FinsetSupportPacking.lean](../../../DkMath/Combinatorics/FinsetSupportPacking.lean).

## 2. Exact subset

supportCollisionDeletionVertices_subset proves D subset V directly from
edge membership. supportPackingRemainder_subset proves R subset V.
No cardinality approximation is used in either set statement.

## 3. Exact disjoint partition

The named theorems disjoint_supportPackingRemainder_deletion and
supportPackingRemainder_union_deletion prove Disjoint R D and R union D=V.
These are exact equalities for every finite support family under the
existing generic order and decidable equality assumptions.

## 4. Exact additive cardinality

card_supportPacking_partition proves V.card=R.card+D.card.
card_supportCollisionDeletionVertices_le_edges proves D.card<=E.card.
The old exists_supportPacking proposition is unchanged; its proof now
uses the public exact packet and the image-cardinality inequality.
The coarse specialization also supplies R.card=V.card-D.card as a
Nat subtraction rewriting theorem.

## 5. Remainder support-disjointness

supportPackingRemainder_pairwiseDisjoint is the named first-endpoint
proof: a remaining collision would delete its smaller endpoint.
supportPacking_exact_packet bundles subset, pairwise-disjointness, and
the exact cardinality partition. R is deterministic but is not claimed
maximal or optimal. The optional right-endpoint variant proves its
subset, exact cardinality partition, and pairwise-disjointness as well.

## 6. Specialized coarse carrier

coarseTownDeletionVertices S n and coarseTownPackingRemainder S n are thin
abbreviations at fullTown and squareOffsetPrimeSupport n. Their public
membership, subsets, disjoint union, family, and exact partition adapters
reuse the generic theorems. The seat condition comes from the existing
fullTown inclusion in squareOffsets. For a certified world, the period
partition is K*totient(M)=R.card+D.card.

Implementation: [CoarseTownDeletionCapacity.lean](../../../DkMath/NumberTheory/Legendre/CoarseTownDeletionCapacity.lean).

## 7. Exact deletion-deficit consumer

The hypothesis pi(n)+D.card<V.card implies pi(n)<R.card by exact
partition. The two public consumers are
not_fullyCovered_of_coarseTown_deletion_deficit and
exists_prime_squareCell_of_coarseTown_deletion_deficit.
They delegate to the established OldSupportCapacity non-full-cover and
prime-square-cell theorems. No second capacity proof was introduced.

## 8. Formal comparison with edges

coarseTown_deletion_deficit_of_edge_deficit proves the theorem-level
implication from pi(n)+E.card<V.card to pi(n)+D.card<V.card, using
D.card<=E.card. The implication is strict as a finite numerical test.
At n=6, S={3}, Lean checks V.card=8, E.card=6, D.card=3, and pi(n)=3:
the deletion test succeeds while the edge test fails. This also witnesses
several collision edges sharing deleted first endpoints. The existing
n=11 edge-packing endpoint from 020 remains named and checked.

## 9. n=1031 symbolic deletion route

The new calibration theorem
DkMathTest.LegendreDeletion1031Calibration.exists_prime_squareCell_1031_of_coarseTownDeletion
has conclusion exists p, p.Prime and SquareCell 1031 p. It consumes the
production deletion carrier for S=primeScalesUpTo 10 and the existing
OldSupportCapacity theorem. No concrete prime is selected or exposed.

The exact deletion computation is compressed through a production equality:
D is the union, over actual old prime q, of its divisibility fiber with
the largest seat omitted. Every first endpoint is a non-maximum element
of some common-prime fiber, and every such element has a later colliding
seat. This is an equality to D, not a different search-generated family.

## 10. Exact large cardinalities

The checked facts are M=210, K=9, base.card=48, V.card=432,
pi(1031)=173, D.card=216, and R.card=216. The last fact follows from
symbolic exact partition after the deletion count is kernel-evaluated.
Thus 173+216<432, equivalently 173<216, supplies the endpoint.

Raw E.card=2565 remains the independently reconstructed diagnostic value;
it is not needed as a large kernel-evaluation premise. A checked q=11
fiber has 39 seats and hence 741 collision edges inside the actual edge
carrier. That lower bound already proves the edge deficit fails at 1031,
while the checked deletion deficit succeeds. Both the large strictness
witness and the cheaper n=6 witness are formal regressions.

## 11. Prior route and provenance

The exact earlier theorem is
DkMathTest.LegendreSqrtQuotientCalibration.quotient1031_structural_endpoint.
It uses reduced-quotient accounting and rejection lower bounds.
LegendreResidueCoverCalibration.residue1031_preserved_endpoint reexports
that route. The new deletion endpoint retains its own name and proof.
The provenance regression references both named routes to the same
existential conclusion. Neither proof is replaced by the other.
This is proof-path provenance, not a claim of stronger logical independence.

## 12. Stable certificate-checker API

OldSupportCapacityCertificate n R is precisely the conjunction of the
existing PairwiseOldSupportDisjointSquareSeatFamily and pi(n)<R.card.
checkOldSupportCapacityCertificate returns a Boolean by checking:

- every input seat lies from 1 through 2*n;
- each actual prime q<=n divides at most one input complete point;
- the seat cardinality exceeds the bounded prime count.

The semantic equivalence theorem is
checkOldSupportCapacityCertificate_eq_true_iff. Its proof relates
fiber cardinality at most one to actual support pairwise-disjointness.
The endpoint wrapper delegates to OldSupportCapacity. No support labels
are accepted as trusted input. The n=3 family {1,2,4,5} lies in the shell
and is large enough, but the checker rejects it because shared q=2
violates the support condition.

Implementation: [OldSupportCapacityCertificate.lean](../../../DkMath/NumberTheory/Legendre/OldSupportCapacityCertificate.lean).

## 13. Explicit n=297 certificate

The exact initial-world discovery family was read from discovery-020.json,
sorted, and represented as a List converted to Finset. It has 63 seats;
Lean checks the entire Boolean certificate and pi(297)=62. The semantic
certificate yields
DkMathTest.LegendreCapacity297Calibration.exists_prime_squareCell_297_of_explicitCapacityCertificate.
Python only supplied the candidate list. Actual bounded divisibility,
shell membership, disjointness, and the capacity comparison are kernel
certified. The endpoint is existential, without a selected prime witness.

## 14. Optional explicit n=1031 family

The optional sorted discovery family has 233 seats against 173 old primes.
It is checked only after the deterministic symbolic deletion endpoint.
Its separate Boolean certificate recomputes actual divisibility over a
kernel-verified bounded prime inventory. The data and exact checker results
are retained in LegendreCapacity1031Calibration. This search-found family
is neither canonical nor claimed optimal, and it does not replace the
216-seat deterministic deletion proof.

## 15. Representation, kernel method, and performance

Four encodings were considered:

- Finset literals are concise, but nested insert/dedup reductions grow.
- Sorted List.toFinset is explicit and adequate for the 63-seat family.
- A range/filter expression is mathematically compact but repeats square
  phase, modulus, and divisibility reductions in large computations.
- The 48-by-9 coordinate expansion is ideal for the full-period geometry;
  a checked linear list expansion connects it to an explicit finite carrier.

For larger carriers the final data representation is a sorted List embedded
as a Finset with a distinctness proof. Adjacent increasing comparisons are
kernel-decided; transitivity proves pairwise order and hence distinctness.
The large town list equals the expansion of the 48 base representatives
through nine streets. This checked equality proves the exact production
carrier, avoiding a quadratic image-equality or all-pairs membership check.
The old prime list is likewise checked against the production inventory.

All finite evaluation uses decide +kernel, checked list rewrites, or
symbolic finite-cardinality theorems. No compiled decision shortcut or
extra evaluation axiom is used. The data lists are never accepted without
their exact production equality or checker proof.

Two early strategies were interrupted before a result: direct evaluation
of the full fiber expression, and direct large-carrier equality. A
coordinate-membership compression then succeeded: its timed build took
201.85 seconds with peak RSS 18325692 KiB, including 173 seconds for data
and 21 seconds for the deletion calibration. The final revision uses
linear list expansion and adjacent comparisons: its timed build took
167.16 seconds with peak RSS 18325300 KiB (138 seconds for data and
21 seconds for the calibration). The optional 233-seat checker build took
18.41 seconds with peak RSS 7385024 KiB (11 seconds for that module).
Final timings are recorded in the validation artifact and performance logs; they are whole build
measurements, not an isolated single theorem microbenchmark.
The n=297 check took 23.50 seconds and 2761828 KiB peak RSS.

## 16. Orientation and prime-fiber comparison

The bounded comparison uses the same 602 operational worlds as 020.
Counts of families exceeding pi(n) are left deletion 504, right deletion
492, the better endpoint choice 534, and diagnostic greedy packing 591.
The raw edge criterion succeeds in 41 rows. Both orientations are
support-disjoint by the generic proof; neither is uniformly better.

| n | world | V | E | left D | right D | left R | right R | greedy | pi | fiber sum |
|---|---|---|---|---|---|---|---|---|---|---|
| 3 | initial | 3 | 0 | 0 | 0 | 3 | 3 | 3 | 2 | 0 |
| 3 | odd | 4 | 1 | 1 | 1 | 3 | 3 | 3 | 2 | 1 |
| 5 | initial | 5 | 1 | 1 | 1 | 4 | 4 | 4 | 3 | 1 |
| 5 | odd | 6 | 6 | 3 | 3 | 3 | 3 | 3 | 3 | 3 |
| 8 | initial | 4 | 0 | 0 | 0 | 4 | 4 | 4 | 4 | 0 |
| 8 | odd | 10 | 8 | 4 | 4 | 6 | 6 | 7 | 4 | 5 |
| 11 | initial | 6 | 0 | 0 | 0 | 6 | 6 | 6 | 5 | 0 |
| 11 | odd | 14 | 31 | 9 | 7 | 5 | 7 | 7 | 5 | 10 |
| 19 | initial | 12 | 4 | 3 | 2 | 9 | 10 | 10 | 8 | 3 |
| 19 | odd | 16 | 31 | 7 | 10 | 9 | 6 | 9 | 8 | 10 |
| 29 | initial | 18 | 11 | 4 | 6 | 14 | 12 | 14 | 10 | 7 |
| 29 | odd | 24 | 83 | 15 | 13 | 9 | 11 | 11 | 10 | 17 |
| 297 | initial | 96 | 126 | 39 | 36 | 57 | 60 | 63 | 62 | 48 |
| 297 | odd | 240 | 7529 | 179 | 177 | 61 | 63 | 79 | 62 | 268 |
| 1031 | initial | 432 | 2565 | 216 | 222 | 216 | 210 | 233 | 173 | 311 |
| 1031 | odd | 912 | 112998 | 721 | 720 | 191 | 192 | 245 | 173 | 1235 |

The maximum-retaining prime-fiber union is exactly left endpoint deletion:
route B, equivalent geometry with a useful kernel computation compression.
The sum of fiber.card-1 without union overlap is too weak at n=1031
initial: 311 exceeds the deletion surplus 432-173=259, whereas the actual
union deletes only 216. At n=297 initial, both deterministic orientations
fail (57 and 60 retained versus 62 primes), while the checked 63-seat
certificate succeeds. No nontrivial hitting-set algorithm was introduced.

The 1031 initial remainder has 144 empty-support seats and 72 supported
retained seats in diagnostics. Across the 48 columns, retained-card counts
are: four columns retain 2 seats, eight retain 3, ten retain 4, fifteen
retain 5, nine retain 6, one retains 7, and one retains 8. None retains
zero, one, or nine seats. The first eight columns losing most seats and
the exact per-column lists are preserved in the discovery artifact.
Largest deletion-prime contributions are q=11 (38), 13 (31), 17 (24),
19 (21), 23 (18), 29 (13), 31 (12), and 37 (10). Contributions overlap.
The total 216 happens to be half of 432; this observation has not been
promoted to a structural half-town theorem. These finer structural counts
are diagnostics, distinct from the checked total cardinalities.

Complete data: [discovery-021.json](logs/discovery-021.json).

## 17. Narrowest next symbolic provider

The finite endpoints are complete. A universal endpoint still requires
an actual symbolic packing-size bound. The narrowest useful next API is
a maximum-of-prime-fibers selector and a proved bound on the union cost,
not additional prime-power valuation precision.

Proposed next implementation, not completed work:

1. Expose exact remainder membership: a is retained precisely when it is
   in V and is the maximum seat in every nonempty old-prime fiber that
   contains it. Then prove a column-aware upper bound on the union of
   non-maximum fiber seats. It must improve the raw sum through proved
   overlaps or phased constraints, rather than assuming independence.

2. Add a transparent better-endpoint packet, selecting the smaller of
   first- and second-endpoint deletion costs. Its symbolic family proof
   follows from the two existing neutral packets. Kernel-check a small
   strict orientation witness before considering a uniform gain; the
   534-row success count alone is not a universal theorem.

3. To improve beyond both orientations, expose a checkable symbolic
   cross-column retained-family construction. The n=297 certificate gives
   a concrete acceptance target: 63 seats against 62 directions, while
   endpoint deletion retains at most 60. Keep search outside the theorem
   assumptions and make the provider output an actual checked family.

4. Choose a canonical fitting world only after a proved selector bound
   makes the choice useful. Do not seek the 018 floor-sum while the
   unresolved inequality is a cross-support deletion or packing bound.

Outcome A - EXACT DELETION CARRIER ADDS NEW KERNEL ENDPOINTS
