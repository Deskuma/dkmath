# Report 022: survivor capacity and exact deletion conservation

The outside-prime universe adds a deterministic endpoint at n=297. Exact
conservation also reveals a limitation stronger than the proposed comparison:
deletion overlap never exceeds support excess, even without full cover.
Consequently the uncovered-free strict conservation condition is impossible.
The useful exact frontier must retain uncovered seats.

Notation: V=fullTown, T=outside primes, D=left deletion, R=left remainder,
A=active outside primes, U=uncovered town seats, I=incidence, X=support excess,
Mdel=deletion mass, O=deletion overlap. Cardinalities are implicit for carriers.
S is certified throughout support-localization results. Unconditional means
no full-cover assumption; it does not remove KnownPrimeScales S.

## 1. Generic support-universe capacity

DkMath.Combinatorics.card_le_supportUniverse proves R.card <= T.card from
nonempty supports, containment in T, and pairwise disjointness. Its proof uses
card_biUnion exactly. The statement does not assume arithmetic or an ordering
on seats. FinsetSupportPacking remains independent of NumberTheory.

## 2. Correct survivor capacity universe

coarseFullTown_survivor and coarse_survivor_support_outside show that actual
support of every town seat is contained in coarseOutsidePrimes S n. This is
primeScalesUpTo n with S removed, including when S contains primes above n.
No precomputed support labels are used.

## 3. Sharper full-cover bound

card_fullTown_pairwiseOldSupportDisjoint_le_outsidePrimes_of_fullyCovered
proves R.card <= T.card for any old-support-disjoint family inside V.
Strict excess gives not_fullyCovered_of_fullTown_survivor_capacity and a prime
consumer. A single adapter reuses Frontier escape and existing primality
arithmetic; all other new prime consumers delegate to it.

## 4. Exact left-deletion deficit

not_fullyCovered_of_coarseTown_outside_deletion_deficit consumes T+D<V.
exists_prime_squareCell_of_coarseTown_outside_deletion_deficit adds n>0.
The old-world criterion implies this criterion by T subset old primes.
Instruction 021 declarations and their original endpoints are unchanged.

## 5. Right deletion specialization

coarseTownRightDeletionVertices and coarseTownRightPackingRemainder specialize
the existing right projection. Subset, family, exact partition and outside
capacity consumers are public. coarseTownRightDeletionVertices_eq_fibers
proves exact compression by erasing the minimum of every nonempty arithmetic
prime fiber. There is no second collision relation and no optimality claim.
Optional better-of-two and symmetric production conservation are deferred.

## 6. Deterministic n=297 endpoint

LegendreSurvivor297Calibration kernel-checks M=210, K=2, V=96, T=58, old=62,
Dleft=39, Rleft=57, Dright=36, Rright=60.
exists_prime_squareCell_297_of_right_survivor_deletion consumes 58+36<96.
Its module imports production only. It does not import or use the explicit
63-seat certificate. The existing explicit endpoint remains separately named
exists_prime_squareCell_297_of_explicitCapacityCertificate.
The identical right selector fails the old comparison 62<60, so the new
capacity universe provides a strict improvement, not a different search.

## 7. Deterministic n=1031 survivor endpoint

LegendreSurvivor1031Calibration checks T=169 and reuses the 021 production
D=216, R=216, V=432 cards. The stronger endpoint is
exists_prime_squareCell_1031_of_survivor_deletion, consuming 169+216<432.
The original exists_prime_squareCell_1031_of_coarseTownDeletion still uses
173+216<432. This is proof-route provenance, not logical independence.

## 8. Exact carrier definitions

Active filters T by actual prime-fiber nonemptiness. Uncovered filters V by
empty actual support. SupportExcess sums support.card-1 over V, with zero
contribution at empty support. NonmaximumFiberSeats filters each actual fiber
by existence of a larger seat in that fiber. WitnessPrimes filters T by
membership in these nonmaximum fibers; deletionMultiplicity is its card.
DeletionMass sums multiplicity over V. DeletionOverlap sums multiplicity-1
over D. Exact membership and deletion/fiber-compression equivalences are
proved. Empty and nonempty maximum-fiber boundary cases are public.

## 9. Deletion mass plus activity

coarseTownDeletionMass_eq_nonmaximum_sum transposes witness incidence exactly.
The per-fiber identity nonmaximum.card+nonempty-indicator=fiber.card proves
coarseTownDeletionMass_add_active_eq_incidence: Mdel+A=I. This theorem does
not require full cover or certification of S; both sums use the same T.

## 10. Distinct deletion plus overlap

card_deletion_add_overlap_eq_mass proves D+O=Mdel. Certified survivor support
makes positive multiplicity equivalent to membership in D. Multiplicity
vanishes outside D, and deleted-seat multiplicity is positive. O is union
compression of repeated witness charges, not the collision edge count.

## 11. Master conservation

The existing actual incidence transpose supplies the seat ledger I+U=V+X.
The new prime ledger gives D+O+A=I. Together with V=R+D these prove
coarseTown_remainder_conservation: R+X=U+A+O. Every cancellation uses additive
Nat equalities. The theorem assumes certified S, with no full-cover premise.

## 12. Full-cover specialization

Full cover implies the local uncovered carrier is empty, and the master
becomes R+X=A+O. Empty town support is a local obstruction, and empty U does
not establish cover of the entire square shell. No global provider is proved.

## 13. Necessary frontier and its unexpected limitation

The requested full-cover frontier A+O<=T+X and strict-reverse prime consumer
are implemented. But coarseTownDeletionWitnessPrimes_subset_support proves
multiplicity(a)<=support(a).card. Summing excess over deleted seats, then
using D subset V, proves coarseTownDeletionOverlap_le_supportExcess: O<=X
UNCONDITIONALLY. Since A<=T, coarseTown_conservation_frontier_unconditional
also proves A+O<=T+X unconditionally. The strict-reverse consumer has an
impossible hypothesis for actual support. It cannot serve as a universal
provider, irrespective of additional PrimeWorld geometry.

## 14. Comparison with direct deficit

The exact unconditional equivalence is T+D<V iff T+X<U+A+O. The version
omitting U is only equivalent when U is empty; its proposed strict inequality
is in fact impossible. The smallest positive counterexample to unconditional
equivalence is kernel-checked n=1,S=empty: V=2,U=2 and all other terms zero.
A nonempty-world example n=5,S={2} has T=2,R=4,A=2,U=2,X=O=0.
Both direct deficits hold, while both uncovered-free comparisons fail.
Thus conservation does not strengthen the selector. The uncovered-free test
has strictly less detection power than the direct deficit: its antecedent
is stronger and impossible.

A useful Nat-safe corrected coordinate is L=X-O. The proved bound O<=X gives
O+L=X, hence R+L=U+A. The public equivalence is
T+D<V iff L+(T-A)<U. A prime consumer exposes this exact loss frontier.

## 15. Conservation values and bounded diagnostics

All initial-world entries in this table have kernel-checked production cards
or coordinates derived from kernel-checked cards and the exact ledgers.
The odd n=11 row is an additional positive-overlap calibration.

| n and world | V | T | A | U | I | X | D | R | Mdel | O | inactive | L |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 5 initial | 5 | 2 | 2 | 2 | 3 | 0 | 1 | 4 | 1 | 0 | 0 | 0 |
| 11 initial | 6 | 3 | 2 | 4 | 2 | 0 | 0 | 6 | 0 | 0 | 1 | 0 |
| 11 odd | 14 | 4 | 3 | 4 | 13 | 3 | 9 | 5 | 10 | 1 | 1 | 2 |
| 19 initial | 12 | 6 | 5 | 6 | 8 | 2 | 3 | 9 | 3 | 0 | 1 | 2 |
| 29 initial | 18 | 8 | 6 | 8 | 13 | 3 | 4 | 14 | 7 | 3 | 2 | 0 |
| 297 initial | 96 | 58 | 40 | 29 | 88 | 21 | 39 | 57 | 48 | 9 | 18 | 12 |
| 1031 initial | 432 | 169 | 128 | 144 | 439 | 151 | 216 | 216 | 311 | 95 | 41 | 56 |

At 297: 57+21=29+40+9=78. At 1031: 216+151=144+128+95=367.
At 1031, R=U+A-L=144+128-56=216. The numerical condition for half the
town is 2*(U+A)=V+2*L: 544=432+112. This does not follow from a general
half-town law; the other checked anchors refute any universal half claim.

The independent 602-row diagnostic scan covers both operational worlds for
n=1..300 and n=1031. All left and right conservation residuals are zero.
Outside capacity succeeds 570 times on the left and 572 on the right.
Uncovered-free conservation succeeds zero times, as the new universal bound
predicts. Signed O-X is diagnostic only. Python output is never a Lean
premise. Large 1031 checks rewrite through the existing kernel-certified town
and prime inventories; they do not enumerate all collision edges.

## 16. Right-versus-left structural rule

At 297 both orientations have common incidence 88, active 40, support excess
21 and prime-fiber deletion mass 48. Diagnostic right overlap is 12 versus
left overlap 9, so the right union cost is smaller by 3: 36 versus 39, and
its remainder is larger by 3: 60 versus 57. In loss coordinates, the left
comparison is 12+18<29 (false), while the right is 9+18<29 (true).
Candidate symmetric theorem:
Rright+Oleft=Rleft+Oright. Kernel right cards and the left master are proved;
a full production right-overlap API is deferred. No orientation dominates:
at 1031 right remainder is 210 and left is 216 in the independently checked
diagnostics; at 29 the left also wins. Periodic min/max witness repetition,
not independent prime waves, controls this finite difference. The explicit
63-seat family at 297 remains a search certificate and is not needed here.

## 17. Next implementation proposal

Attack the single correct inequality L+(T-A)<U, where L=X-O, rather than
trying to force O>X+(T-A): the latter is mathematically impossible for this
actual-support selector. A next bounded module should characterize retained
supported seats, prove L is the sum of unrepresented active directions and
retained-seat support excess, and mirror the minimum-fiber loss ledger. Then a transparent better-of-two
selector minimizes the two losses, with no claim of optimal packing.
A useful geometry theorem would bound this lost-direction count from
cross-column repeated witnesses while controlling inactive directions.
Actual positive lower bounds for U remain necessary for the direct finite
capacity frontier; no analytic or global prime-existence input is hidden.
Do not resume the 018 prime-power floor sum unless it directly bounds one
of these exact terms. This checkpoint proves finite identities, conditional
capacity and named finite endpoints, not Legendre's conjecture.

Validation evidence is recorded in [validation-022.md](validation-022.md).
The source audit is [source-inventory-022.md](source-inventory-022.md), and
milestone findings are [findings-022.md](findings-022.md).

Outcome A - SURVIVOR-WORLD CAPACITY ADDS NEW DETERMINISTIC ENDPOINTS
