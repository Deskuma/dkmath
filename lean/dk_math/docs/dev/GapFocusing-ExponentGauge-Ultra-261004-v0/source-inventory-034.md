# Source inventory 034 - Ordered prime triples

The checkout starts clean after committed checkpoint 033. Instruction 034 is
the bounded contract. Earlier production modules are reused without edits.

## Inspected receivers

- ParitySafeSqrtRoughProductWaves.roughTriples uses strict ordered active labels
  p<q<s and support-wave incidence. Its hypotheses and carrier differ from
  cofactor windows, and repetitions are excluded.
- Internal pair/triple combinatorics gives strict support representatives,
  not ordered multiplicity-preserving factor triples.
- The 033 semiprime product carrier supplies the earlier certified image and
  lower mass, and the 032 factor cover supplies the quotient interval idea.
- Nat.primeFactorsList_unique is the existing unique factorization receiver:
  any finite list of primes with a given product is a permutation of its
  primeFactorsList. List.Perm.eq_of_pairwise' turns a permutation between
  ordered lists into equality, retaining repeated factors.
- List.Perm.length_eq distinguishes two-prime from three-prime products.
  No new factor-count function or general factor-depth framework is required.
- Positive natural quotient inequalities and Nat.sqrt bounds enumerate the
  complementary endpoint interval. Coprime multiplication proves wheel survival.
- Finset.sum_image and sum_union transport product weights after injection
  and disjointness, and sum_le_sum_of_subset_of_nonneg gives the lower witness.

## Chosen bounded extension

Enumerate r prime with r^3<=B, then s prime with r<=s<=sqrt(B/r), then t prime
with max(s,A/(r*s)+1)<=t<=B/(r*s), each coprime to the existing wheel product.
No target minFac, actual composite filter or carry inventory defines this set.
Use sorted prime-list uniqueness for product injectivity, and list lengths
for disjointness from the semiprime image. A combined product union gives one
mass and one new upper envelope. No four/five-factor API is implemented.
