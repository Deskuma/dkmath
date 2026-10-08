# Source inventory 033 - Collision-safe prime products

The live checkout starts clean after committed checkpoint 032. Instruction 033
is the bounded contract; earlier production modules are reused without edits.

## Existing receivers inspected

- GnomonCofactorLeastFactor already defines the independent endpoint factor
  cover, proves its product is a surviving composite, and defines the
  diagonal product image and square lower mass. It supplies the actual
  cofactor-window geometry required here.
- Internal.PairCombinatorics.upperPairs and its binomial-cardinality theorem
  represent strict pairs p<q. They exclude the diagonal and concern generic
  support combinatorics, not the present quotient endpoints.
- PairOverlap.squarePrimePairs uses primes up to n and strict pair ordering.
  Its wave overlap theorems concern divisibility occupancy of square offsets,
  not exact semiprime products inside cofactor windows.
- ParitySafeSqrtRoughProductWaves.roughPairs uses upperPairs of actual active
  rough labels. Its support/cutoff hypotheses differ from the 031 carrier.
  Importing that stack would not identify the required endpoint witness.
- Nat.Prime.dvd_mul, Nat.Prime.dvd_iff_eq and positive multiplication
  cancellation give product uniqueness for two ordered prime factors.
- Finset.sum_image transports pair weights only after injectivity is proved.
  sum_le_sum_of_subset_of_nonneg gives the distinct-product lower mass.

## Chosen minimal extension

Filter the existing 032 endpoint cover by primality of its complementary
factor. Its first factor is already prime and the order is already r<=s.
This includes squares and off-diagonal semiprimes in a single carrier.
No new general pair framework or complete target factorization is introduced.

For two equal products, a prime first factor divides one of the other pair's
prime factors. In the same orientation, cancellation gives equality of both
factors. In the reversed orientation, the two ordering inequalities force
equality as well. This is the proved collision-safe product injection.

The product image is a subset of the old surviving composite carrier. Its
log mass D is therefore a lower error witness. The 032 square image is a
subset of this image; squares are not charged twice. One new envelope and
one exact-ledger consumer complete the production extension.
