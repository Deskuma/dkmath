# GNPC-004 report

## Outcome

Outcome A — the prime-target residue/degree-divisibility filter is formally
available for positive nondegenerate GN representations.

For `GN d x u = p` with `GNPositiveRepresentation p d x u` and `p` prime,
the verified chain is:

```text
d is prime
  ↓
d ∤ x
  ↓
p ≡ 1 [MOD d]
  ↓
d ∣ p - 1
```

The proof reuses existing GN degree and weighted-congruence layers.  It does
not expand `GN` into a fresh binomial-sum proof and does not claim any
converse or representation classification.

## Reused DkMath API

The exact existing congruence theorems reused from
`DkMath.NumberTheory.WeightedGNBridge` are:

```lean
prime_GN_modEq_rightBoundary
    {p x u : ℕ} (hp : p.Prime) :
    GN p x u ≡ x ^ (p - 1) [MOD p]
```

```lean
prime_GN_modEq_one_of_not_dvd_x
    {p x u : ℕ} (hp : p.Prime) (hx : ¬ p ∣ x) :
    GN p x u ≡ 1 [MOD p]
```

The GNPC-002 and GNPC-003 APIs reused are:

```lean
GNPositiveRepresentation.bounds
GNPositiveRepresentation.degree_prime_of_target_prime
```

The repository search for existing GNPC-004 declarations was run before
editing:

```text
rg -n 'degree_not_dvd_boundary|target_modEq_one_degree|degree_dvd_target_sub_one|prime_degree_constraints|GNPrimeTargetResidue' DkMath DkMathTest docs
```

No pre-existing GNPC-004 theorem or owner module was found; the matches were
the instruction document itself.

## Mathlib API and arithmetic bridge

For equality of prime divisors, the implementation uses:

```lean
Nat.prime_dvd_prime_iff_eq
```

For the zero congruence and the power divisibility step, it uses:

```lean
Nat.modEq_zero_iff_dvd
dvd_pow
```

For the final natural-number conversion from `p ≡ 1 [MOD d]` to
`d ∣ p - 1`, the exact API is:

```lean
Nat.modEq_iff_dvd'
```

applied to the symmetric congruence `1 ≡ p [MOD d]` and `1 ≤ p` from
`Nat.Prime.one_lt`.

## Owner and changed files

The new thin owner is:

```text
DkMath/NumberTheory/GNPrimeTargetResidue.lean
```

Its imports are:

```lean
import DkMath.NumberTheory.GNDegreeFactorization
import DkMath.NumberTheory.WeightedGNBridge
```

Changed files:

```text
DkMath/NumberTheory/GNPrimeTargetResidue.lean
docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-004.md
```

No aggregator or existing GN declaration was modified.

## Final theorem surface

### P0 — boundary nondivisibility

```lean
theorem DkMath.NumberTheory.GNPositiveRepresentation.degree_not_dvd_boundary_of_target_prime
    {p d x u : ℕ}
    (hrep : GNPositiveRepresentation p d x u)
    (hp : Nat.Prime p) :
    ¬ d ∣ x
```

### P1 — target residue

```lean
theorem DkMath.NumberTheory.GNPositiveRepresentation.target_modEq_one_degree_of_target_prime
    {p d x u : ℕ}
    (hrep : GNPositiveRepresentation p d x u)
    (hp : Nat.Prime p) :
    p ≡ 1 [MOD d]
```

### P2 — degree divisibility

```lean
theorem DkMath.NumberTheory.GNPositiveRepresentation.degree_dvd_target_sub_one_of_target_prime
    {p d x u : ℕ}
    (hrep : GNPositiveRepresentation p d x u)
    (hp : Nat.Prime p) :
    d ∣ p - 1
```

### P3 — packaged filters

```lean
theorem DkMath.NumberTheory.GNPositiveRepresentation.prime_degree_constraints
    {p d x u : ℕ}
    (hrep : GNPositiveRepresentation p d x u)
    (hp : Nat.Prime p) :
    Nat.Prime d ∧ d ∣ p - 1 ∧ 2 ^ d - 1 ≤ p
```

The floor component is obtained directly from
`GNPositiveRepresentation.bounds`.

## Validation

Command run from `lean/dk_math`:

```text
lake build DkMath.NumberTheory.GNPrimeTargetResidue
```

Result: success (`Build completed successfully (8673 jobs).`) with no Lean
warnings.

The new module was audited for `sorry` and `axiom`; neither was added.
`git diff --check` was run successfully.

The optional executable `GNPrimeDegreeCandidates` filter was not added.  The
required P0–P3 surface was sufficient for this checkpoint, so no finite
candidate-set API was introduced.

## Deferred items

- executable degree candidate `Finset` filtering;
- cyclotomic factorization;
- uniqueness or classification of `(x,u)` representations;
- primitive-prime / Zsigmondy existence;
- converse claims such as `d ∣ p - 1 → ∃ x u, GN d x u = p`;
- sufficiency of prime degree for GN primality;
- ABC, FLT, Legendre, and RH applications;
- logarithmic/root-based search-box optimization;
- arbitrary semiring generalization and repository-wide GN refactoring.

The checkpoint stops at the formally verified prime-target residue filter.
