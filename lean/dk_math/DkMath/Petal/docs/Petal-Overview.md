# DkMath.Petal Overview

## Purpose

`DkMath.Petal` is the package that exposes the Petal side of the
BinomialPrime / WeightedBinomial / GN route.

The surrounding project is not only tracking primality as a yes/no predicate.
It is tracking the structure around primeness:

```text
prime character
primitive prime factor
divisibility support
boundary / beam / gap separation
GN and Petal observation surfaces
```

The current main roadmap reached `AKSBridge v1` at Phase 4.5.  Before moving to
Phase 5, the Zsigmondy bridge, the project needed a stable language for
counting, addressing, and preserving factors in Petal-style layers.

This is the role of `DkMath.Petal`.

## Position in the Main Route

The main route is:

```text
Pascal prime row
  -> weighted binomial terms
  -> congruent cosmic formula
  -> finite-field / polynomial Frobenius
  -> AKS cyclic quotient observation
  -> Petal dynamic counting and addressing
  -> GN / primitive-factor / Zsigmondy bridge
```

The Petal layer sits between:

```text
Phase 4.5: AKSBridge v1
Phase 5: Zsigmondy preparation
```

It is not a replacement for the number-theory route.  It is a structured
observation layer used before primitive prime divisors are studied directly.

## Why Petal Counting Was Needed

The long-term target includes continuous-dimensional or dimension-parametric
readings of expressions related to:

```text
(x + u)^d
GN d x u
factorial-like growth
prime-base products
```

Using the Gamma function would be one classical way to continue factorials.
Here the project keeps a more combinatorial and divisibility-oriented route.

The Petal counting layer generalizes the fixed factorial-like growth into a
dynamic product:

```lean
dynamicOrbitTotal b k = product of b i for i < k
```

This gives a common Lean surface for:

```text
ordinary powers
factorial orbit
abstract prime-base orbit
strict prime-base orbit
```

The point is not numerical evaluation.  The point is to preserve divisibility
information:

```text
past bases divide the current prefix product
prefix products divide later prefix products
adopted prime bases remain visible in later products
```

These are the properties needed before the project asks where a primitive
factor first appears.

## Package Surface

The current package contains these main files.

```text
DkMath.Petal.Basic
DkMath.Petal.Forms
DkMath.Petal.RelPolygon
DkMath.Petal.CoreUnit
DkMath.Petal.GNBridge
DkMath.Petal.Counting
DkMath.Petal.Address
```

### `DkMath.Petal.Basic`

Provides Petal-facing aliases for the older `S0` / `S1` vocabulary.

Important names:

```lean
S0Nat
S1Nat
```

### `DkMath.Petal.Forms`

Exposes Petal-facing aliases around the existing `S0` / `S1` forms and
difference kernels.

Important names:

```lean
petal_diff_kernel
petal_diff_kernel_nat
petal_S0_comm
petal_S1_comm
petal_S0_le_S1_nat
```

### `DkMath.Petal.RelPolygon`

Provides the Petal-facing import surface for the dynamic relative polygon
state model.

Important name:

```lean
RelPolygonState
```

### `DkMath.Petal.CoreUnit`

Provides the Petal-facing import surface for unit and phase vocabulary.

Important name:

```lean
CoreUnit
```

### `DkMath.Petal.GNBridge`

Connects the degree-three Petal face to the GN kernel.

Reference note:

```text
docs/explanation/S0_cubic_petal_kernel.md
```

Important names:

```lean
S0_nat_eq_GN_three_sub
three_S0_nat_modEq_one_of_not_dvd_sub
three_not_dvd_S0_nat_of_not_dvd_sub
```

This is the concrete bridge:

```text
GN 3
  -> S0 / Petal face
  -> divisibility observation
```

### `DkMath.Petal.GcdBridge`

Transfers existing degree-three GN gcd control to the `S0_nat` surface.

Important names:

```lean
gcd_sub_S0_nat_eq_gcd_sub_three
gcd_sub_S0_nat_dvd_three
coprime_sub_S0_nat_of_coprime_of_not_dvd_three
```

### `DkMath.Petal.PadicBridge`

Reads boundary-free cubic valuations on the `S0_nat` surface.

Important names:

```lean
padicValNat_cube_sub_eq_padicValNat_S0_nat_of_not_dvd_sub
padicValNat_three_cube_sub_eq_padicValNat_three_S0_nat_of_not_dvd_sub
```

### `DkMath.Petal.PrimitiveBridge`

Connects degree-three primitive-prime witnesses to `S0_nat`.

Important names:

```lean
primitive_prime_dvd_S0_nat
primitive_prime_padicValNat_cube_sub_eq_S0_nat
primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub
exists_primitiveOnS0_of_not_three_dvd_sub
exists_prime_dvd_S0_nat_of_not_three_dvd_sub
```

### `DkMath.Petal.ReducedSupport`

Introduces the reduced-support vocabulary for anchor-prime observations.

Important names:

```lean
HasNoPrimeBelow
HasAnchorPrime
HasPositiveAnchorPrime
hasAnchorPrime_prime
hasAnchorPrime_anchor_dvd
hasAnchorPrime_no_smaller_prime
hasAnchorPrime_anchor_le_of_prime_dvd
hasPositiveAnchorPrime_pos
hasPositiveAnchorPrime_ne_zero
hasPositiveAnchorPrime_of_pos
hasPositiveAnchorPrime_prime
hasPositiveAnchorPrime_anchor_dvd
hasPositiveAnchorPrime_no_smaller_prime
hasPositiveAnchorPrime_anchor_le_of_prime_dvd
hasPositiveAnchorPrime_self_of_prime
```

`HasAnchorPrime` is the wide raw carrier predicate.  Use
`HasPositiveAnchorPrime` when the carrier must be a genuine nonzero support
object.

### `DkMath.Petal.Anchor`

Connects positive anchored carriers to concrete `S0_nat` and `GN` divisibility
surfaces.

Important names:

```lean
AnchoredS0Carrier
AnchoredGNCarrier
anchoredS0Carrier_dvd_S0
anchoredS0Carrier_anchor_prime
anchoredGNCarrier_dvd_GN
anchoredGNCarrier_anchor_prime
anchoredGNCarrier_of_anchoredS0Carrier
anchoredS0Carrier_of_anchoredGNCarrier
exists_anchoredS0Carrier_of_not_three_dvd_sub
```

### `DkMath.Petal.BoundaryD3`

Records the degree-three boundary split for the cubic Petal detector.

Important names:

```lean
BoundaryD3Branch
BoundaryD3Reduced
three_dvd_S0_nat_of_three_dvd_sub
three_dvd_sub_of_three_dvd_S0_nat
three_dvd_S0_nat_iff_three_dvd_sub
boundaryD3Reduced_three_not_dvd_S0_nat
boundaryD3Branch_three_dvd_S0_nat
boundaryD3Reduced_coprime_sub_S0_nat
```

Conceptually, this says:

```text
3 divides S0_nat c b exactly on the boundary branch 3 | (c - b).
```

The reduced branch therefore gives the usable cubic Petal surface:

```text
BoundaryD3Reduced c b
  -> not 3 | S0_nat c b
  -> Coprime (c - b) (S0_nat c b), assuming Coprime c b
```

### `DkMath.Petal.Counting`

Defines the fixed and dynamic counting layer.

Fixed Petal names:

```lean
baseUnitCore
inheritanceSlot
lapBase
relPetalTotal
relPolygonKernel
```

Dynamic orbit names:

```lean
dynamicOrbitTotal
dynamicPetalTotal
```

Factorial bridge:

```lean
dynamicOrbitTotal_succIndex_eq_factorial
```

Prime-base orbit names:

```lean
primeBaseOrbitTotal
IsPrimeBaseSequence
IsDistinctPrimeBaseSequence
IsStrictPrimeBaseSequence
```

Core divisibility facts:

```lean
dynamicOrbitTotal_base_dvd_of_lt
dynamicOrbitTotal_dvd_succ
dynamicOrbitTotal_dvd_of_le
primeBaseOrbitTotal_base_dvd_of_lt
primeBaseOrbitTotal_prime_dvd_of_lt
primeBaseOrbitTotal_prime_dvd_of_lt_of_le
primeBaseOrbitTotal_dvd_of_le
```

Prime-base sequence API:

```lean
IsPrimeBaseSequence.prime_at
IsDistinctPrimeBaseSequence.prime_at
IsDistinctPrimeBaseSequence.injective
IsDistinctPrimeBaseSequence.ne_of_ne
IsDistinctPrimeBaseSequence.ne_of_lt
IsStrictPrimeBaseSequence.prime_at
IsStrictPrimeBaseSequence.strictMono
IsStrictPrimeBaseSequence.injective
IsStrictPrimeBaseSequence.distinct
IsStrictPrimeBaseSequence.base_lt_of_lt
IsStrictPrimeBaseSequence.ne_of_lt
```

### `DkMath.Petal.Address`

Defines the address layer for Petal channels.

Important names:

```lean
relPetalBlockSize
PetalAddress
IsInheritanceChannel
IsPetalChannel
outerPetalAddress
outerPetalRemainder
nestedPetalAddress
```

The key theorem is the one-step decomposition:

```lean
outerPetalAddress_decompose
```

Conceptually:

```text
m = channel * blockSize + remainder
```

with the corresponding one-based subtraction form:

```lean
outerPetalAddress_decompose_sub_one
```

This turns Petal addressing into ordinary quotient-remainder arithmetic with
Petal-facing names.

## Current Achieved Checkpoint

The current Petal checkpoint is:

```text
Fixed Petal counting
  -> dynamic Petal counting
  -> dynamic orbit product
  -> factorial orbit
  -> prime-base orbit
  -> distinct / strict prime-base sequence
  -> prefix divisibility persistence
  -> Petal address decomposition
  -> GN degree-three bridge
  -> S0/GN primitive bridge
  -> reduced-support anchor carriers
  -> degree-three boundary split
```

This means the package can already express:

```text
an adopted base remains visible in later products
an adopted prime base remains visible in later prime-base products
strict prime-base sequences preserve order and non-repetition
one Petal address step is a quotient-remainder decomposition
S0 is a visible degree-three Petal face of GN
primitive S0 witnesses can be read as anchored carriers
the cubic 3-contact is exactly the boundary branch
```

## What This Does Not Claim Yet

The package does not yet prove a standard primorial theorem using a concrete
prime enumeration such as `nthPrime`.

It also does not yet prove a Zsigmondy theorem.  Instead, it prepares the
language needed for that bridge:

```text
where factors are stored
which factors persist across later layers
how Petal addresses split a layer into channels
how GN degree 3 becomes the Petal S0 face
how reduced cubic support excludes the boundary prime 3
```

## Next Directions

The next reasonable implementation directions are:

```text
1. connect AnchoredS0Carrier to the primitive S0 witnesses
2. use Petal address decomposition in nested observations
3. expose the Eisenstein norm route through `DkMath.Petal.EisensteinBridge`
4. connect strict prime-base orbits to a concrete prime enumeration
5. decide whether GNPrimitiveCandidate needs a separate vocabulary layer
```

The most conservative next theorem work is probably:

```text
DkMath.Petal.EisensteinBridge
```

The most concrete arithmetic next step is:

```text
standard primorial connection
```

but that should be started only after surveying the current Mathlib prime
enumeration API.
