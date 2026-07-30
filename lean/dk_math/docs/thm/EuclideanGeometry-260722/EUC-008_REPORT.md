# EUC-008 Report - Fermat Form Arithmetic Layer

## Goal

Define the classical arithmetic target

```text
2^a times a finite product of distinct Fermat primes
```

without importing geometric constructibility into the definition.

## Mathlib inventory

The pinned Mathlib already provides:

```text
Nat.fermatNumber
Nat.fermatNumber_strictMono
Nat.fermatNumber_injective
Nat.coprime_fermatNumber_fermatNumber
Nat.pairwise_coprime_fermatNumber
Nat.totient
Nat.totient_mul
Nat.totient_prime
Nat.totient_prime_pow_succ
```

Accordingly, DkMath does not redefine Fermat numbers, primality, coprimality,
or Euler's totient.

## Implementation

Added:

```text
DkMath/NumberTheory/EuclideanGeometry/FermatForm.lean
```

The public predicates are:

```text
IsFermatPrimeIndex i
IsGaussWantzelIndex n
```

The finite set of indices enforces distinct selected indices.  Primality is
required explicitly for every selected Fermat number.  The definition does
not restrict the support to the five currently known Fermat primes.

## Arithmetic API

The module proves:

```text
fermatNumbers_pairwise_coprime
isGaussWantzelIndex_one
isGaussWantzelIndex_two_pow
isGaussWantzelIndex_fermatNumber
totient_fermatNumber
totient_two_pow
totient_fermatProduct
two_pow_coprime_fermatProduct
IsGaussWantzelIndex.exists_totient_eq_two_pow
```

For a witness with two-power exponent `a` and Fermat support `s`, the final
totient exponent is explicitly

```text
a.pred + sum (2^i), for i in s.
```

This follows from pairwise coprimality of distinct Fermat numbers, oddness of
every Fermat number, and multiplicativity of Euler's totient on coprime
factors.

## Scope boundary

The implemented bridge is the forward implication:

```text
IsGaussWantzelIndex n -> exists e, Nat.totient n = 2^e.
```

The converse is not asserted.  It requires a prime-factor classification
argument showing that every odd prime divisor has Fermat form and occurs only
once.  That obligation is mathematically separate from the direct finite
product calculation proved here.

No theorem in this module mentions Euclidean rotation, regular orbits, or
straightedge-and-compass construction.  Those concepts belong to later bridge
layers.

No axiom, `sorry`, or `native_decide` was introduced.

## Verification

From `lean/dk_math`:

```text
lake build DkMath.NumberTheory.EuclideanGeometry.FermatForm
  success

lake build DkMath.CosmicFormula.Rotation.CF2D
  success
```

The shell's existing `/opt/wonderful/bin/wf-env` permission warning and the
pre-existing `ring_nf` suggestions replayed by the CF2D aggregate are unrelated
to EUC-008.  Lean emitted no warning for the new arithmetic declarations.

## Next checkpoint

EUC-009 can define the constructibility predicates and their closure API while
keeping `IsGaussWantzelIndex` as an independent arithmetic classification.
The full Gauss-Wantzel equivalence remains a later bridge theorem, not a
definition.
