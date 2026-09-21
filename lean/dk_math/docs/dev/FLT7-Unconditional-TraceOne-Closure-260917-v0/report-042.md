# FLT7TC-005R36 — ideal-norm exponent transport

## Scope

This report records the R36 attempt to transport the R35 exact ideal
multiplicities to the natural factorization coefficients of the two absolute
norms.  The global canonical `C,U,V` packet is outside this checkpoint.

## Initial investigation

- R30 already provides inertia degree one for every prime ideal above a common
  norm prime.
- `Ideal.natAbs_pow_inertiaDeg` is the direct bridge from the rational prime
  and inertia degree to the absolute norm of a prime ideal.
- Mathlib provides `Ideal.exists_isMaximal_dvd_of_dvd_absNorm'` for extracting
  a prime ideal above `q` from a residual ideal whose absolute norm is divisible
  by `q`.
- The remaining transport requires a checked residual q-freeness argument and
  an explicit finite q-primary ideal product; cardinality alone is not used as
  a norm-exponent identity.

## Implementation log

Entries are appended after each scratch experiment and production validation.

## Part A — prime-ideal absolute norm

Added `directOrbitCanonicalCommonFactor_prime_absNorm`.  The theorem uses the
R30 inertia-degree-one result together with
`Ideal.natAbs_pow_inertiaDeg` and proves `Ideal.absNorm P = q` for every
common prime ideal `P` above `(q)`.

## Part B/C — gap residual and natural factorization

Added `directOrbitCanonicalCommonFactor_gap_qPrimary_residual`.  A maximal
prime above `q` is extracted from the gap ideal, its multiplicity is fixed by
the R35 allocation theorem, and the residual ideal is proved q-free by a
second maximal-prime extraction and the gap singleton allocation.

Added `directOrbitCanonicalCommonFactor_gap_factorization`.  Taking absolute
norms of the residual equation and applying `Nat.factorization_mul` and
`Nat.factorization_pow_self` proves

```text
natAbs (norm gapSquareRoot).factorization q = a.factorization q.
```

## Part D — quotient residual and natural factorization

Added `directOrbitCanonicalCommonFactor_quotient_qPrimary_residual`.  The two
distinct quotient primes from the R30 cardinality result are extracted,
their equal R35 multiplicities are combined using ideal coprimality, and the
remaining ideal is proved q-free.

Added `directOrbitCanonicalCommonFactor_quotient_factorization`.  The two
prime norms are both `q`, so the residual norm equation yields

```text
natAbs (norm quotientSquareRoot).factorization q =
  2 * a.factorization q.
```

## Validation

- The production module and `DkMath.FLT.Seven` facade build successfully.
- The R36 scratch file kernel-checks the inertia-degree bridge, both residual
  decompositions, and both natural factorization identities.
- The API audit exposes the five new public theorems.
- The axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound` for the new theorem chain.
