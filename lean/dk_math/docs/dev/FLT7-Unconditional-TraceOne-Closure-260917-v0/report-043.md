# FLT7TC-005R37 — canonical gcd cubic split

## Scope

This report records the R37 arithmetic checkpoint.  It uses the R36 exact
common-prime exponent identities and the existing cube ledger to construct
canonical finite supports and products.  The R32 `DirectOrbitCubeDefectPacket`
and all Galois, residue-field, successor, and descent layers remain
unchanged.

## Initial investigation

- `Nat.factorization_prod_apply` and
  `Nat.prod_factorization_pow_eq_self` provide the finite-product and
  reconstruction bridges needed for canonical support products.
- `Nat.factorization_gcd` gives the common-product identification once the
  complete three-way exponent table is established.
- `Nat.Coprime.prod_left`/`prod_right` support pairwise coprimality directly
  from disjoint filtered supports.

## Implementation log

Entries are appended after each scratch experiment and production validation.

- The R37 scratch kernel-check now passes for the finite support partition,
  exact common/gap-only/quotient-only exponent table, and the three product
  reconstructions.  The dependent `Finset` membership step was discharged
  through `Finset.mem_filter.mp`, without unsafe elimination or axioms.
- The production module now contains the corresponding support/product
  infrastructure, `Nat.factorization_gcd` identification of the common
  product, pairwise coprimality from disjoint prime supports, and the direct
  R37 exponent-table theorem.
- The production constructor
  `directOrbitSquareRefinement_canonicalCommonFactor_nonempty` packages the
  canonical `C,U,V` split, positivity, `C ∣ a`, the three factorization
  equalities, pairwise coprimality, common-prime mod-7 support, and
  `C * U ^ 5 < V`.
- Sequential production validation passed with
  `lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCanonicalCommonFactor`.
- The R37 kernel-check scratch and the existing canonical-common-factor scratch
  both passed sequentially with `lake env lean`; only linter warnings were
  emitted by the R37 scratch.
- The public API check passed for the packet, support/product definitions,
  exponent-table theorem, and packet constructor.  The axiom audit reported
  only `propext`, `Classical.choice`, and `Quot.sound`, matching the existing
  arithmetic infrastructure.
- The facade build passed with
  `lake build DkMath.FLT.Seven`.  `git diff --check` and the untracked-file
  whitespace checks were clean, and the forbidden-construct scan found no
  `sorry`, `admit`, `unsafe`, or declaration of an `axiom` in the decisive
  production, API, axiom, and scratch files.
