# Source inventory 030 - Singleton cofactor windows

The live checkout starts from committed checkpoint 029. The new work is bounded
by instruction-030. Earlier checkpoints are reused, rather than replayed.

## Exact receivers

- GnomonCarryFiber: large-base fibers have only exponent one; canonical targets
  are injective; the capacity envelope has nonnegative excess over the ledger.
- GnomonDivisorCarry: next-shell-multiple packet, uniqueness, cofactor cutoff,
  prime-power weights, small/large split, and exact old/higher/carry ledger.
- GnomonPascalCell: exact old/birth logarithmic split and prime-existence iff.
- ParitySafeSqrtQuotientConservation: finite quotient/census conservation;
  its carriers and hypotheses do not supply an independent weighted estimate.
  sqrt_cross_fiber_card_le_odd_span already proves an odd-spacing cardinal
  estimate for its rough-active carrier. The elementary parity idea transfers,
  but this specific theorem cannot be applied without its carrier hypotheses.
- ParitySafeSqrtRoughFactorization: rough-quotient factorization under explicit
  roughness assumptions, not a bound for every singleton carry window.
- ParitySafeTripleFarCofactor: active-support cofactor transport under triple
  hypotheses; no uniform weighted interval bound is present.

## Elementary bound search

- Mathlib.Data.Nat.Choose.Dvd, Nat.Prime.dvd_choose: a prime between both
  denominator factorial cutoffs and the top divides the binomial coefficient.
  For A=max(base/k,width), B=top/k, each window prime exceeds A and B-A.
- Nat.prod_primeFactors_dvd and finite product subset divisibility bound the
  product of distinct window primes by choose(B,B-A). Real.log_prod converts
  this integer estimate to a weighted finite sum.
- Real.log_nat_eq_sum_factorization provides an alternative weighted proof.
- Nat.add_div_le_div_add_div_add_one controls the quotient-window length.
- Mathlib.NumberTheory.Chebyshev has finite theta/psi sums and global bounds,
  including theta_le_log4_mul_x. Subtracting two global upper estimates does
  not produce an upper estimate for their difference. The finite difference
  alone would just reindex Q.
- BinomialPrime and Bertrand supply binomial divisibility/growth tools. Their
  existing prime-row/doubling-interval results do not settle these short windows.

The selected final bound takes the smaller binomial or odd-cardinality power
coefficient in each window, then sums their logarithms. Its definition depends
only on n and quotient endpoints, not carry-event membership. The generic
odd-spacing cardinal proof uses prime oddness and the half-interval injection;
it imposes none of the older rough-active carrier hypotheses. Diagnostics
compare both candidates with the exact singleton mass and the exact ledger.
