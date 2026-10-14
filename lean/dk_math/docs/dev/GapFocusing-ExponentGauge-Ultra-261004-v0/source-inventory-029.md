# Source inventory 029

Read instruction-029 and report-028 before production edits. The live checkout
started clean on the expected research branch.

## Existing application APIs

GnomonDivisorCarry supplies exact binary carriers, bands, unique next-shell
multiples, common-base exclusion for large power divisors, the old budget
identity and the conditional band-bound consumer. SquareShellPrimePower supplies
canonical prime-power base/depth via minFac and factorization, and distinguishes
shell powers from old power-divisor labels. SquareShellVonMangoldt and Gauge
supply exact weights and correction bounds. GnomonPascalCell supplies choose
valuation carries. BinomialPrimePower supplies existing valuation receivers;
no duplicate padic observable is needed.

## Mathlib APIs

Nat.Prime.pow_dvd_iff_le_factorization identifies the upper valuation depth for
positive targets. Nat.log_lt_of_lt_pow and Nat.lt_pow_of_log_lt convert the
large-width cutoff; le_log_of_pow_le and pow_le_of_le_log convert the old cutoff.
Nat.pow_right_injective provides exponent uniqueness. IsPrimePow provides its
minFac power/factorization identity. Finset sum_fiberwise_of_maps_to, sum_bij
and interval cardinality supply exact finite regrouping. vonMangoldt_apply_pow
makes each positive same-base label contribute exactly log(p).

## Minimal selected surface

Add GnomonCarryFiber, importing the existing 028 module. Define a bounded
exponent fiber, the finite image of canonical (prime base, shell target) pairs,
and one global cutoff budget. Prove the exact exponent interval, cardinal and
weighted formulas, the cutoff bound and a 028 consumer. No analytic prime
estimate or independent global provider is assumed. The facade dependency
remains one way.
