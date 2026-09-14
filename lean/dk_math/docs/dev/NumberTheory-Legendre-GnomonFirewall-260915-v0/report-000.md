# LGF-000 report — exact reindexed support intersection

Date: 2026-09-15

## Outcome

**A — EXACT TURNOVER LAW ESTABLISHED.**

The canonical threshold-skipping reindex now has exact adjacent-shell support
intersection laws.  The lower displacement is `oddGnomon n`; the upper
displacement is `2 * (n + 1)`.  The result remains a finite support statement
and does not prove Legendre's conjecture, full-cover failure, or a global
capacity contradiction.

## Production changes

Added `DkMath/NumberTheory/Legendre/GnomonSupportTurnover.lean` and exported it
from `DkMath/NumberTheory/Legendre.lean`.

The module proves:

- `mem_reindexed_primeSupport_inter_lower_iff`: exact lower membership iff;
- `reindexed_primeSupport_inter_lower_eq_filter`: exact lower Finset filter;
- `mem_reindexed_primeSupport_inter_upper_iff`: exact upper membership iff;
- `reindexed_primeSupport_inter_upper_eq_filter`: exact upper Finset filter;
- `oldPrime_dvd_two_mul_succ_imp_eq_two` and
  `oldPrime_dvd_two_mul_succ_iff_eq_two`: under `Nat.Prime (n + 1)`, an old
  prime divisor of `2 * (n + 1)` is exactly `2`;
- `mem_reindexed_primeSupport_inter_upper_imp_eq_two` and
  `reindexed_primeSupport_inter_upper_eq_filter_eq_two`: the corresponding
  upper intersection collapse;
- `disjoint_reindexed_primeSupport_lower_of_prime_oddGnomon`: conditional lower
  disjointness when the unit gnomon is prime;
- `disjoint_reindexed_primeSupport_upper_of_prime_succ_of_not_dvd_two`:
  conditional upper disjointness after removing the parity channel.

The reverse directions use the old support's bounded-prime witness and the
appropriate displacement divisibility to construct successor support.  No
support-set enumeration is used in the structural results.

## `30 -> 31` regressions

The following kernel-checked regressions were added:

- `disjoint_reindexed_primeSupport_lower_30`: every `SquareOffset 30 r` with
  `r < 31` has disjoint old and successor support, using
  `oddGnomon 30 = 61` and `Nat.Prime 61`;
- `mem_reindexed_primeSupport_inter_upper_30_imp_eq_two`: for every upper seat
  with `31 ≤ r`, any common support member is `2`.

The existing `successor_reindex_30_6_mismatch` and
`successor_reindex_30_7_mismatch` remain untouched.

## Existing-module overlap audit

The pre-existing `GnomonSuccessor` module supplied the two displacement
equalities and one-way divisibility firewalls, but not the exact support
intersection or its reverse direction.  `CenteredPair` and `OldSupportGcd`
address common support for two seats in one fixed shell, controlled by their
seat gap; they do not cover the canonical adjacent-shell reindex.  A source
search over the read-first Legendre modules found no equivalent adjacent-shell
exact theorem.

The current parity-safe incidence/frontier modules provide finite incidence
identities and conditional full-cover inequalities.  The new theorem only
localizes persistent support to divisors of the displacement; by itself it
does not produce a new aggregate lower bound on shell-to-shell turnover under
simultaneous full cover, and it does not imply `¬ SquareOffsetsFullyCovered n`.

Therefore a separate LGF-001 two-shell incidence/turnover ledger is **not
justified yet**.  It should be opened only once a concrete quantitative
charging statement, beyond the existing parity-safe ledger, is specified.

## Validation

- `lake build DkMath.NumberTheory.Legendre.GnomonSupportTurnover` — passed;
- `lake build DkMath.NumberTheory.Legendre` — passed;
- `git diff --check` — passed after the final documentation edit;
- changed Lean files were checked for `sorry`, `admit`, and `axiom`.
