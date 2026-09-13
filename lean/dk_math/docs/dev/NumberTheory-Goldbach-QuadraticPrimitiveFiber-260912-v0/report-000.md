# QP-000 — environment and theorem inventory

Date: 2026-09-12. Initial HEAD: `b723621ed9a6d9a33fd36ed20e4c2cdfbe933123`.
Branch verified: `research/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0`.
Initial worktree clean. No applicable AGENTS.md found in ancestors or repository.

The user's direct request authorizes research implementation and commits on this
branch only. The attached instruction supplies the six-phase research contract,
allowed paths, incremental commits, and verification requirements. It does not
authorize a production migration or establish a mathematical conjecture.

## Current source inventory

All names below are checked against current source, rather than taken solely from
historical reports. Namespace is `DkMath.NumberTheory` unless indicated.

| Owner | Existing facts and consequence for this audit |
|---|---|
| Goldbach/Basic | `goldbach_GN_two`, `goldbachPairAt_iff_exists_offset`, `goldbachOffset_bounds`, `goldbachPairAt_iff_gnFiberAt`: coordinates and admissible range already exact |
| Lib/Cosmic/GTailBoundary | `DkMath.CosmicFormula.gcd_GTail_eq_gcd_boundary`, `gcd_GTail_eq_gcd_choose`, `gcd_GN_eq_gcd_of_one_le`, prime branches: quadratic boundary is a specialization, not new general gcd mathematics |
| Lib/Cosmic/GTail, GTailPascal | `GTail_rec`, `GTail_split_at`: exact algebraic filtration; no identification with obstruction supports |
| Lib/Cosmic/GTailCongruence | `prime_dvd_GN_iff_dvd_gap`, `GN_modEq_head_of_dvd_x`: congruence facts, not short-interval existence |
| Lib/Cosmic/GTailPadic, GTailCyclotomic | head-unit valuation and cyclotomic identities inspected; no unconditional simultaneous primality provider |
| Goldbach/Obstruction | `goldbach_survives_iff_prime_pair`, `goldbach_not_prime_pair_iff_obstructed`, `goldbachSmallPrimes`: proper exceptions and complete cutoff already accounted for |
| Goldbach/PrimeWorld | `goldbach_left_obstructed_iff`, `goldbach_right_obstructed_iff`, `goldbach_residue_eq_neg_iff`, `goldbach_primeWorld_crt`, `goldbach_residue_periodic`: orientation and product geometry already available |
| Goldbach/Cardinality | `goldbach_card_primeWorld`: product count of full-period raw survivors |
| Goldbach/Capacity | `goldbachPairAt_iff_covered_card_lt`, `strongGoldbach_iff_capacityEscape`, `goldbach_blocked_card_le_residue_capacity`: exact escape remains the original problem |
| Goldbach/Conservation | `goldbach_paired_primitive_dichotomy`, `goldbach_prime_pair_of_square_support`: conditional endpoint classification, different from gcd(n,u)=1 |
| Goldbach/Overlap, PairOverlap | `goldbachIncidenceConservation`, `goldbachPrimePairOverlapCount_eq_sum_local_pairMultiplicity`, `goldbachPrimePairOverlapCount_eq_overlapExcess_add_residual`: the split ledger must reconcile with these |
| Goldbach/Limitations | `goldbach_proper_obstruction_not_periodic`, `goldbach_two_raw_interval_empty`: raw/proper distinction is mandatory |
| Primitive/PeriodicPrimeWorld | `supportDisjointFrom_centered_mirror_iff`: existing mirror divisibility transport |
| Legendre/ParitySafeActiveCapacity | `squareAnchorOddPointCoprimeOffsets`, membership/coprimality APIs: similar filter pattern, but a different square-anchor domain, not a Goldbach equivalence |

Mathlib owners: `Data/Nat/GCD/Basic.lean` already proves
`Nat.coprime_sub_self_left`, `Nat.coprime_add_self_left` and gcd transport.
`Data/Nat/Prime/Basic.lean` supplies `Nat.coprime_primes`,
`Nat.coprime_two_right`. `Data/Nat/ModEq.lean` supplies
`Nat.chineseRemainder`, `Nat.chineseRemainder_modEq_unique`,
`Nat.modEq_and_modEq_iff_modEq_mul`. Thus the candidate coordinate coprimality
lemma is redundant and CRT uniqueness does not require prime moduli, only
coprime ones.

## Search and reading evidence

Read the specified Goldbach source modules and GTail family, the prior GN-fiber
README/reports 004, 006, 007, and GTcore analysis 001/002 and reports 002–005.
Used `rg` with gcd/Coprime, parity/odd/even, primitive/offset, mirror/support,
left/right, pair/choose, CRT/primeWorld and GN/GTail shapes. Also used `zgrep`
on `lean/dk_math/logs/__dkmath-all.lean.txt.gz`: boundary gcd at line 233221,
capacity at 240920/240945, CRT at 242004. The compressed database is a search
supplement; current `.lean` source is authoritative.

Planned scratch imports: production `DkMath.NumberTheory.Goldbach` and canonical
`DkMath.Lib.Cosmic.GTailBoundary`. The production facade must not import scratch.
No Lean theorem has yet been added or build result claimed in this phase.
Next: prove bounded subtraction/gcd facts, positive-pair normalization, diagonal
exception, and scratch filter memberships before drawing an information-gain verdict.
