# Instruction 009 source inventory

Baseline `cfd1d5f12`,008 implementation `b88687d79`, initial tree clean. [Inventory Lean](../../../DkMathTest/NumberTheory/LegendreAdaptiveCertificateInventory.lean) was run before adding abstractions; [exact checked types](evidence/MANIFEST.md#log-8825fb8c9e727d2a).

| Required source | Exact interfaces audited |
| --- | --- |
| `ParitySafeIncidenceUpper` | `paritySafeIncidenceCount_le_twoPrimeUpper`, `paritySafeTwoPrimeIncidenceUpper_eq_upper_two_pow_mul_prime_pow`; cap remains B2 from008 |
| `ParitySafeExcessCertificate` | `sum_witness_support_excess_le_supportExcess`, `paritySafeUncovered_nonempty_of_local_witnesses`, `exists_prime_squareCell_of_local_witnesses`, `paritySafeUncovered_card_ge_candidate_add_excess_sub_twoPrimeUpper`; arbitrary Finset seat aggregation already exists |
| `ParitySafeIncidenceBalance` | `mem_paritySafeActiveSupport_iff_dvd`, `paritySafeSupportExcess`, the exact covered/uncovered/excess partition and prime consumer |
| `ParitySafeReducedResidue` | `mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue`, `coprime_two_mul_iff_coprime_and_odd`; candidate means a positive offset≤2n with anchor coprimality and odd point |
| requested `ParitySafePrimeSupport` | File absent in the live checkout. Audited `Basic` (`squareOffsetCovered_iff_primeSupport_nonempty` and actual prime-support membership), `ParitySafeActiveCapacity` (active primes and candidate membership), and `ParitySafeIncidenceBalance` (actual parity-safe active support) instead |
| `ParitySafeBlockLocalization` | `block_incidence_add_uncovered_eq_candidate_add_supportExcess`; original ledger remains unchanged |
| `Primitive` | Existing finite-prime-world/square-Body facade; no replacement Primitive framework |

Mathlib inventory includes `Nat.chineseRemainder`, `Nat.chineseRemainder_lt_mul`, `Nat.ModEq.of_dvd`, `Nat.modEq_zero_iff_dvd`, `Nat.Prime.coprime_iff_not_dvd`, `Nat.Coprime.prod_left`, `Finset.prod_pos`, `Finset.dvd_prod_of_mem`. `Mathlib.Data.Nat.ChineseRemainder` also provides finite-list/Finset CRT. Here every support equation is homogeneous on the shell point, so divisibility by the product simultaneously supplies every q congruence; the actual CRT construction only needs the product modulus and the independent parity modulus2.

The neutral period/CRT lemmas live in `DkMath.NumberTheory`, inside the new application module. They have no Legendre hypotheses. Application transport and prime-anchor family results live in `DkMath.NumberTheory.Legendre`. No required-charge definition or duplicate incidence/excess/certificate ledger is added.

The indexed family API uses injectivity of actual offsets. It does not infer distinctness from labels or prime subsets. The existing Finset seat-witness aggregation is reused for mandatory and finite-classification proofs.
