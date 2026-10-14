# Instruction 008 source inventory

Baseline `a8d0be1e6`,007 implementation `6362ea935`; initial tree clean. The [inventory probe](../../../DkMathTest/NumberTheory/LegendreHybridProviderInventory.lean) was run before adding abstractions. [Checked types](evidence/MANIFEST.md#log-3070195d1190e582).

| Requested source | Exact interfaces audited and reused |
| --- | --- |
| `ParitySafeIncidenceUpper` | `paritySafeReducedQuotient_card_le_divisorUpper`, `paritySafeActiveWave_card_le_waveUpper`, `paritySafeIncidenceCount_le_upper`, `paritySafeUncovered_card_ge_candidate_add_excess_sub_upper` |
| `ParitySafeReducedResidue` | `mem_paritySafeReducedQuotientInterval_iff`, `paritySafeReducedQuotientInterval_subset_oddRaw`, `card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval` (the subset lemma is exported by the Möbius module) |
| `ParitySafeMobiusOddCorrection` | `card_filter_odd_dvd_Ioc_eq_paritySafeDelta`, `paritySafeOddRawQuotientInterval_card_eq`, `paritySafeOddMultipleFloorDelta` |
| `ParitySafeIncidenceBalance` | `mem_paritySafeActiveSupport_iff_dvd`, `paritySafeSupportExcess`, `paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence`, `paritySafeCoveredCandidates_card_add_uncoveredCandidates_card_eq_candidate_card`, `exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty` |
| `ParitySafeFreshCost` | `sum_lowerCandidates_sub_parityCap_sub_firstSlots_le_excess`; its full-cover premise distinguishes it from the new unconditional certificate |
| `ParitySafeBlockLocalization` | `block_incidence_add_uncovered_eq_candidate_add_supportExcess`; the existing deficit ledger is retained |
| requested `ParitySafePrimeSupport` | This file does not exist in the live checkout. `Legendre.Basic` supplies `squareOffsetPrimeSupport`, `mem_squareOffsetPrimeSupport`, `squareOffsetCovered_iff_primeSupport_nonempty`, `squareOffsetForbiddenBy_pair_iff_product_dvd`. `ParitySafeActiveCapacity` supplies `mem_squareAnchorOddActivePrimes` and `mem_squareAnchorOddPointCoprimeOffsets`. Actual active support is in `ParitySafeIncidenceBalance`. These sources were read instead. |
| `DkMath.NumberTheory.Primitive` | Existing finite-prime-world and square-Body facade; application-specific coverage remains in the Legendre modules. No replacement primitive framework is introduced. |

Relevant Mathlib APIs were checked before use: `Finset.card_union_add_card_inter`, `Finset.card_sdiff_of_subset`, `Finset.sum_le_sum_of_subset_of_nonneg`, `Finset.le_fold_min`, `Finset.fold_min_le`, `Nat.mem_primeFactors`, `Nat.coprime_primes`, `Nat.Coprime.mul_dvd_of_dvd_of_dvd`. The existing prime-factor multiplication/power equalities and Finset off-diagonal membership/cardinality support the structural limitation theorem.

The generic finite-set theorem lives in `DkMath.NumberTheory` and has no Legendre-specific premise. The remaining additions to `ParitySafeIncidenceUpper` use the original active-prime index, quotient sets and incidence object. `ParitySafeExcessCertificate` only aggregates subsets of the existing support-excess sum. No production definition of a hybrid-gap ledger is needed.
