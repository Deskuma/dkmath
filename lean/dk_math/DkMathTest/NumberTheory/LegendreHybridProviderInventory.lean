/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre
import DkMath.NumberTheory.Primitive

#print "file: DkMathTest.NumberTheory.LegendreHybridProviderInventory"

open DkMath.NumberTheory.Legendre

#check paritySafeReducedQuotient_card_le_divisorUpper
#check paritySafeActiveWave_card_le_waveUpper
#check paritySafeIncidenceCount_le_upper
#check paritySafeUncovered_card_ge_candidate_add_excess_sub_upper
#check mem_paritySafeReducedQuotientInterval_iff
#check paritySafeReducedQuotientInterval_subset_oddRaw
#check card_filter_odd_dvd_Ioc_eq_paritySafeDelta
#check mem_paritySafeActiveSupport_iff_dvd
#check paritySafeSupportExcess
#check paritySafeCoveredCandidates_card_add_supportExcess_eq_incidence
#check exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty
#check sum_lowerCandidates_sub_parityCap_sub_firstSlots_le_excess
#check block_incidence_add_uncovered_eq_candidate_add_supportExcess
#check mem_squareAnchorOddActivePrimes
#check mem_squareAnchorOddPointCoprimeOffsets
#check squareOffsetCovered_iff_primeSupport_nonempty
#check Finset.card_union_add_card_inter
#check Finset.card_sdiff_of_subset
#check Finset.sum_le_sum_of_subset_of_nonneg
#check Finset.le_fold_min
#check Finset.fold_min_le
#check Nat.mem_primeFactors
#check Nat.coprime_primes
#check Nat.Coprime.mul_dvd_of_dvd_of_dvd
