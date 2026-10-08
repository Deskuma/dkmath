/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre
import DkMath.NumberTheory.Primitive
import Mathlib.Data.Nat.ChineseRemainder

#print "file: DkMathTest.NumberTheory.LegendreAdaptiveCertificateInventory"

open DkMath.NumberTheory.Legendre

#check sum_witness_support_excess_le_supportExcess
#check paritySafeUncovered_nonempty_of_local_witnesses
#check exists_prime_squareCell_of_local_witnesses
#check paritySafeUncovered_card_ge_candidate_add_excess_sub_twoPrimeUpper
#check paritySafeIncidenceCount_le_twoPrimeUpper
#check paritySafeTwoPrimeIncidenceUpper_eq_upper_two_pow_mul_prime_pow
#check mem_paritySafeActiveSupport_iff_dvd
#check mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue
#check coprime_two_mul_iff_coprime_and_odd
#check paritySafeSupportExcess
#check block_incidence_add_uncovered_eq_candidate_add_supportExcess
#check squareOffsetCovered_iff_primeSupport_nonempty
#check Nat.chineseRemainder
#check Nat.chineseRemainder_lt_mul
#check Nat.ModEq.of_dvd
#check Nat.modEq_zero_iff_dvd
#check Nat.Prime.coprime_iff_not_dvd
#check Nat.Prime.dvd_mul
#check Nat.Coprime.prod_left
#check Finset.prod_pos
#check Finset.dvd_prod_of_mem
