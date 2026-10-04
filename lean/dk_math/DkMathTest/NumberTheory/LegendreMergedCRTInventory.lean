/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre
import Mathlib.Data.Nat.ChineseRemainder

#print "file: DkMathTest.NumberTheory.LegendreMergedCRTInventory"

open DkMath.NumberTheory.Legendre

#check activeSupport_contains_of_point_modEq
#check candidate_of_window_coprime_odd
#check sum_indexed_modEq_charge_le_supportExcess
#check prime_anchor_period_family_charge_le_supportExcess
#check exists_candidate_support_of_prime_product_lt
#check sum_witness_support_excess_le_supportExcess
#check paritySafeUncovered_nonempty_of_local_witnesses
#check exists_prime_squareCell_of_local_witnesses
#check paritySafeIncidenceCount_le_twoPrimeUpper
#check paritySafeTwoPrimeIncidenceUpper_eq_upper_two_pow_mul_prime_pow
#check mem_paritySafeActiveSupport_iff_dvd
#check mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue
#check block_incidence_add_uncovered_eq_candidate_add_supportExcess
#check Finset.mem_biUnion
#check Finset.card_union_add_card_inter
#check Finset.sum_image
#check Finset.sum_union_inter
#check Finset.sum_ite_mem
#check Nat.chineseRemainder
#check Nat.ModEq.add_left
#check Nat.ModEq.of_dvd
#check Nat.ModEq.dvd_iff
#check Nat.coprime_of_mul_modEq_one
#check Nat.Coprime.pow_left
#check Nat.coprime_mul_iff_left
#check Nat.Coprime.prod_left
#check Nat.mod_add_div
