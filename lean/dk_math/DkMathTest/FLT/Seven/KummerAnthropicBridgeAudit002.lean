/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicKummerUnit

#print "file: DkMathTest.FLT.Seven.KummerAnthropicBridgeAudit002"

namespace DkMathTest.FLT.Seven.KummerAnthropicBridgeAudit002

open DkMath.FLT.Seven
open SevenCyclotomicDegreeSixInt

#check unit_eq_starUnit_of_congruent_mod_seven
#check exists_normUnit_seventhPower_of_congruent_mod_seven
#check degreeSixKummerUnitLemmaAtSeven
#check DegreeSixKummerUnitLemmaAtSeven
#check star_sub_int_mem_sevenIdeal
#check unit_sq_eq_ofReal_normUnit_pow

/-- Apply the original specification to an arbitrary congruent unit, without
constructing or assuming any counterexample packet. -/
theorem congruentUnit_seventhPower
    (u : Ringˣ)
    (h : DegreeSixUnitCongruentToRationalModSeven (u : Ring)) :
    ∃ v : Ringˣ, u = v ^ 7 :=
  degreeSixKummerUnitLemmaAtSeven u h

-- The input can be supplied directly as an integer congruence modulo `(7)`.
example (u : Ringˣ) (m : ℤ) (hm : ¬ (7 : ℤ) ∣ m)
    (h : (u : Ring) - (m : Ring) ∈ Ideal.span ({(7 : Ring)} : Set Ring)) :
    ∃ v : Ringˣ, u = v ^ 7 :=
  congruentUnit_seventhPower u ⟨m, hm, h⟩

#print axioms unit_eq_starUnit_of_congruent_mod_seven
#print axioms exists_normUnit_seventhPower_of_congruent_mod_seven
#print axioms degreeSixKummerUnitLemmaAtSeven
#print axioms star_sub_int_mem_sevenIdeal
#print axioms unit_sq_eq_ofReal_normUnit_pow
#print axioms congruentUnit_seventhPower

end DkMathTest.FLT.Seven.KummerAnthropicBridgeAudit002
