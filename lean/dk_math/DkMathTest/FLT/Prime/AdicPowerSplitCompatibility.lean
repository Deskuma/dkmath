/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Prime.AdicPowerSplit
import DkMath.FLT.Seven.SevenAdicPowerSplit

#print "file: DkMathTest.FLT.Prime.AdicPowerSplitCompatibility"

namespace DkMathTest.FLT.Prime

open DkMath.CosmicFormula
open DkMath.CosmicFormulaBinom
open DkMath.FLT.Prime
open DkMath.FLT.Seven

/-- The existing exponent-seven ramified packet supplies the generic packet. -/
theorem primeAdicFactorPacket_of_seven
    {x y z : ℕ} (P : SevenAdicCounterexamplePacket x y z) :
    PrimeAdicFactorPacket 7 (z - y) y x :=
  { prime := by norm_num
    odd := by norm_num
    gap_pos := gap_pos_of_fermat7Equation P.counterexample.hx P.counterexample.hEq
    distinguished_pos := P.counterexample.hx
    coprime_gap_unit := coprime_gap_y_of_counterexamplePack P.counterexample
    prime_dvd_gap := P.seven_dvd_gap
    factor_eq := by simpa using P.factor_eq }

theorem generic_split_of_seven_packet
    {x y z : ℕ} (P : SevenAdicCounterexamplePacket x y z) :
    Nonempty (PrimeAdicPowerSplit 7 (z - y) y x) :=
  nonempty_primeAdicPowerSplit_of_packet (primeAdicFactorPacket_of_seven P)

/-- The generic output retains the same seventh-prime normal-form shape. -/
theorem generic_split_shape_of_seven_packet
    {x y z : ℕ} (P : SevenAdicCounterexamplePacket x y z) :
    ∃ a b : ℕ,
      0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      z - y = 7 ^ 6 * a ^ 7 ∧
      DkMath.CosmicFormula.GN 7 (z - y) y = 7 * b ^ 7 ∧
      x = 7 * a * b ∧ ¬ 7 ∣ b := by
  rcases generic_split_of_seven_packet P with ⟨S⟩
  refine ⟨S.a, S.b, S.a_pos, S.b_pos, S.coprime_a_b, ?_, ?_,
    S.distinguished_eq, S.prime_not_dvd_b⟩
  · simpa using S.gap_eq
  · simpa using S.residual_eq

#print axioms DkMath.CosmicFormula.gcd_GN_eq_gcd_of_one_le
#print axioms DkMath.CosmicFormula.prime_dvd_GN_iff_dvd_gap
#print axioms DkMath.CosmicFormula.GN_modEq_head_mod_sq_of_odd_prime_dvd_x
#print axioms DkMath.CosmicFormula.padicValNat_GN_prime_eq_one_of_dvd_gap
#print axioms DkMath.FLT.Prime.nonempty_primeAdicPowerSplit_of_packet
#print axioms generic_split_shape_of_seven_packet

end DkMathTest.FLT.Prime
