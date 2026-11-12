/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic

#print "file: DkMath.Lib.Algebra.PrimeOrderResonance"

/-!
# 厳密位数と共鳴する冪の固定・反転

元の同じ群の元の厳密位数を使う。共役不変性を仮定せずに結論しない。
-/
namespace DkMath.Lib.Algebra.PrimeOrderResonance
variable {G : Type*} [Group G] {p q : ℕ} {z : G}

/-- 位数が正確に p の元は、q 乗で固定されることと q=1 mod p が同値。 -/
theorem pow_eq_self_iff (hz : orderOf z = p) : z ^ q = z ↔ (q : ZMod p) = 1 := by
  conv_lhs => rhs; rw [← pow_one z]
  rw [pow_inj_mod, hz]
  simpa only [Nat.ModEq, Nat.cast_one] using (ZMod.natCast_eq_natCast_iff q 1 p).symm

/-- q=-1 mod p なら、同じ位数 p の元の q 乗は逆元。 -/
theorem pow_eq_inv (hz : orderOf z = p) (hq : (q : ZMod p) = -1) : z ^ q = z⁻¹ := by
  have hm : ((q + 1 : ℕ) : ZMod p) = 0 := by simp only [Nat.cast_add, Nat.cast_one, hq, neg_add_cancel]
  have hd : p ∣ q + 1 := (ZMod.natCast_eq_zero_iff (q + 1) p).mp hm
  have he : z ^ (q + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (hz ▸ hd)
  exact eq_inv_iff_mul_eq_one.mpr (by simpa only [pow_succ] using he)

/-- p>2 の厳密位数 p の元は、その逆元と異なる。 -/
theorem inv_ne_self (hp : 2 < p) (hz : orderOf z = p) : z⁻¹ ≠ z := by
  intro he
  have h2 : z ^ 2 = 1 := by
    rw [pow_two]
    calc z * z = z⁻¹ * z := congrArg (fun w => w * z) he.symm
         _ = 1 := inv_mul_cancel z
  have hd : p ∣ 2 := hz ▸ orderOf_dvd_of_pow_eq_one h2
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

/-- 負の共鳴分岐では、q 乗によって同じ値が実際に変化する。 -/
theorem pow_ne_self_of_negative (hp : 2 < p) (hz : orderOf z = p)
    (hq : (q : ZMod p) = -1) : z ^ q ≠ z := by
  rw [pow_eq_inv hz hq]
  exact inv_ne_self hp hz

end DkMath.Lib.Algebra.PrimeOrderResonance
