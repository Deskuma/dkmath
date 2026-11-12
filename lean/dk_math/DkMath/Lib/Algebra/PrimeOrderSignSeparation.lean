/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.GroupTheory.OrderOfElement

#print "file: DkMath.Lib.Algebra.PrimeOrderSignSeparation"

/-! # 奇素数位数の元に対する二つの符号の分離 -/
namespace DkMath.Lib.Algebra.PrimeOrderSignSeparation

/-- 位数が 2 より大きい元は、自分自身の負に等しくない。 -/
theorem ne_neg_of_order_gt_two {A : Type*} [AddCommGroup A] (v : A)
    (horder : 2 < addOrderOf v) : v ≠ -v := by
  intro h
  have hz : 2 • v = 0 := by
    calc
      2 • v = v + v := two_nsmul v
      _ = v + -v := congrArg (fun z => v + z) h
      _ = 0 := add_neg_cancel v
  have hd : addOrderOf v ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

/-- 同じ元について固定作用と符号反転作用は両立しない。 -/
theorem fixed_ne_neg_of_order_gt_two {A : Type*} [AddCommGroup A] (v w : A)
    (horder : 2 < addOrderOf v) (hfix : w = v) : w ≠ -v := by
  rw [hfix]
  exact ne_neg_of_order_gt_two v horder

end DkMath.Lib.Algebra.PrimeOrderSignSeparation
