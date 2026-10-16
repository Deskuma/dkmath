/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.UnitPowerClass
import Mathlib.Tactic.LinearCombination

/-!
# 冪根の単元倍による取り替え

根を t 倍し、係数単元を t^(-n) 倍すれば、元の積は保存される。
さらに t^n≡1 mod m なら、係数単元の一次合同も保存される。
具体的な数体や降下の仮定を含まない有限恒等式。
-/

namespace DkMath.Lib.Algebra

/-- 根と単元の同時取り替えは、分岐因子を含む同じ source を保存する。 -/
theorem root_unit_gauge_identity {R : Type*} [CommRing R]
    (a b : R) (u t : Rˣ) (n : ℕ) :
    a * ((u : R) * b ^ n) = a * (((u * t⁻¹ ^ n : Rˣ) : R) * ((t : R) * b) ^ n) := by
  have hc : (t : R) * (↑t⁻¹ : R) = 1 := t.val_inv
  change a * ((u : R) * b ^ n) = a * (((u : R) * (↑t⁻¹ : R) ^ n) * ((t : R) * b) ^ n)
  calc
    a * ((u : R) * b ^ n) = a * ((u : R) * b ^ n) * ((t : R) * (↑t⁻¹ : R)) ^ n := by
      rw [hc, one_pow, mul_one]
    _ = _ := by simp only [mul_pow]; ring

/-- t^n≡1 なら逆単元の n 乗も同じ合同を満たす。 -/
theorem dvd_unit_inv_pow_sub_one {R : Type*} [CommRing R]
    (m : R) (t : Rˣ) (n : ℕ) (ht : m ∣ (t : R) ^ n - 1) :
    m ∣ (↑t⁻¹ : R) ^ n - 1 := by
  have hc : (t : R) ^ n * (↑t⁻¹ : R) ^ n = 1 := by
    rw [← mul_pow]
    have hh : (t : R) * (↑t⁻¹ : R) = 1 := t.val_inv
    rw [hh, one_pow]
  have he : (↑t⁻¹ : R) ^ n - 1 = -((t : R) ^ n - 1) * (↑t⁻¹ : R) ^ n := by
    linear_combination hc
  rw [he]
  exact dvd_mul_of_dvd_left (dvd_neg.mpr ht) _

/-- 同じ係数 b との一次合同を、許容される根の取り替えで保持する。 -/
theorem dvd_regauged_unit_sub {R : Type*} [CommRing R]
    (m b : R) (u t : Rˣ) (n : ℕ) (hu : m ∣ (u : R) - b) (ht : m ∣ (t : R) ^ n - 1) :
    m ∣ ((u * t⁻¹ ^ n : Rˣ) : R) - b := by
  have hi := dvd_unit_inv_pow_sub_one m t n ht
  have he : ((u * t⁻¹ ^ n : Rˣ) : R) - b = (u : R) * ((↑t⁻¹ : R) ^ n - 1) + ((u : R) - b) := by
    change (u : R) * (↑t⁻¹ : R) ^ n - b = _
    ring
  rw [he]
  exact dvd_add (dvd_mul_of_dvd_right hi (u : R)) hu

end DkMath.Lib.Algebra
