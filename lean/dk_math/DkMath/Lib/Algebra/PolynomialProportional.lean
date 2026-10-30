/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import Mathlib.Algebra.Polynomial.FieldDivision

#print "file: DkMath.Lib.Algebra.PolynomialProportional"

/-!
# 交差乗算からの多項式対の比例性

互いに素な分子分母対 `F,G` と交差乗算 `F * D = A * G` を考える。
`A` の次数が `F` 以下なら、Euclid 型可除性で `F ∣ A` を得たあと、商の次数が
零であることが分かる。従って商は定数 `u` であり、同じ交差乗算から
`D = u * G` も従う。

この補題はモニック性を要求しない。標準有理式の係数正規化を完全一致として
固定する前に、有限積対が標準対の共通スカラー倍であることだけを取り出すための
DkMath 教科書層である。
-/

namespace DkMath.Lib.Algebra

open Polynomial

variable {k : Type*} [Field k]

/-- [DkMath.Lib] 交差乗算と次数比較から多項式対の比例性を得る。

`hcop` と `hcross` は `F ∣ A` を与える。`hdeg` によりその商の次数は零なので、
商を `C u` と書ける。最後に `F ≠ 0` を用いて交差乗算から分母側を消去する。
-/
theorem proportional_of_cross_relation_of_coprime
    {F G A D : k[X]}
    (hcop : IsCoprime F G)
    (hF : F ≠ 0)
    (hA : A ≠ 0)
    (hcross : F * D = A * G)
    (hdeg : A.natDegree ≤ F.natDegree) :
    ∃ u : k, u ≠ 0 ∧
      A = C u * F ∧
      D = C u * G := by
  have hdiv : F ∣ A := by
    apply hcop.dvd_of_dvd_mul_right
    rw [← hcross]
    exact dvd_mul_right F D
  obtain ⟨Q, hAQ⟩ := dvd_def.mp hdiv
  have hQ : Q ≠ 0 := by
    intro hQ0
    apply hA
    rw [hAQ, hQ0, mul_zero]
  have hleading : F.leadingCoeff * Q.leadingCoeff ≠ 0 :=
    mul_ne_zero (leadingCoeff_ne_zero.mpr hF) (leadingCoeff_ne_zero.mpr hQ)
  have hdegQ : Q.natDegree = 0 := by
    rw [hAQ, natDegree_mul' hleading] at hdeg
    omega
  let u : k := Q.coeff 0
  have hQeq : Q = C u := by
    exact eq_C_of_natDegree_eq_zero hdegQ
  have hu : u ≠ 0 := by
    intro hu0
    apply hQ
    rw [hQeq, hu0, map_zero]
  refine ⟨u, hu, ?_, ?_⟩
  · rw [hAQ, hQeq]
    simp only [mul_comm]
  · have hcross' : F * D = F * (C u * G) := by
      calc
        F * D = A * G := hcross
        _ = (F * C u) * G := by rw [hAQ, hQeq]
        _ = F * (C u * G) := by ring
    exact mul_left_cancel₀ hF hcross'

end DkMath.Lib.Algebra
