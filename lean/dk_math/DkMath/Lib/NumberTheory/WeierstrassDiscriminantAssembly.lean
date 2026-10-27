/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from the delta_identity argument in
S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.lean,
blob 0c42a9282f1033d6d64cc213bb1f7c7c52b17d1e.
-/
import DkMath.Lib.NumberTheory.WeierstrassDiscriminantRoots

#print "file: DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly"

/-!
# 三組の根の差から判別式積公式を組み立てる

[DkMath.Lib] 源と標的の三根、それぞれの半核距離積 H₁,H₂,H₃、三組の根の差の
関係式から判別式の積恒等式を導く。これは純粋な体の計算であり、三組の関係式を
実際の Vélu 写像から供給する幾何学的な証明は別途必要である。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly
variable {k : Type*} [Field k]

/-- [DkMath.Lib] 有理式による座標評価と移動された点の積の関係から、
三組の差に共通する一つの関係式を作る。分母で割る代わりに両辺へ因子を掛ける。 -/
theorem pair_relation (n : ℕ) (G Hj Hk Hl Xj Xk ej ek A : k)
    (hA : A = Hk ^ 2 * Xk)
    (hF : A - Xj * Hk ^ 2 = (ek - ej) * G ^ 2)
    (hG : G * Hj = (ek - ej) ^ n * Hl) :
    (Xj - Xk) ^ 2 * Hj ^ 4 * Hk ^ 4 =
      (ek - ej) ^ (2 * (2 * n + 1)) * Hl ^ 4 := by
  have h : (Xk - Xj) * Hk ^ 2 * Hj ^ 2 = (ek - ej) * (G * Hj) ^ 2 := by
    linear_combination Hj ^ 2 * (hF - hA)
  rw [hG] at h
  calc
    _ = ((Xk - Xj) * Hk ^ 2 * Hj ^ 2) ^ 2 := by ring
    _ = ((ek - ej) * ((ek - ej) ^ n * Hl) ^ 2) ^ 2 := by rw [h]
    _ = _ := by ring

/-- [DkMath.Lib] 三組の根の差の関係を掛け合わせ、共通の非零因子を消去する。
`n` は半核の大きさ、`Hᵢ` は源の第 i 根への距離積、`U` は接線分母積を表す。
`P₁₂` などの仮定は実際の商写像から別に証明する必要がある。 -/
theorem discriminant_product_of_pair_relations
    (n : ℕ) (e₁ e₂ e₃ X₁ X₂ X₃ Δ Δ' H₁ H₂ H₃ U : k)
    (hH : H₁ * H₂ * H₃ ≠ 0)
    (hU : U = 4 ^ n * (H₁ * H₂ * H₃))
    (hΔ : Δ = 16 * ((e₂ - e₁) * (e₃ - e₁) * (e₃ - e₂)) ^ 2)
    (hΔ' : Δ' = 16 * ((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2)
    (P₁₂ : (X₁ - X₂) ^ 2 * H₁ ^ 4 * H₂ ^ 4 =
      (e₂ - e₁) ^ (2 * (2 * n + 1)) * H₃ ^ 4)
    (P₁₃ : (X₁ - X₃) ^ 2 * H₁ ^ 4 * H₃ ^ 4 =
      (e₃ - e₁) ^ (2 * (2 * n + 1)) * H₂ ^ 4)
    (P₂₃ : (X₂ - X₃) ^ 2 * H₂ ^ 4 * H₃ ^ 4 =
      (e₃ - e₂) ^ (2 * (2 * n + 1)) * H₁ ^ 4) :
    Δ' * U ^ 4 = Δ ^ (2 * n + 1) := by
  have h16 : (16 : k) ^ (2 * n + 1) = 16 * ((4 : k) ^ n) ^ 4 := by
    rw [pow_succ, pow_mul, ← pow_mul (4 : k) n 4, mul_comm n 4, pow_mul,
      show ((16 : k)) ^ 2 = 4 ^ 4 by norm_num]
    ring
  generalize e₂ - e₁ = a at P₁₂ hΔ
  generalize e₃ - e₁ = b at P₁₃ hΔ
  generalize e₃ - e₂ = c at P₂₃ hΔ
  have hP0 : (H₁ * H₂ * H₃) ^ 4 ≠ 0 := pow_ne_zero 4 hH
  have key : ((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2 *
      (H₁ * H₂ * H₃) ^ 4 * (H₁ * H₂ * H₃) ^ 4 =
      a ^ (2 * (2 * n + 1)) * b ^ (2 * (2 * n + 1)) *
        c ^ (2 * (2 * n + 1)) * (H₁ * H₂ * H₃) ^ 4 := by
    have eqprod : ((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2 *
        (H₁ * H₂ * H₃) ^ 4 * (H₁ * H₂ * H₃) ^ 4 =
        ((X₁ - X₂) ^ 2 * H₁ ^ 4 * H₂ ^ 4) *
        ((X₁ - X₃) ^ 2 * H₁ ^ 4 * H₃ ^ 4) *
        ((X₂ - X₃) ^ 2 * H₂ ^ 4 * H₃ ^ 4) := by ring
    rw [eqprod, P₁₂, P₁₃, P₂₃]
    ring
  have key2 : ((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2 *
      (H₁ * H₂ * H₃) ^ 4 =
      a ^ (2 * (2 * n + 1)) * b ^ (2 * (2 * n + 1)) *
        c ^ (2 * (2 * n + 1)) := mul_right_cancel₀ hP0 key
  calc
    Δ' * U ^ 4 = 16 * (4 ^ n) ^ 4 *
        (((X₁ - X₂) * (X₁ - X₃) * (X₂ - X₃)) ^ 2 * (H₁ * H₂ * H₃) ^ 4) := by
      rw [hΔ', hU]; ring
    _ = 16 * (4 ^ n) ^ 4 * (a ^ (2 * (2 * n + 1)) *
        b ^ (2 * (2 * n + 1)) * c ^ (2 * (2 * n + 1))) := by rw [key2]
    _ = Δ ^ (2 * n + 1) := by rw [hΔ, mul_pow, h16]; ring

end DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly
