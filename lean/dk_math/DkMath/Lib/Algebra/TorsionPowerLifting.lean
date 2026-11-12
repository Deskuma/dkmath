/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.TorsionMultiplication
import Mathlib.Tactic.Abel

#print "file: DkMath.Lib.Algebra.TorsionPowerLifting"

/-!
# 二つの生成元を冪の塔へ持ち上げる

p倍で零になる群がQ₀,Q₁で生成されているとする。pᵏPᵢ=Qᵢとなる二点を選べば、
p^{k+1}倍で零になる任意の点はP₀,P₁の自然数係数の和で表せる。
最高段へ写した点を基底で表し、その分を引くと一段低い核に入る。
低い段ではpP₀,pP₁が同じQᵢを持ち上げるので、指数の帰納法が使える。
この一般群の生成補題には、素数性・有限性・局所環・Nakayamaの補題は不要である。
-/
namespace DkMath.Lib.Algebra.TorsionPowerLifting
variable {G : Type*} [AddCommGroup G]

/-- 最高段の生成元の任意の持ち上げは、冪の核全体を生成する。 -/
theorem lifted_pair_generates (p : ℕ) (Q₀ Q₁ : G)
    (hgen : ∀ x : G, p • x = 0 → ∃ a b : ℕ, x = a • Q₀ + b • Q₁) (k : ℕ) :
    ∀ P₀ P₁ : G, p ^ k • P₀ = Q₀ → p ^ k • P₁ = Q₁ →
      ∀ x : G, p ^ (k + 1) • x = 0 → ∃ a b : ℕ, x = a • P₀ + b • P₁ := by
  induction k with
  | zero =>
    intro P₀ P₁ h₀ h₁ x hx
    simp only [pow_zero, one_smul] at h₀ h₁
    subst Q₀ Q₁
    exact hgen x (by simpa only [zero_add, pow_one] using hx)
  | succ k ih =>
    intro P₀ P₁ h₀ h₁ x hx
    have htop : p • (p ^ (k + 1) • x) = 0 := by
      rw [← mul_smul, ← pow_succ']
      exact hx
    obtain ⟨a, b, hab⟩ := hgen (p ^ (k + 1) • x) htop
    let y := x - (a • P₀ + b • P₁)
    have hy : p ^ (k + 1) • y = 0 := by
      dsimp only [y]
      rw [nsmul_sub, nsmul_add, smul_comm (p ^ (k + 1)) a, smul_comm (p ^ (k + 1)) b,
        h₀, h₁, hab, sub_self]
    have hl₀ : p ^ k • (p • P₀) = Q₀ := by rw [← mul_smul, ← pow_succ]; exact h₀
    have hl₁ : p ^ k • (p • P₁) = Q₁ := by rw [← mul_smul, ← pow_succ]; exact h₁
    obtain ⟨c, d, hcd⟩ := ih (p • P₀) (p • P₁) hl₀ hl₁ y hy
    refine ⟨a + p * c, b + p * d, ?_⟩
    change x - (a • P₀ + b • P₁) = c • (p • P₀) + d • (p • P₁) at hcd
    rw [smul_comm c p, smul_comm d p] at hcd
    rw [add_nsmul, add_nsmul, mul_smul, mul_smul]
    exact (sub_eq_iff_eq_add.mp hcd).trans (by abel)

end DkMath.Lib.Algebra.TorsionPowerLifting
