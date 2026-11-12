/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.FieldTheory.Finite.Basic

#print "file: DkMath.Lib.NumberTheory.FiniteFieldFrobeniusImage"

/-! # 有限体拡大の実際の Frobenius による有界生成
元の付値環の剰余作用がこの有限体拡大へ因子化することは別の算術である。 -/
namespace DkMath.Lib.NumberTheory.FiniteFieldFrobeniusImage
variable (k E : Type*) [Field k] [Fintype k] [Field E] [Algebra k E] [FiniteDimensional k E]

/-- 有限体拡大の各自己同型は、拡大次数未満の Frobenius 冪。 -/
theorem exists_bounded_power (σ : E ≃ₐ[k] E) :
    ∃ n : ℕ, n < Module.finrank k E ∧
      FiniteField.frobeniusAlgEquivOfAlgebraic k E ^ n = σ := by
  let := Module.finite_of_finite k (M := E)
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k E).surjective σ
  exact ⟨n.val, n.isLt, hn⟩

/-- 有限体 Galois 作用に実際に因子化する表現の像は、対応する Frobenius の像の冪。 -/
theorem factor_image_bounded_power {G M : Type*} [Group G] [Monoid M]
    (π : G →* (E ≃ₐ[k] E)) (a : (E ≃ₐ[k] E) →* M)
    (φ : G) (hφ : π φ = FiniteField.frobeniusAlgEquivOfAlgebraic k E) (g : G) :
    ∃ n : ℕ, n < Module.finrank k E ∧ a (π g) = a (π φ) ^ n := by
  obtain ⟨n, hn, he⟩ := exists_bounded_power k E (π g)
  refine ⟨n, hn, ?_⟩
  rw [hφ, ← map_pow, he]
end DkMath.Lib.NumberTheory.FiniteFieldFrobeniusImage
