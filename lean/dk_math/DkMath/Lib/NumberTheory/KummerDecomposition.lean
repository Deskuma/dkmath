/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.KummerLocalValuation

#print "file: DkMath.Lib.NumberTheory.KummerDecomposition"

/-!
# 同じ生成根の分解群固定性から実際の e=f=1 へ

分解群が根を固定するなら、単純生成性により分解群そのものが自明となる。
有限数体では慣性群の位数と剰余次数の積の公式から、同じ素点の e=f=1 を得る。
これは完備化の次数との比較をまだ含まない。
-/

namespace DkMath.Lib.NumberTheory.KummerDecomposition
open CyclicKummer IsDedekindDomain
open scoped NumberField Pointwise
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {F M : Type*} [Field F] [Field M] [Algebra F M]
    {p : ℕ} (P : Presentation p F M)

/-- 生成根を固定する部分群は自明。分解群・慣性群の両方に使える代数的核心。 -/
theorem subgroup_eq_bot_of_fixes_radical (H : Subgroup (M ≃ₐ[F] M))
    (hfix : ∀ σ ∈ H, σ P.radical = P.radical) : H = ⊥ := by
  apply bot_unique
  intro σ hσ
  have he : σ = 1 := by
    apply DFunLike.ext
    intro a
    exact DFunLike.congr_fun
      (P.algHom_ext (f := σ.toAlgHom) (g := AlgHom.id F M) (hfix σ hσ)) a
  rw [he]
  exact Subgroup.one_mem ⊥

variable [NumberField F] [NumberField M] [IsGalois F M]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 M))
    [w.asIdeal.LiesOver v.asIdeal]

/-- 同じ有限分解群の固定性から、同じ素点の実際の分岐指数と剰余次数が1となる。
局所完備化の次数を仮定せず、Mathlib の整数環の位数公式で計算する。 -/
theorem ramification_and_inertiaDeg_eq_one_of_decomposition_fixes_radical
    (hfix : ∀ σ : M ≃ₐ[F] M,
      σ ∈ MulAction.stabilizer (M ≃ₐ[F] M) w.asIdeal → σ P.radical = P.radical) :
    v.asIdeal.ramificationIdx' w.asIdeal = 1 ∧ w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
  let : FiniteDimensional F M := Module.Finite.of_restrictScalars_finite ℚ F M
  let : IsGaloisGroup (M ≃ₐ[F] M) (𝓞 F) (𝓞 M) :=
    IsGaloisGroup.of_isFractionRing (M ≃ₐ[F] M) (𝓞 F) (𝓞 M) F M
  let : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have hi : ∀ σ : M ≃ₐ[F] M, σ ∈ w.asIdeal.inertia (M ≃ₐ[F] M) →
      σ P.radical = P.radical := fun σ hσ => hfix σ (Ideal.inertia_le_stabilizer w.asIdeal hσ)
  have hd := subgroup_eq_bot_of_fixes_radical P
    (MulAction.stabilizer (M ≃ₐ[F] M) w.asIdeal) hfix
  have ht := subgroup_eq_bot_of_fixes_radical P (w.asIdeal.inertia (M ≃ₐ[F] M)) hi
  refine ⟨KummerLocalValuation.ramification_eq_one_of_inertia_fixes_radical P v w hi, ?_⟩
  have hc := Ideal.card_stabilizer_eq_card_inertia_mul_finrank
    (G := M ≃ₐ[F] M) v.asIdeal w.asIdeal
  simpa only [hd, ht, Nat.card_unique, one_mul] using hc.symm

end
end DkMath.Lib.NumberTheory.KummerDecomposition
