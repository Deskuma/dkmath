/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelCommonTameQuotient

#print "file: DkMath.FLT.FreyKernelFiniteDetector"

/-!
# 同じ核を識別する有限個の実際の慣性元

有限 K の各非零元を検出する実際の慣性元を選び、指定された元も保持する。
生成元の存在や単一評価の単射性を仮定せず、有限評価写像の単射性を構成する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 指定した有限集合 Ω の元による、元の実際の評価のベクトル。 -/
def ResidualCyclicStage.fixedFiniteEvaluation (Ω : Finset (inertiaSubgroupIn A ℚ)) :
    T.fixedH1CoefficientKernel A →ₗ[ℤ] (Ω → T.inertiaFixedUpperQuotient A) where
  toFun k σ := T.fixedKernelEvaluation A σ.val k
  map_add' x y := by funext σ; exact map_add (T.fixedKernelEvaluation A σ.val) x y
  map_smul' m x := by funext σ; exact (T.fixedKernelEvaluation A σ.val).map_smul' m x

/-- 有限評価が単射なら、実際の核の濃度は |F|^|Ω| を割る。 -/
theorem ResidualCyclicStage.fixedFiniteEvaluation_card_dvd
    (Ω : Finset (inertiaSubgroupIn A ℚ)) (hinj : Function.Injective (T.fixedFiniteEvaluation A Ω)) :
    Nat.card (T.fixedH1CoefficientKernel A) ∣ Nat.card (T.inertiaFixedUpperQuotient A) ^ Ω.card := by
  have hd := AddSubgroup.card_dvd_of_injective (T.fixedFiniteEvaluation A Ω).toAddMonoidHom hinj
  simpa only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_coe] using hd

variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 指定した σ₀ を含む有限集合を構成し、全核をその評価で識別する。 -/
theorem ResidualCyclicStage.exists_finite_inertia_detector (σ₀ : inertiaSubgroupIn A ℚ) :
    ∃ Ω : Finset (inertiaSubgroupIn A ℚ), σ₀ ∈ Ω ∧
      Ω.card ≤ Nat.card (T.fixedH1CoefficientKernel A) ∧
      Function.Injective (T.fixedFiniteEvaluation A Ω) := by
  classical
  let := T.fixedKernel_finite A hp5 hq hqp haddr hA
  let := Fintype.ofFinite (T.fixedH1CoefficientKernel A)
  have hex (k : T.fixedH1CoefficientKernel A) (hk : k ≠ 0) :
      ∃ σ, T.fixedKernelEvaluation A σ k ≠ 0 := by
    by_contra! he
    apply hk
    apply T.fixedKernelEvaluation_separates A k 0
    intro σ
    exact (he σ).trans (map_zero _).symm
  let g : T.fixedH1CoefficientKernel A → inertiaSubgroupIn A ℚ :=
    fun k => if hk : k = 0 then 1 else Classical.choose (hex k hk)
  have hg (k : T.fixedH1CoefficientKernel A) (hk : k ≠ 0) :
      T.fixedKernelEvaluation A (g k) k ≠ 0 := by
    simpa only [g, dite_eq_right hk] using Classical.choose_spec (hex k hk)
  let D := (Finset.univ.erase (0 : T.fixedH1CoefficientKernel A)).image g
  let Ω := insert σ₀ D
  have hdet (k : T.fixedH1CoefficientKernel A)
      (he : ∀ σ ∈ Ω, T.fixedKernelEvaluation A σ k = 0) : k = 0 := by
    by_contra hk
    apply hg k hk
    apply he
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨k, Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩, rfl⟩
  have hD : D.card ≤ Fintype.card (T.fixedH1CoefficientKernel A) - 1 := by
    calc
      D.card ≤ (Finset.univ.erase (0 : T.fixedH1CoefficientKernel A)).card := Finset.card_image_le
      _ = Fintype.card (T.fixedH1CoefficientKernel A) - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hΩ := Finset.card_insert_le σ₀ D
  have hpos : 0 < Fintype.card (T.fixedH1CoefficientKernel A) := Fintype.card_pos
  refine ⟨Ω, Finset.mem_insert_self _ _, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card]
    change (insert σ₀ D).card ≤ _
    omega
  · intro x y hxy
    apply sub_eq_zero.mp
    apply hdet
    intro σ hσ
    rw [map_sub, sub_eq_zero]
    exact congrFun hxy ⟨σ, hσ⟩

end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation CyclotomicKernelField CyclotomicKummerWeight ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)

include hline hζ hp5 hclass in
/-- 元の障害元を保持し、全核の有限検出・連続性・inflation 回収・指数制約を出力する。 -/
theorem residual_exists_finitely_detected_coefficient_kernel
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let ev := T.fixedKernelEvaluation A ⟨τ, h.inertia⟩
      ∃ Ω : Finset (inertiaSubgroupIn A ℚ), ⟨τ, h.inertia⟩ ∈ Ω ∧
        Ω.card ≤ Nat.card (T.fixedH1CoefficientKernel A) ∧
        Function.Injective (T.fixedFiniteEvaluation A Ω) ∧
        Finite (T.fixedKernelCommonTameQuotient A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over) ∧
        (∀ k : T.fixedH1CoefficientKernel A, Continuous (T.fixedKernelCharacter A k) ∧
          T.fixedH1Inflation A (T.fixedKernelTameClass A hp5 h.prime h.ne_torsion_prime
            (Or.inr h.support) h.lies_over k) = k.val) ∧
        ∃ r t u, 1 ≤ r ∧ r ≤ n + 2 ∧ 1 ≤ t ∧ t ≤ r ∧ u ≤ n + 1 ∧
          n + 3 - 2 * r ≤ u ∧ r + t + u = n + 3 ∧ t + u ≤ r * Ω.card ∧
          Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
          Nat.card (LinearMap.range ev) = p ^ t ∧ Nat.card (LinearMap.ker ev) = p ^ u ∧
          Nat.card (T.fixedH1CoefficientKernel A) = p ^ (t + u) := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  obtain ⟨Ω, hτ, hΩ, hi⟩ := T.exists_finite_inertia_detector A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over ⟨τ, h.inertia⟩
  obtain ⟨r, t, u, hr, hrb, ht, htr, hu, hul, hsum, hF, hB, hU, hK⟩ :=
    h.fixed_evaluation_constrained_profile hp5
  have hd := T.fixedFiniteEvaluation_card_dvd A Ω hi
  rw [hK, hF, ← pow_mul] at hd
  have hmeasure := (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hd
  exact ⟨n, T, q, A, τ, y, h, Ω, hτ, hΩ, hi,
    T.fixedKernelCommonTameQuotient_finite A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over,
    fun k => ⟨T.fixedKernelCharacter_continuous A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over k,
      T.fixedKernelTameClass_inflation A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over k⟩,
    r, t, u, hr, hrb, ht, htr, hu, hul, hsum, hmeasure, hF, hB, hU, hK⟩

end
end DkMath.FLT.Frey.Source
