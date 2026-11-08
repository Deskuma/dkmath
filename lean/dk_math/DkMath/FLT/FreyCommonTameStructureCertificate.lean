/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonTameGeneratorCriterion

#print "file: DkMath.FLT.FreyCommonTameStructureCertificate"

/-!
# 非自明な共通有限可換 p 群と、巡回性が得られた場合の数値制約

元の障害慣性元の像を保持し、H の非自明性を同じ位数 p の差分で検出する。
最終定理は巡回性を仮定しない。巡回性が別途証明された場合の帰結は含意として出力する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 元の同じ障害慣性元の、同じ共通有限商での像。 -/
def NarrowAbsorptionObstruction.commonInertiaElement
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :=
  T.fixedKernelCommonProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over ⟨τ, h.inertia⟩

/-- この同じ共通商元による同じ核元の評価は、元の同じ固定差分。 -/
theorem NarrowAbsorptionObstruction.commonInertiaElement_evaluation
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    T.fixedKernelCommonEvaluation A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over
      (h.commonInertiaElement hp5)
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩) =
      h.fixedDifference hp5 := h.fixedKernelEvaluation_obstruction hp5

/-- 位数 p の同じ差分を検出するので、元の慣性像は H の単位元ではない。 -/
theorem NarrowAbsorptionObstruction.commonInertiaElement_ne_one
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) : h.commonInertiaElement hp5 ≠ 1 := by
  intro hz
  have he := h.commonInertiaElement_evaluation hp5
  rw [hz, T.fixedKernelCommonEvaluation_one A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over] at he
  have hd : h.fixedDifference hp5 = 0 := he.symm
  have ho := h.fixedDifference_order_eq_prime hp5
  rw [hd, addOrderOf_zero] at ho
  exact (Fact.out : p.Prime).ne_one ho.symm

/-- 同じ障害により、H の p 冪濃度指数も正。元の F の指数上界は n+2。 -/
theorem NarrowAbsorptionObstruction.commonTame_positive_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    ∃ r m, 1 ≤ r ∧ r ≤ n + 2 ∧ 1 ≤ m ∧ m ≤ r * Nat.card (T.fixedH1CoefficientKernel A) ∧
      Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
      Nat.card (T.fixedKernelCommonTameQuotient A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over) = p ^ m ∧
      ∀ u : T.fixedKernelCommonTameQuotient A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over,
        u ^ (p ^ r) = 1 := by
  obtain ⟨r, _, hr, hrb, _, _, _, hF, _⟩ := h.fixed_kernel_sharp_profile hp5
  have hd := T.fixedKernelCommonTame_card_dvd A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over
  rw [hF, ← pow_mul] at hd
  obtain ⟨m, hm, hH⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd
  have hm0 : m ≠ 0 := by
    intro hz
    have hc1 := hH.trans (by rw [hz, pow_zero])
    have hu := (Nat.card_eq_one_iff_unique.mp hc1).1
    exact h.commonInertiaElement_ne_one hp5 (hu.elim _ 1)
  exact ⟨r, m, hr, hrb, by omega, hm, hF, hH,
    fun u => hF ▸ T.fixedKernelCommonTame_pow_card_fixed A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over u⟩

/-- 巡回性が別途得られれば、単一評価と r+s=n+3、s≤r、n+3≤2r が従う。 -/
theorem NarrowAbsorptionObstruction.single_evaluation_profile_of_common_isCyclic
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (hcyclic : IsCyclic (T.fixedKernelCommonTameQuotient A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over)) :
    ∃ (γ : inertiaSubgroupIn A ℚ) (r s : ℕ), Function.Injective (T.fixedKernelEvaluation A γ) ∧
      1 ≤ r ∧ 1 ≤ s ∧ r + s = n + 3 ∧ s ≤ r ∧ n + 3 ≤ 2 * r ∧
      Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧ Nat.card (T.fixedH1CoefficientKernel A) = p ^ s := by
  obtain ⟨γ, hi, hd⟩ := T.exists_single_evaluation_of_common_isCyclic A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over hcyclic
  obtain ⟨r, s, hr, hs, hsum, hF, hK⟩ := h.fixed_kernel_balanced_profile hp5
  rw [hF, hK] at hd
  have hsr := (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hd
  exact ⟨γ, r, s, hi, hr, hs, hsum, hsr, by omega, hF, hK⟩

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
/-- 元の同じ証明書から、非自明な有限可換 p 群と、巡回性を得た場合の含意を出力する。 -/
theorem residual_exists_nontrivial_common_tame_pGroup
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let H := T.fixedKernelCommonTameQuotient A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over
      h.commonInertiaElement hp5 ≠ 1 ∧ Finite H ∧ IsPGroup p H ∧ (∀ u v : H, u * v = v * u) ∧
      (∃ r m, 1 ≤ r ∧ r ≤ n + 2 ∧ 1 ≤ m ∧ m ≤ r * Nat.card (T.fixedH1CoefficientKernel A) ∧
        Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧ Nat.card H = p ^ m ∧ ∀ u : H, u ^ (p ^ r) = 1) ∧
      (IsCyclic H → ∃ (γ : inertiaSubgroupIn A ℚ) (r s : ℕ), Function.Injective (T.fixedKernelEvaluation A γ) ∧
        1 ≤ r ∧ 1 ≤ s ∧ r + s = n + 3 ∧ s ≤ r ∧ n + 3 ≤ 2 * r ∧
        Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧ Nat.card (T.fixedH1CoefficientKernel A) = p ^ s) := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  exact ⟨n, T, q, A, τ, y, h, h.commonInertiaElement_ne_one hp5,
    T.fixedKernelCommonTameQuotient_finite A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over,
    T.fixedKernelCommonTame_isPGroup A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over,
    T.fixedKernelCommonTame_mul_comm A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over,
    h.commonTame_positive_profile hp5, h.single_evaluation_profile_of_common_isCyclic hp5⟩

end
end DkMath.FLT.Frey.Source
