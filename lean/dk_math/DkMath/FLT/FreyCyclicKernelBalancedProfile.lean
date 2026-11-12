/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonTameCyclicClosure

#print "file: DkMath.FLT.FreyCyclicKernelBalancedProfile"

/-! # 実装済み単一評価による障害の指数制約
巡回性を追加仮定とせず、同じ元の F と K の指数を制限する。矛盾は結論しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ具体的な生成元の単一評価から s≤r と半分の上界を内部供給する。 -/
theorem NarrowAbsorptionObstruction.cyclic_balanced_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    ∃ r s, 1 ≤ r ∧ 1 ≤ s ∧ r + s = n + 3 ∧ s ≤ r ∧
      2 * s ≤ n + 3 ∧ s ≤ (n + 3) / 2 ∧ n + 3 ≤ 2 * r ∧
      Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
      Nat.card (T.fixedH1CoefficientKernel A) = p ^ s := by
  obtain ⟨r, s, hr, hs, hsum, hF, hK⟩ := h.fixed_kernel_balanced_profile hp5
  have hd := T.kernel_card_dvd_fixed_of_radical_generator A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over
  rw [hF, hK] at hd
  have hsr := (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hd
  exact ⟨r, s, hr, hs, hsum, hsr, by omega, by omega, by omega, hF, hK⟩

/-- n=0 段の実際の障害なら、同じ F と K の濃度は一意に決まる。 -/
theorem NarrowAbsorptionObstruction.stage_zero_card_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) (hn : n = 0) :
    Nat.card (T.inertiaFixedUpperQuotient A) = p ^ 2 ∧
      Nat.card (T.fixedH1CoefficientKernel A) = p := by
  obtain ⟨r, s, hr, hs, hsum, hsr, _, _, _, hF, hK⟩ := h.cyclic_balanced_profile hp5
  have hr2 : r = 2 := by omega
  have hs1 : s = 1 := by omega
  simpa only [hr2, hs1, pow_one] using And.intro hF hK

/-- n=1 段では指数対が (3,1) または (2,2) に限定される。 -/
theorem NarrowAbsorptionObstruction.stage_one_card_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) (hn : n = 1) :
    (Nat.card (T.inertiaFixedUpperQuotient A) = p ^ 3 ∧
      Nat.card (T.fixedH1CoefficientKernel A) = p) ∨
    (Nat.card (T.inertiaFixedUpperQuotient A) = p ^ 2 ∧
      Nat.card (T.fixedH1CoefficientKernel A) = p ^ 2) := by
  obtain ⟨r, s, hr, hs, hsum, hsr, _, _, _, hF, hK⟩ := h.cyclic_balanced_profile hp5
  have hc : (r = 3 ∧ s = 1) ∨ (r = 2 ∧ s = 2) := by omega
  rcases hc with ⟨hr3, hs1⟩ | ⟨hr2, hs2⟩
  · exact Or.inl (by simpa only [hr3, hs1, pow_one] using And.intro hF hK)
  · exact Or.inr (by simpa only [hr2, hs2] using And.intro hF hK)
end
end DkMath.FLT.Frey.Source

