/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedDifferencePrimeOrder

#print "file: DkMath.FLT.FreyConnectingKernelSharpProfile"

/-!
# 固定部分群と係数核の指数収支、改善された上界 n+2

F の同じ非零差分と K の同じ非零類を別々に使う。両方の指数が正なので、
濃度積の指数 n+3 は r+s に正確に分かれる。新しい算術仮定を加えない。
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

/-- 元の同じ固定部分群 F の濃度は、正の指数の p 冪。 -/
theorem NarrowAbsorptionObstruction.fixed_positive_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    ∃ r, 1 ≤ r ∧ r ≤ n + 3 ∧ Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r := by
  have hd : Nat.card (T.inertiaFixedUpperQuotient A) ∣ p ^ (n + 3) := by
    refine ⟨Nat.card (T.fixedH1CoefficientKernel A), ?_⟩
    rw [mul_comm]
    exact (T.fixedKernel_card_mul_fixed A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over).symm
  obtain ⟨r, hr, hc⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd
  have hr0 : r ≠ 0 := by
    intro hz
    have hd1 := h.prime_dvd_fixed_card hp5
    rw [hc, hz, pow_zero, Nat.dvd_one] at hd1
    exact (Fact.out : p.Prime).ne_one hd1
  exact ⟨r, by omega, hr, hc⟩

/-- 元の同じ F と K の濃度指数は正で、和は正確に n+3。 -/
theorem NarrowAbsorptionObstruction.fixed_kernel_balanced_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    ∃ r s, 1 ≤ r ∧ 1 ≤ s ∧ r + s = n + 3 ∧
      Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
      Nat.card (T.fixedH1CoefficientKernel A) = p ^ s := by
  obtain ⟨r, hr, _, hF⟩ := h.fixed_positive_profile hp5
  obtain ⟨s, hs, _, hK⟩ := h.fixedKernel_positive_profile hp5
  have he := T.fixedKernel_card_mul_fixed A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over
  rw [hF, hK, ← pow_add] at he
  have hsum : s + r = n + 3 := Nat.pow_right_injective (Fact.out : p.Prime).two_le he
  exact ⟨r, s, hr, hs, by omega, hF, hK⟩

/-- レビュー提案の改善：両方の正の濃度指数は n+2 以下。 -/
theorem NarrowAbsorptionObstruction.fixed_kernel_sharp_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    ∃ r s, 1 ≤ r ∧ r ≤ n + 2 ∧ 1 ≤ s ∧ s ≤ n + 2 ∧ r + s = n + 3 ∧
      Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
      Nat.card (T.fixedH1CoefficientKernel A) = p ^ s := by
  obtain ⟨r, s, hr, hs, hsum, hF, hK⟩ := h.fixed_kernel_balanced_profile hp5
  exact ⟨r, s, hr, by omega, hs, by omega, hsum, hF, hK⟩

end
end DkMath.FLT.Frey.Source
