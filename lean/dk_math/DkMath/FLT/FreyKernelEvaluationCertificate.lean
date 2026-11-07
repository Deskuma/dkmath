/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelEvaluationImage

#print "file: DkMath.FLT.FreyKernelEvaluationCertificate"

/-!
# 固定係数・慣性評価像・評価核の三つの指数と元の算術証明書

F と評価像にはそれぞれ同じ位数 p の元がある。従って評価核の濃度指数は n+1 以下。
この指数収支は局所障害の存在と整合する構造定理であり、算術的矛盾ではない。
最後の存在定理には元の hclass と Cofixed が明示的に残る。
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

/-- 同じ F・評価像・評価核の指数収支。評価核の指数上界は n+1。 -/
theorem NarrowAbsorptionObstruction.fixed_evaluation_balanced_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let ev := T.fixedKernelEvaluation A ⟨τ, h.inertia⟩
    ∃ r t u, 1 ≤ r ∧ r ≤ n + 2 ∧ 1 ≤ t ∧ t ≤ n + 2 ∧ u ≤ n + 1 ∧
      r + t + u = n + 3 ∧
      Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
      Nat.card (LinearMap.range ev) = p ^ t ∧ Nat.card (LinearMap.ker ev) = p ^ u ∧
      Nat.card (T.fixedH1CoefficientKernel A) = p ^ (t + u) := by
  let ev := T.fixedKernelEvaluation A ⟨τ, h.inertia⟩
  obtain ⟨r, s, hr, hrb, hs, _, hrs, hF, hK⟩ := h.fixed_kernel_sharp_profile hp5
  have hc : Nat.card (LinearMap.range ev) * Nat.card (LinearMap.ker ev) =
      Nat.card (T.fixedH1CoefficientKernel A) := T.fixedKernelEvaluation_card A ⟨τ, h.inertia⟩
  have hdR : Nat.card (LinearMap.range ev) ∣ p ^ s :=
    ⟨Nat.card (LinearMap.ker ev), hK.symm.trans hc.symm⟩
  have hdU : Nat.card (LinearMap.ker ev) ∣ p ^ s :=
    ⟨Nat.card (LinearMap.range ev), hK.symm.trans (hc.symm.trans (mul_comm _ _))⟩
  obtain ⟨t, _, hR⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdR
  obtain ⟨u, _, hU⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdU
  have ht0 : t ≠ 0 := by
    intro hz
    have hd := h.prime_dvd_evaluation_image_card hp5
    change p ∣ Nat.card (LinearMap.range ev) at hd
    rw [hR, hz, pow_zero, Nat.dvd_one] at hd
    exact (Fact.out : p.Prime).ne_one hd
  have htu : t + u = s := by
    rw [hR, hU, hK, ← pow_add] at hc
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le hc
  exact ⟨r, t, u, hr, hrb, by omega, by omega, by omega, by omega,
    hF, hR, hU, by rw [htu]; exact hK⟩

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
/-- 元の同じ算術障害を保持した、厳密位数・実際の評価・三つの濃度指数の証明書。 -/
theorem residual_exists_evaluated_coefficient_kernel
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
      let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
      let ev := T.fixedKernelEvaluation A ⟨τ, h.inertia⟩
      addOrderOf k = p ∧ ev k = h.fixedDifference hp5 ∧
      addOrderOf (h.fixedDifference hp5) = p ∧ addOrderOf (h.fixedEvaluationImageElement hp5) = p ∧
      ∃ r t u, 1 ≤ r ∧ r ≤ n + 2 ∧ 1 ≤ t ∧ t ≤ n + 2 ∧ u ≤ n + 1 ∧
        r + t + u = n + 3 ∧
        Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
        Nat.card (LinearMap.range ev) = p ^ t ∧ Nat.card (LinearMap.ker ev) = p ^ u ∧
        Nat.card (T.fixedH1CoefficientKernel A) = p ^ (t + u) := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  exact ⟨n, T, q, A, τ, y, h, h.fixedKernel_order_eq_prime hp5,
    h.fixedKernelEvaluation_obstruction hp5, h.fixedDifference_order_eq_prime hp5,
    h.fixedEvaluationImage_order_eq_prime hp5, h.fixed_evaluation_balanced_profile hp5⟩

end
end DkMath.FLT.Frey.Source
