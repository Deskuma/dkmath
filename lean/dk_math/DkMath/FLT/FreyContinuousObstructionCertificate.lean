/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyContinuousTameInflation
import DkMath.FLT.FreyCyclicKernelBalancedProfile

#print "file: DkMath.FLT.FreyContinuousObstructionCertificate"

/-! # 同じ障害核元の連続代表・非零単一評価・通常 H¹ 比較の証明書
連続 H¹ 全体や大域 Selmer 条件を追加の provider として導入しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ非零係数核元を、連続指標と具体的 γ で検出する。 -/
theorem NarrowAbsorptionObstruction.continuous_kernel_detected
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    ∃ k : T.fixedH1CoefficientKernel A, k ≠ 0 ∧
      T.continuousKernelCharacter A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over k
        (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) ≠ 1 ∧
      ContinuousTrivialCharacterH1.forgetClass
        (T.continuousKernelCharacter A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over k) = k.val ∧
      T.fixedH1Inflation A (ContinuousTrivialCharacterH1.forgetClass
        (T.continuousKernelTameCharacter A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over k)) = k.val := by
  let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
  let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
  have hk : k ≠ 0 := by
    intro hz
    have hv := congrArg Subtype.val hz
    have hc := (h.fixed_H1_nonzero hp5).2
    apply hc
    exact (T.fixedCosetKernelElement_val hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x).symm.trans hv
  refine ⟨k, hk, ?_, T.continuousKernelCharacter_forget A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over k, T.continuousKernelTameClass_inflation A hp5 h.prime
    h.ne_torsion_prime (Or.inr h.support) h.lies_over k⟩
  intro he
  have hv := congrArg Multiplicative.toAdd he
  change T.fixedKernelEvaluation A
    (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k = 0 at hv
  apply hk
  apply T.generator_evaluation_injective A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over
  simpa only [map_zero] using hv

/-- 同じ連続障害の通常 H¹ 像も非零で、同じ γ の値で検出される。 -/
theorem NarrowAbsorptionObstruction.continuous_class_nonzero
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    ∃ k : T.fixedH1CoefficientKernel A,
      ContinuousTrivialCharacterH1.forgetClass
        (T.continuousKernelCharacter A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over k) ≠ 0 := by
  obtain ⟨k, _, hdet, _, _⟩ := h.continuous_kernel_detected hp5
  exact ⟨k, ContinuousTrivialCharacterH1.forgetClass_ne_zero _ ⟨_, hdet⟩⟩
end
end DkMath.FLT.Frey.Source

