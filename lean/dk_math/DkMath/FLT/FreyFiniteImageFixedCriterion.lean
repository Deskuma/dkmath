/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteFrobeniusImage

#print "file: DkMath.FLT.FreyFiniteImageFixedCriterion"

/-! # 有限作用像の生成だけから同じ k の D 固定性へ
D 全体の密度を入力にしない。有限像の生成自体の算術的供給は別工程。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

/-- 同じ有限作用像が生成されれば、φ 固定性から全 D 固定性が従う。 -/
theorem ResidualCyclicStage.kernel_fixed_of_finite_image
    (φ : A.decompositionSubgroup ℚ) (himage : ∀ σ : A.decompositionSubgroup ℚ, (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) σ ∈ Subgroup.zpowers ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) φ))
    (k : T.fixedH1CoefficientKernel A) (hfixed : T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k = k) :
    ∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k := by
  let f : Module.End ℤ (T.fixedH1CoefficientKernel A) := T.kernelDecompositionAction A hp5 hq hqp haddr hA φ
  have hp : ∀ m : ℕ, (f ^ m) k = k := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      calc (f ^ (m + 1)) k = (f ^ m) (f k) :=
            congrArg (fun z : Module.End ℤ (T.fixedH1CoefficientKernel A) => z k) (pow_succ f m)
        _ = (f ^ m) k := congrArg (fun z : T.fixedH1CoefficientKernel A => (f ^ m) z) hfixed
        _ = k := ih
  intro σ
  obtain ⟨m, _, hm⟩ := T.finiteDecomposition_bounded_action_power A hp5 hq hqp haddr hA φ himage σ
  exact (congrArg (fun z : Module.End ℤ (T.fixedH1CoefficientKernel A) => z k) hm).trans (hp m)

/-- 有限像生成の下で、全 D 固定性を同じ γ の固有値で判定する。 -/
theorem ResidualCyclicStage.decomposition_fixed_iff_eigenvalue_of_finite_image
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (himage : ∀ σ : A.decompositionSubgroup ℚ, (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) σ ∈ Subgroup.zpowers ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) φ)) (k : T.fixedH1CoefficientKernel A) :
    (∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k) ↔
      T.fixedDecompositionAction A φ
        (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k) =
      q • T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k :=
  (show (∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k) ↔ T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k = k from
    ⟨fun h => h φ, T.kernel_fixed_of_finite_image A hp5 hq hqp haddr hA φ himage k⟩).trans
      (T.kernelFrobenius_fixed_iff A hp5 hq hqp haddr hA φ hφ k)
end
end DkMath.FLT.Frey.Source
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 有限像生成の下で、元の共鳴符号条件は同じ障害核元の hD と同値。 -/
theorem NarrowAbsorptionObstruction.decomposition_fixed_iff_resonant_sign_of_finite_image
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (himage : ∀ σ : A.decompositionSubgroup ℚ, (T.finiteDecompositionProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over) σ ∈ Subgroup.zpowers ((T.finiteDecompositionProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over) φ)) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    (∀ σ, T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over σ k = k) ↔ ((q : ZMod p) = 1 ∧ T.fixedDecompositionAction A φ v = v) ∨
      ((q : ZMod p) = -1 ∧ T.fixedDecompositionAction A φ v = -v) := by
  have he := T.decomposition_fixed_iff_eigenvalue_of_finite_image A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over φ hφ himage (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩)
  constructor
  · intro hD
    have hv := he.mp hD
    rcases h.resonance with hplus | hminus
    · exact Or.inl ⟨hplus, hv.trans (h.generatorValue_q_smul_plus hp5 hplus)⟩
    · exact Or.inr ⟨hminus, hv.trans (h.generatorValue_q_smul_minus hp5 hminus)⟩
  · intro hs
    apply he.mpr
    rcases hs with ⟨hplus, hv⟩ | ⟨hminus, hv⟩
    · exact hv.trans (h.generatorValue_q_smul_plus hp5 hplus).symm
    · exact hv.trans (h.generatorValue_q_smul_minus hp5 hminus).symm
end
end DkMath.FLT.Frey.Source
