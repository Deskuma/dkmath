/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyOpenDecompositionActionKernel
import DkMath.Lib.NumberTheory.FiniteFieldFrobeniusImage
import DkMath.Lib.RepresentationTheory.DenseFiniteImageGeneration

#print "file: DkMath.FLT.FreyFiniteFrobeniusImage"

/-! # 実際の有限作用像を Frobenius が生成するための二つの供給経路
密度または有限体 Galois 因子化は明示条件。元の住所からの無条件供給は未完成。 -/
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

/-- 元の密度入力は、必要な有限作用像の生成条件を供給する。 -/
theorem ResidualCyclicStage.finiteDecomposition_generated_of_dense
    (φ : A.decompositionSubgroup ℚ)
    (hdense : (A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) :
    ∀ σ : A.decompositionSubgroup ℚ, (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) σ ∈ Subgroup.zpowers ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) φ) :=
  DenseFiniteImageGeneration.mem_zpowers_of_dense (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) QuotientGroup.continuous_mk
    (A.inertiaSubgroup ℚ) (T.inertia_le_finiteDecompositionProjection_kernel A hp5 hq hqp haddr hA) φ hdense

/-- 有限体 Galois 作用を通じた実際の因子化があれば、密度を経由せず同じ有限像の生成を得る。 -/
theorem ResidualCyclicStage.finiteDecomposition_generated_of_field_factor
    (k E : Type*) [Field k] [Fintype k] [Field E] [Algebra k E] [FiniteDimensional k E]
    (π : A.decompositionSubgroup ℚ →* (E ≃ₐ[k] E))
    (a : (E ≃ₐ[k] E) →* T.finiteDecompositionImage A hp5 hq hqp haddr hA)
    (hfactor : (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) = a.comp π)
    (φ : A.decompositionSubgroup ℚ)
    (hφ : π φ = FiniteField.frobeniusAlgEquivOfAlgebraic k E) :
    ∀ σ : A.decompositionSubgroup ℚ, (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) σ ∈ Subgroup.zpowers ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) φ) := by
  intro σ
  obtain ⟨m, _, hm⟩ := FiniteFieldFrobeniusImage.factor_image_bounded_power k E π a φ hφ σ
  rw [hfactor]
  change a (π σ) ∈ Subgroup.zpowers (a (π φ))
  rw [hm]
  exact Subgroup.npow_mem_zpowers _ _

/-- 同じ有限像の生成条件は、元の線形作用そのものの有界な冪等式を供給する。 -/
theorem ResidualCyclicStage.finiteDecomposition_bounded_action_power
    (φ : A.decompositionSubgroup ℚ) (himage : ∀ σ : A.decompositionSubgroup ℚ, (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) σ ∈ Subgroup.zpowers ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) φ)) (σ : A.decompositionSubgroup ℚ) :
    ∃ m : ℕ, m < orderOf ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) φ) ∧ T.kernelDecompositionAction A hp5 hq hqp haddr hA σ = (T.kernelDecompositionAction A hp5 hq hqp haddr hA φ) ^ m := by
  obtain ⟨m, hm, he⟩ := DenseFiniteImageGeneration.bounded_power_of_mem_zpowers
    ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) φ) ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) σ) (himage σ)
  have hu := congrArg (T.finiteDecompositionEmbedding A hp5 hq hqp haddr hA) he
  rw [map_pow] at hu
  have hv := congrArg Units.val hu
  exact ⟨m, hm, hv.symm⟩
end
end DkMath.FLT.Frey.Source
