/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResonantFrobeniusSigns

#print "file: DkMath.FLT.FreyDecompositionOrbitContinuity"

/-! # 元の有限係数 F,Q/F,K の D 軌道の連続性
Frobenius の位相的生成性はここでは供給しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 元の Q の商位相を、同じ慣性表現の台集合に保持する。 -/
instance ResidualCyclicStage.fullInertiaCoefficientTopology : TopologicalSpace (T.fullInertiaCoefficient A) :=
  inferInstanceAs (TopologicalSpace T.upperQuotient)

/-- 元の離散 Q の位相を保持する。 -/
instance ResidualCyclicStage.fullInertiaCoefficientDiscrete : DiscreteTopology (T.fullInertiaCoefficient A) :=
  inferInstanceAs (DiscreteTopology T.upperQuotient)

/-- 元の Q/F の標準商位相を保持する。 -/
instance ResidualCyclicStage.fixedQuotientCoefficientTopology : TopologicalSpace (T.fixedQuotientCoefficient A) :=
  inferInstanceAs (TopologicalSpace (T.upperQuotient ⧸ T.inertiaFixedUpperQuotient A))

/-- 元の Q/F は標準商位相で離散。 -/
instance ResidualCyclicStage.fixedQuotientCoefficientDiscrete : DiscreteTopology (T.fixedQuotientCoefficient A) :=
  inferInstanceAs (DiscreteTopology (T.upperQuotient ⧸ T.inertiaFixedUpperQuotient A))

/-- 同じ F の D 軌道写像は、元の位相で連続。 -/
theorem ResidualCyclicStage.fixedDecomposition_orbit_continuous (z : T.inertiaFixedUpperQuotient A) :
    Continuous (fun σ : A.decompositionSubgroup ℚ => T.fixedDecompositionAction A σ z) := by
  apply Continuous.subtype_mk
  exact (T.upperQuotient_orbit_continuous z.val).comp continuous_subtype_val

/-- 同じ Q/F の D 軌道写像も商位相から連続。 -/
theorem ResidualCyclicStage.quotientDecomposition_orbit_continuous (z : T.fixedQuotientCoefficient A) :
    Continuous (fun σ : A.decompositionSubgroup ℚ => T.quotientDecompositionAction A σ z) := by
  obtain ⟨v, rfl⟩ := (T.fixedCoefficientSubmodule A).mkQ_surjective z
  exact (continuous_of_discreteTopology : Continuous (T.fixedCoefficientSubmodule A).mkQ).comp
    ((T.upperQuotient_orbit_continuous v).comp continuous_subtype_val)
variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 同じ K の軌道は、有限商から既存同型で運んだ値に関して連続。 -/
theorem ResidualCyclicStage.kernelDecomposition_orbit_evaluation_continuous
    (k : T.fixedH1CoefficientKernel A) (τ : inertiaSubgroupIn A ℚ) :
    Continuous (fun σ : A.decompositionSubgroup ℚ =>
      T.fixedKernelEvaluation A τ (T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k)) := by
  have hc := T.quotientDecomposition_orbit_continuous A
    ((T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA).symm k)
  exact (continuous_of_discreteTopology : Continuous (fun z : T.fixedQuotientCoefficient A =>
    T.fixedKernelEvaluation A τ (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA z))).comp hc
/-- 同じ具体的 γ の評価により、K の D 固定元条件は閉集合になる。 -/
theorem ResidualCyclicStage.kernelDecomposition_stabilizer_isClosed (k : T.fixedH1CoefficientKernel A) :
    IsClosed {σ : A.decompositionSubgroup ℚ | T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k} := by
  have he : {σ : A.decompositionSubgroup ℚ | T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k} =
      {σ | T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA)
        (T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k) =
        T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k} := by
    ext σ
    exact T.kernel_fixed_iff_generator_evaluation A hp5 hq hqp haddr hA σ k
  rw [he]
  exact isClosed_eq (T.kernelDecomposition_orbit_evaluation_continuous A hp5 hq hqp haddr hA k _) continuous_const
end
end DkMath.FLT.Frey.Source

