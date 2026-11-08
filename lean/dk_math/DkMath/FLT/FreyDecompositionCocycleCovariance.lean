/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDecompositionFixedCoefficient

#print "file: DkMath.FLT.FreyDecompositionCocycleCovariance"

/-! # 同じ点の cocycle の分解群共役輸送
作用差の恒等式から、元の F 値 cocycle の共変性まで輸送する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

/-- 一つの全 Galois 元による元の有限捩れ点の像。 -/
def ResidualCyclicStage.globalTranslateTorsion (σ : Field.absoluteGaloisGroup ℚ)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :=
  representation S.rationalCurve (p ^ (n + 1 + 1)) σ x

/-- 同じ点の商類の輸送は、元の商作用と一致する。 -/
theorem ResidualCyclicStage.globalTranslate_upperClass (σ : Field.absoluteGaloisGroup ℚ)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    (QuotientAddGroup.mk' T.upperStage) (ResidualCyclicStage.globalTranslateTorsion σ x) =
      T.upperQuotientAction σ ((QuotientAddGroup.mk' T.upperStage) x) := rfl

/-- 同じ Q 値の作用差は、点の輸送と群の共役に関して共変。 -/
theorem ResidualCyclicStage.globalCocycle_conjugate (σ τ : Field.absoluteGaloisGroup ℚ)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.fullGlobalCocycle (ResidualCyclicStage.globalTranslateTorsion σ x) τ =
      T.upperQuotientAction σ (T.fullGlobalCocycle x (σ⁻¹ * τ * σ)) := by
  change T.upperQuotientAction τ ((QuotientAddGroup.mk' T.upperStage)
    (ResidualCyclicStage.globalTranslateTorsion σ x)) -
      (QuotientAddGroup.mk' T.upperStage) (ResidualCyclicStage.globalTranslateTorsion σ x) =
    T.upperQuotientAction σ (T.upperQuotientAction (σ⁻¹ * τ * σ)
      ((QuotientAddGroup.mk' T.upperStage) x) - (QuotientAddGroup.mk' T.upperStage) x)
  rw [T.globalTranslate_upperClass]
  refine Eq.trans ?_ ((T.upperQuotientAction σ).map_sub
    (T.upperQuotientAction (σ⁻¹ * τ * σ) ((QuotientAddGroup.mk' T.upperStage) x))
    ((QuotientAddGroup.mk' T.upperStage) x)).symm
  have he : τ * σ = σ * (σ⁻¹ * τ * σ) := by group
  have hm (a b : Field.absoluteGaloisGroup ℚ) (v : T.upperQuotient) :
      T.upperQuotientAction (a * b) v = T.upperQuotientAction a (T.upperQuotientAction b v) :=
    congrArg (fun f : AddMonoid.End T.upperQuotient => f v) (T.upperQuotientAction.map_mul a b)
  apply congrArg (fun v : T.upperQuotient => v - T.upperQuotientAction σ ((QuotientAddGroup.mk' T.upperStage) x))
  calc T.upperQuotientAction τ (T.upperQuotientAction σ ((QuotientAddGroup.mk' T.upperStage) x))
      = T.upperQuotientAction (τ * σ) ((QuotientAddGroup.mk' T.upperStage) x) := (hm τ σ _).symm
    _ = T.upperQuotientAction (σ * (σ⁻¹ * τ * σ)) ((QuotientAddGroup.mk' T.upperStage) x) :=
      congrArg (fun g => T.upperQuotientAction g ((QuotientAddGroup.mk' T.upperStage) x)) he
    _ = T.upperQuotientAction σ (T.upperQuotientAction (σ⁻¹ * τ * σ) ((QuotientAddGroup.mk' T.upperStage) x)) := hm σ _ _
variable (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 分解群共役で輸送された同じ F 値の連続 cocycle が一致する。 -/
theorem ResidualCyclicStage.continuousCocycle_decomposition_conjugate
    (σ : A.decompositionSubgroup ℚ) (τ : inertiaSubgroupIn A ℚ)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.continuousConnectingCocycle A hp5 hq hqp haddr hA (ResidualCyclicStage.globalTranslateTorsion σ.val x) τ =
      T.fixedDecompositionAction A σ
        (T.continuousConnectingCocycle A hp5 hq hqp haddr hA x
          ⟨σ.val⁻¹ * τ.val * σ.val, decomposition_inv_conj_mem_inertia A σ.val τ.val σ.property τ.property⟩) := by
  apply Subtype.ext
  change (T.continuousConnectingCocycle A hp5 hq hqp haddr hA (ResidualCyclicStage.globalTranslateTorsion σ.val x) τ).val =
    T.upperQuotientAction σ.val (T.continuousConnectingCocycle A hp5 hq hqp haddr hA x _).val
  rw [T.continuousCocycle_global_restriction A hp5 hq hqp haddr hA,
    T.continuousCocycle_global_restriction A hp5 hq hqp haddr hA]
  exact T.globalCocycle_conjugate σ.val τ.val x
end
end DkMath.FLT.Frey.Source

