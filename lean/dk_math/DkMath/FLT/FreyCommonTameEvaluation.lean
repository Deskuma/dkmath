/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonTamePGroup

#print "file: DkMath.FLT.FreyCommonTameEvaluation"

/-!
# 同じ H と K の両側で元を識別する評価

共通商 H の元で評価しても、K→F は整数線形。H 側の積に関しては準同型となる。
元の商と元の指標値を保持した二つの分離性を公開する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 同じ共通商 H の元による K の実際の整数線形評価。 -/
def ResidualCyclicStage.fixedKernelCommonEvaluation
    (h : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) :
    T.fixedH1CoefficientKernel A →ₗ[ℤ] T.inertiaFixedUpperQuotient A where
  toFun k := Multiplicative.toAdd (T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA h k)
  map_add' x y := by
    obtain ⟨σ, rfl⟩ := T.fixedKernelCommonProjection_surjective A hp5 hq hqp haddr hA h
    exact (T.fixedKernelEvaluation A σ).map_add x y
  map_smul' m x := by
    obtain ⟨σ, rfl⟩ := T.fixedKernelCommonProjection_surjective A hp5 hq hqp haddr hA h
    exact (T.fixedKernelEvaluation A σ).map_smul' m x

/-- 同じ I の元からの像による評価は、以前の同じ慣性評価。 -/
theorem ResidualCyclicStage.fixedKernelCommonEvaluation_projection (σ : inertiaSubgroupIn A ℚ) :
    T.fixedKernelCommonEvaluation A hp5 hq hqp haddr hA
      (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA σ) = T.fixedKernelEvaluation A σ := rfl

/-- H の単位元での評価は零写像。 -/
theorem ResidualCyclicStage.fixedKernelCommonEvaluation_one :
    T.fixedKernelCommonEvaluation A hp5 hq hqp haddr hA 1 = 0 := by
  apply LinearMap.ext
  intro k
  change Multiplicative.toAdd (T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA 1 k) = 0
  rw [map_one]
  rfl

/-- K の元を固定した、同じ H 上の乗法記法の準同型。 -/
def ResidualCyclicStage.fixedKernelCommonCharacter (k : T.fixedH1CoefficientKernel A) :
    T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA →* Multiplicative (T.inertiaFixedUpperQuotient A) :=
  (Pi.evalMonoidHom (fun _ : T.fixedH1CoefficientKernel A => Multiplicative (T.inertiaFixedUpperQuotient A)) k).comp
    (T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA)

/-- H 側の指標と K 側の線形評価は同じ値を持つ。 -/
theorem ResidualCyclicStage.fixedKernelCommonCharacter_apply (k : T.fixedH1CoefficientKernel A)
    (h : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) :
    Multiplicative.toAdd (T.fixedKernelCommonCharacter A hp5 hq hqp haddr hA k h) =
      T.fixedKernelCommonEvaluation A hp5 hq hqp haddr hA h k := rfl

/-- H 側の全評価が一致すれば、同じ K の元が一致する。 -/
theorem ResidualCyclicStage.fixedKernelCommonEvaluation_separates_kernel
    (x y : T.fixedH1CoefficientKernel A)
    (he : ∀ h, T.fixedKernelCommonEvaluation A hp5 hq hqp haddr hA h x =
      T.fixedKernelCommonEvaluation A hp5 hq hqp haddr hA h y) : x = y := by
  apply T.fixedKernelCommonTameValues_separates A hp5 hq hqp haddr hA x y
  intro h
  exact congrArg Multiplicative.ofAdd (he h)

/-- K 側の全評価が一致すれば、同じ H の元が一致する。 -/
theorem ResidualCyclicStage.fixedKernelCommonEvaluation_separates_quotient
    (h g : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA)
    (he : ∀ k, T.fixedKernelCommonEvaluation A hp5 hq hqp haddr hA h k =
      T.fixedKernelCommonEvaluation A hp5 hq hqp haddr hA g k) : h = g := by
  apply T.fixedKernelCommonTameValues_injective A hp5 hq hqp haddr hA
  apply funext
  intro k
  exact congrArg Multiplicative.ofAdd (he k)

end
end DkMath.FLT.Frey.Source
