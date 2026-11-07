/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyConnectingKernelSharpProfile

#print "file: DkMath.FLT.FreyConnectingKernelEvaluation"

/-!
# 実際の係数核を慣性元で評価する

F の作用は自明なので、Mathlib の通常の H¹ 同型が各類の一意な準同型を回収する。
その評価を実際の核 K に制限する。代表の追加選択や連続 H¹ への移行は行わない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 元の実際の係数核の元を、指定した慣性元で評価する整数線形写像。 -/
def ResidualCyclicStage.fixedKernelEvaluation (σ : inertiaSubgroupIn A ℚ) :
    T.fixedH1CoefficientKernel A →ₗ[ℤ] T.inertiaFixedUpperQuotient A where
  toFun k := (groupCohomology.H1IsoOfIsTrivial
    (TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A))).hom
      k.val (Additive.ofMul σ)
  map_add' x y := congrArg
    (fun f : Additive (inertiaSubgroupIn A ℚ) →+ T.inertiaFixedUpperQuotient A => f (Additive.ofMul σ))
    ((groupCohomology.H1IsoOfIsTrivial
      (TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A))).hom.hom.map_add x.val y.val)
  map_smul' m x := congrArg
    (fun f : Additive (inertiaSubgroupIn A ℚ) →+ T.inertiaFixedUpperQuotient A => f (Additive.ofMul σ))
    ((groupCohomology.H1IsoOfIsTrivial
      (TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A))).hom.hom.map_smul m x.val)

/-- 全慣性元での評価が一致すれば、同じ核の元そのものが一致する。 -/
theorem ResidualCyclicStage.fixedKernelEvaluation_separates
    (x y : T.fixedH1CoefficientKernel A)
    (he : ∀ σ, T.fixedKernelEvaluation A σ x = T.fixedKernelEvaluation A σ y) : x = y := by
  apply Subtype.ext
  apply (CategoryTheory.Iso.toLinearEquiv (groupCohomology.H1IsoOfIsTrivial
    (TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A)))).injective
  apply AddMonoidHom.ext
  intro σ
  exact he σ.toMul

variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

/-- 以前の同じ核元の評価は、元の同じ固定差分指標の値である。 -/
theorem ResidualCyclicStage.fixedKernelEvaluation_coset
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ : inertiaSubgroupIn A ℚ) :
    T.fixedKernelEvaluation A σ (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x) =
      Multiplicative.toAdd (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x σ) := by
  change (groupCohomology.H1IsoOfIsTrivial _).hom
    (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x).val (Additive.ofMul σ) = _
  rw [T.fixedCosetKernelElement_val hp5 hq hqp haddr A hA x]
  exact TrivialCharacterH1.class_evaluate _ σ

end
end DkMath.FLT.Frey.Source
