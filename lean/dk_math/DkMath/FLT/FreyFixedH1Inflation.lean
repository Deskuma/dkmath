/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyInertiaH1CoefficientBoundary

#print "file: DkMath.FLT.FreyFixedH1Inflation"

/-!
# 同じ馴分岐固定係数類の実際の H¹ inflation

代表の値の一致を、Mathlib の通常の H¹ 写像の等式へ上げる。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

/-- 同じ F の恒等線形写像を、群商に沿う制限表現からの射として明示する。 -/
def ResidualCyclicStage.fixedInflationCoefficient (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Rep.res (QuotientGroup.mk' (wildInertiaSubgroup A))
      (TrivialCharacterH1.coefficient (tameInertiaQuotient A) (T.inertiaFixedUpperQuotient A)) ⟶
      TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- 同じ群商 I→J と同じ自明係数 F による、実際の通常の H¹ inflation。 -/
def ResidualCyclicStage.fixedH1Inflation (A : ValuationSubring (AlgebraicClosure ℚ)) :=
  groupCohomology.map
    (A := TrivialCharacterH1.coefficient (tameInertiaQuotient A) (T.inertiaFixedUpperQuotient A))
    (B := TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A))
    (QuotientGroup.mk' (wildInertiaSubgroup A)) (T.fixedInflationCoefficient A) 1

variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 同じ馴分岐類の inflation は、元の同じ慣性類そのもの。 -/
theorem ResidualCyclicStage.fixedTameClass_inflation
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.fixedH1Inflation A (T.fixedTameH1Class hp5 hq hqp haddr A hA x) =
      T.fixedInertiaH1Class hp5 hq hqp haddr A hA x := by
  unfold fixedH1Inflation fixedTameH1Class fixedInertiaH1Class TrivialCharacterH1.cohomologyClass
  rw [groupCohomology.H1π_comp_map_apply]
  congr 1

end
end DkMath.FLT.Frey.Source
