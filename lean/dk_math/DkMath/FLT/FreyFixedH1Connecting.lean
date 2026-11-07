/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyInvariantCosetObstruction

#print "file: DkMath.FLT.FreyFixedH1Connecting"

/-!
# 実際の短完全列の連結準同型で同じ H¹ 類を回収する

Mathlib の δ₀_apply の符号規約を使い、同じ [x]+F の像が同じ差分類であることを証明する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

/-- 同じ実際の短完全列に対する、通常の H⁰→H¹ 連結準同型。 -/
noncomputable abbrev ResidualCyclicStage.fixedConnecting (A : ValuationSubring (AlgebraicClosure ℚ)) :=
  groupCohomology.δ (T.fixedCoefficientSequence_shortExact A) 0 1 rfl

variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

include hp5 hq hqp haddr hA in
/-- 同じ不変剰余類を、標準 H⁰ 同型で通常の H⁰ の元にする。 -/
def ResidualCyclicStage.fixedCosetH0
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :=
  (groupCohomology.H0Iso (T.fixedQuotientCoefficient A)).inv
    (T.fixedCosetInvariant hp5 hq hqp haddr A hA x)

/-- 実際の連結準同型の像は、以前構成した同じ固定係数 H¹ 類そのもの。 -/
theorem ResidualCyclicStage.fixedCoset_connecting
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.fixedConnecting A (T.fixedCosetH0 hp5 hq hqp haddr A hA x) =
      T.fixedInertiaH1Class hp5 hq hqp haddr A hA x := by
  let f : (inertiaSubgroupIn A ℚ) → T.inertiaFixedUpperQuotient A :=
    TrivialCharacterH1.cocycle (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x)
  have hf : (T.fixedCoefficientInclusion A).hom ∘ f =
      groupCohomology.d₀₁ (T.fullInertiaCoefficient A) ((QuotientAddGroup.mk' T.upperStage) x) := by
    funext σ
    exact T.fixedCocycle_include_value hp5 hq hqp haddr A hA x σ
  exact groupCohomology.δ₀_apply (T.fixedCoefficientSequence_shortExact A)
    (T.fixedCosetInvariant hp5 hq hqp haddr A hA x)
    ((QuotientAddGroup.mk' T.upperStage) x) rfl f hf

end
end DkMath.FLT.Frey.Source
