/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyStageUpperQuotientCard
import DkMath.FLT.FreyInertiaDifferenceCharacter
import DkMath.Lib.NumberTheory.EllipticTorsionContinuity
import Mathlib.Topology.Algebra.Group.Quotient

#print "file: DkMath.FLT.FreyStageUpperQuotientTopology"

/-!
# 同じ有限商・Galois 作用・慣性差分の連続性

元の Krull 位相、慣性の部分群位相、標準商位相を保つ。
連続性や開核を新しい provider として要求しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 離散な有限捩れ群の標準商位相は離散。別の位相へ取り替えない。 -/
instance ResidualCyclicStage.upperQuotientDiscreteTopology (T : S.ResidualCyclicStage L n) :
    DiscreteTopology T.upperQuotient := QuotientAddGroup.discreteTopology (isOpen_discrete _)

/-- 同じ実際の商作用の各軌道写像は Krull 位相から連続。 -/
theorem ResidualCyclicStage.upperQuotient_orbit_continuous (T : S.ResidualCyclicStage L n)
    (z : T.upperQuotient) : Continuous (fun σ : Field.absoluteGaloisGroup ℚ => T.upperQuotientAction σ z) := by
  refine QuotientAddGroup.induction_on z ?_
  intro x
  change Continuous (fun σ : Field.absoluteGaloisGroup ℚ =>
    (QuotientAddGroup.mk' T.upperStage) (representation S.rationalCurve (p ^ (n + 1 + 1)) σ x))
  exact (continuous_of_discreteTopology : Continuous (QuotientAddGroup.mk' T.upperStage)).comp
    (representation_orbit_continuous S.rationalCurve _ x)

/-- Galois 元と同じ商元の両変数について連続。 -/
theorem ResidualCyclicStage.upperQuotient_action_continuous (T : S.ResidualCyclicStage L n) :
    Continuous (fun z : Field.absoluteGaloisGroup ℚ × T.upperQuotient => T.upperQuotientAction z.1 z.2) := by
  rw [continuous_prod_of_discrete_right]
  intro z
  exact T.upperQuotient_orbit_continuous z

end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)
    (n : ℕ) (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 同じ有限点を基点とする実際の慣性差分準同型は連続。 -/
theorem inertiaDifferenceCharacter_continuous (x : Torsion S.rationalCurve (p ^ (n + 1))) :
    Continuous (S.inertiaDifferenceCharacter n hp5 hq hqp haddr A hA x) := by
  change Continuous (fun σ : inertiaSubgroupIn A ℚ =>
    Multiplicative.ofAdd (representation S.rationalCurve (p ^ (n + 1)) σ.val x - x))
  exact continuous_ofAdd.comp
    (((representation_orbit_continuous S.rationalCurve _ x).comp (@continuous_subtype_val (Field.absoluteGaloisGroup ℚ) _ (fun σ => σ ∈ inertiaSubgroupIn A ℚ))).sub continuous_const)

end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 元の同じ有限商への慣性差分準同型も連続。 -/
theorem ResidualCyclicStage.inertiaQuotientDifferenceCharacter_continuous
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    Continuous (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x) := by
  exact (continuous_of_discreteTopology : Continuous (QuotientAddGroup.mk' T.upperStage).toMultiplicative).comp
    (S.inertiaDifferenceCharacter_continuous (n + 1) hp5 hq hqp haddr A hA x)

/-- 同じ準同型の実際の核は開かつ閉。 -/
theorem ResidualCyclicStage.inertiaQuotientDifferenceCharacter_kernel_isClopen
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    IsClopen ((T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x).ker :
      Set (inertiaSubgroupIn A ℚ)) := by
  have hc := T.inertiaQuotientDifferenceCharacter_continuous hp5 hq hqp haddr A hA x
  change IsClopen ((T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x) ⁻¹' {1})
  exact ⟨isClosed_singleton.preimage hc, (isOpen_discrete {1}).preimage hc⟩

/-- この差分は同じ商元を基点とする作用差そのもの。非零 H¹ 類の主張ではない。 -/
theorem ResidualCyclicStage.inertiaQuotientDifferenceCharacter_coboundary
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ : inertiaSubgroupIn A ℚ) :
    Multiplicative.toAdd (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x σ) =
      T.upperQuotientAction σ.val ((QuotientAddGroup.mk' T.upperStage) x) -
        (QuotientAddGroup.mk' T.upperStage) x := by
  rw [T.inertiaQuotientDifferenceCharacter_apply hp5 hq hqp haddr A hA x σ, map_sub]
  rfl

end
end DkMath.FLT.Frey.Source
