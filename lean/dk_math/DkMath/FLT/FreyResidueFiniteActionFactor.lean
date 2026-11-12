/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteFrobeniusImage

#print "file: DkMath.FLT.FreyResidueFiniteActionFactor"

/-! # 実際の剰余作用と有限 K 作用の因子化
同じ付値環の剰余自己同型作用を使う。有限剰余拡大への因子化や Frobenius 生成性はここでは主張しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section

/-- 同じ付値環の剰余体上の実際の分解群作用。 -/
def residueFieldAction (A : ValuationSubring (AlgebraicClosure ℚ)) :
    A.decompositionSubgroup ℚ →* RingAut (IsLocalRing.ResidueField A) :=
  MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ) (IsLocalRing.ResidueField A)

/-- この作用の核は、定義上、元の慣性群そのものである。 -/
theorem residueFieldAction_ker (A : ValuationSubring (AlgebraicClosure ℚ)) :
    (residueFieldAction A).ker = A.inertiaSubgroup ℚ := rfl

/-- 元の D/I は実際の剰余自己同型群に忠実に作用する。 -/
def residueFieldFaithfulAction (A : ValuationSubring (AlgebraicClosure ℚ)) :
    ((A.decompositionSubgroup ℚ) ⧸ A.inertiaSubgroup ℚ) →* RingAut (IsLocalRing.ResidueField A) :=
  QuotientGroup.lift _ (residueFieldAction A) (le_of_eq (residueFieldAction_ker A).symm)

/-- 忠実性は慣性核を割ったことから従う。 -/
theorem residueFieldFaithfulAction_injective (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Function.Injective (residueFieldFaithfulAction A) := by
  exact QuotientGroup.kerLift_injective (residueFieldAction A)

/-- 実際の Frobenius 持ち上げは、この同じ剰余体上で q 乗として作用する。 -/
theorem residueFieldAction_frobenius (A : ValuationSubring (AlgebraicClosure ℚ))
    {q : ℕ} (φ : A.decompositionSubgroup ℚ)
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (x : IsLocalRing.ResidueField A) :
    (residueFieldAction A φ) x = x ^ q := by
  change φ • x = x ^ q
  have he : (⟨φ.val, hφ.mem_decompositionSubgroup⟩ : A.decompositionSubgroup ℚ) = φ :=
    Subtype.ext rfl
  rw [← he]
  exact hφ.smul_residue_eq x

variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

/-- 同じ有限 K 作用は、実際の剰余群 D/I を通って因子化する。 -/
def ResidualCyclicStage.finiteResidueProjection :
    ((A.decompositionSubgroup ℚ) ⧸ A.inertiaSubgroup ℚ) →*
      T.finiteDecompositionImage A hp5 hq hqp haddr hA :=
  QuotientGroup.lift _ (T.finiteDecompositionProjection A hp5 hq hqp haddr hA)
    (T.inertia_le_finiteDecompositionProjection_kernel A hp5 hq hqp haddr hA)

/-- 元の D からの有限作用射影は、D/I を経由した射影に等しい。 -/
theorem ResidualCyclicStage.finiteResidueProjection_comp :
    (T.finiteResidueProjection A hp5 hq hqp haddr hA).comp
      (QuotientGroup.mk' (A.inertiaSubgroup ℚ)) =
      T.finiteDecompositionProjection A hp5 hq hqp haddr hA := by
  ext σ
  rfl

/-- この D/I からの射影は、実際の有限作用像へ全射である。 -/
theorem ResidualCyclicStage.finiteResidueProjection_surjective :
    Function.Surjective (T.finiteResidueProjection A hp5 hq hqp haddr hA) := by
  intro z
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective z
  exact ⟨QuotientGroup.mk' (A.inertiaSubgroup ℚ) σ, rfl⟩

end
end DkMath.FLT.Frey.Source
