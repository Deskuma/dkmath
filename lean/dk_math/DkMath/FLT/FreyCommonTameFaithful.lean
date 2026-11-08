/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelFiniteDetector

#print "file: DkMath.FLT.FreyCommonTameFaithful"

/-!
# 実際の共通馴分岐商の忠実な値写像と可換群構造

元の群商 H=J/ker Ψ と群演算を保持する。別の可換群へ取り替えず、
元の全指標値への写像の単射性から同じ H の可換性を証明する。
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

/-- 元の共通商から、元の全指標値への写像は単射。 -/
theorem ResidualCyclicStage.fixedKernelCommonTameValues_injective :
    Function.Injective (T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA) := by
  intro x y he
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
  apply QuotientGroup.eq.mpr
  change (T.fixedKernelTameFamily A hp5 hq hqp haddr hA) (t⁻¹ * s) = 1
  change (T.fixedKernelTameFamily A hp5 hq hqp haddr hA) t =
    (T.fixedKernelTameFamily A hp5 hq hqp haddr hA) s at he
  rw [map_mul, map_inv, he, inv_mul_cancel]

/-- 元の同じ H の群演算は可換である。 -/
theorem ResidualCyclicStage.fixedKernelCommonTame_mul_comm
    (x y : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) : x * y = y * x := by
  apply T.fixedKernelCommonTameValues_injective A hp5 hq hqp haddr hA
  rw [map_mul, map_mul, mul_comm]

/-- 元の Group 構造をそのまま拡張した、同じ H の可換群構造。 -/
@[instance_reducible]
def ResidualCyclicStage.fixedKernelCommonTameCommGroup :
    CommGroup (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) :=
  { (inferInstance : Group (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA)) with
    mul_comm := T.fixedKernelCommonTame_mul_comm A hp5 hq hqp haddr hA }

/-- 元の I から同じ J と同じ共通商 H への合成。 -/
def ResidualCyclicStage.fixedKernelCommonProjection :
    inertiaSubgroupIn A ℚ →* T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA :=
  (QuotientGroup.mk' (T.fixedKernelTameFamily A hp5 hq hqp haddr hA).ker).comp
    (QuotientGroup.mk' (wildInertiaSubgroup A))

/-- 元の慣性群から同じ H への合成は全射。 -/
theorem ResidualCyclicStage.fixedKernelCommonProjection_surjective :
    Function.Surjective (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA) :=
  QuotientGroup.mk_surjective.comp QuotientGroup.mk_surjective

/-- 同じ I の元の共通商像で、元の同じ核指標値を回収する。 -/
theorem ResidualCyclicStage.fixedKernelCommonProjection_value
    (σ : inertiaSubgroupIn A ℚ) (k : T.fixedH1CoefficientKernel A) :
    T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA
      (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA σ) k = T.fixedKernelCharacter A k σ := rfl

end
end DkMath.FLT.Frey.Source
