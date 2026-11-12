/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedConnectingKernel

#print "file: DkMath.FLT.FreyConnectingKernelPrimeOrder"

/-!
# 同じ不変剰余類と実際の係数核の厳密位数 p

元の p•y∈T を使い、同じ剰余類、H⁰ 元、係数核の元とその巡回部分群を保持する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ点の Q での商類は、元の前像条件から p で消える。 -/
theorem NarrowAbsorptionObstruction.pointClass_killed
    (h : S.NarrowAbsorptionObstruction L T q A τ y) :
    p • (QuotientAddGroup.mk' T.upperStage)
      (⟨y, h.killed⟩ : Torsion S.rationalCurve (p ^ (n + 1 + 1))) = 0 := by
  rw [← map_nsmul]
  exact (QuotientAddGroup.eq_zero_iff (N := T.upperStage) _).mpr h.preimage

/-- 同じ Q/F の不変剰余類も p で消える。 -/
theorem NarrowAbsorptionObstruction.fixedCoset_killed
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    p • (T.fixedCosetInvariant hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x).val = 0 := by
  change p • (T.fixedCoefficientProjection A) ((QuotientAddGroup.mk' T.upperStage) _) = 0
  exact (map_nsmul (T.fixedCoefficientProjection A).hom p _).symm.trans
    ((congrArg (T.fixedCoefficientProjection A) h.pointClass_killed).trans (map_zero _))

/-- 元の同じ不変剰余類自体の厳密位数は p。 -/
theorem NarrowAbsorptionObstruction.fixedCoset_order_eq_prime
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    addOrderOf (T.fixedCosetInvariant hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = p := by
  apply addOrderOf_eq_prime_iff.mpr
  constructor
  · apply Subtype.ext
    exact h.fixedCoset_killed hp5
  · intro hz
    exact h.fixedCoset_ne_zero hp5 (congrArg Subtype.val hz)

/-- 標準 H⁰ 同型で写した同じ H⁰ 元も厳密位数 p。 -/
theorem NarrowAbsorptionObstruction.fixedCosetH0_order_eq_prime
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    addOrderOf (T.fixedCosetH0 hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = p := by
  exact ((CategoryTheory.Iso.toLinearEquiv (groupCohomology.H0Iso (T.fixedQuotientCoefficient A))).symm.toAddEquiv.addOrderOf_eq
    (T.fixedCosetInvariant hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩)).trans
      (h.fixedCoset_order_eq_prime hp5)

end

section KernelElement
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 同じ不変剰余類を、構成済みの同型で元の実際の係数核へ写す。 -/
noncomputable def ResidualCyclicStage.fixedCosetKernelElement
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) : T.fixedH1CoefficientKernel A :=
  T.invariantConnectingKernelEquiv A (T.fixedCosetInvariant hp5 hq hqp haddr A hA x)

/-- この同じ核元の値は、以前の同じ慣性 H¹ 類である。 -/
theorem ResidualCyclicStage.fixedCosetKernelElement_val
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x).val =
      T.fixedInertiaH1Class hp5 hq hqp haddr A hA x :=
  T.fixedCoset_connecting hp5 hq hqp haddr A hA x
end KernelElement

noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ実際の係数核の元自身も、同型によって厳密位数 p を持つ。 -/
theorem NarrowAbsorptionObstruction.fixedKernel_order_eq_prime
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    addOrderOf (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = p := by
  exact ((T.invariantConnectingKernelEquiv A).toAddEquiv.addOrderOf_eq
    (T.fixedCosetInvariant hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩)).trans
      (h.fixedCoset_order_eq_prime hp5)

/-- 同じ核元が生成する実際の巡回部分群の濃度は p。核全体の濃度は主張しない。 -/
theorem NarrowAbsorptionObstruction.fixedKernel_cyclic_card
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    Nat.card (AddSubgroup.zmultiples
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x)) = p := by
  exact (Nat.card_zmultiples _).trans (h.fixedKernel_order_eq_prime hp5)

end
end DkMath.FLT.Frey.Source
