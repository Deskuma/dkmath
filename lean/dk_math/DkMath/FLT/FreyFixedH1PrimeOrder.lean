/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedH1Connecting

#print "file: DkMath.FLT.FreyFixedH1PrimeOrder"

/-!
# 同じ前像条件から全ての差分値の p 倍零性と類の厳密位数 p へ

一点の値の位数だけでは足りない。p•y∈T と元の安定性から全ての値を p で消し、
既存の非零性と合わせて通常の H¹ 類そのものの厳密位数を確定する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}
    {T : S.ResidualCyclicStage L n} {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 元の前像条件と安定性により、同じ固定係数指標の全ての値は p で消える。 -/
theorem NarrowAbsorptionObstruction.fixed_character_values_killed
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) (σ : inertiaSubgroupIn A ℚ) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    p • Multiplicative.toAdd (T.inertiaFixedDifferenceCharacter hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) A h.lies_over x σ) = 0 := by
  apply Subtype.ext
  change p • Multiplicative.toAdd (T.inertiaQuotientDifferenceCharacter hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩ σ) = 0
  rw [T.inertiaQuotientDifferenceCharacter_apply hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩ σ, ← map_nsmul]
  apply (QuotientAddGroup.eq_zero_iff (N := T.upperStage) _).mpr
  change p • (pointAction S.rationalCurve σ.val y - y) ∈ T.carrier
  rw [nsmul_sub, ← map_nsmul]
  exact T.carrier.sub_mem (T.stable σ.val _ h.preimage) h.preimage

/-- 同じ慣性固定係数類そのものは p で消える。 -/
theorem NarrowAbsorptionObstruction.fixed_inertia_class_killed
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    p • T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x = 0 := by
  let f := T.inertiaFixedDifferenceCharacter hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
  have hc : p • TrivialCharacterH1.cocycle f = 0 := by
    apply groupCohomology.cocycles₁_ext
    intro σ
    exact h.fixed_character_values_killed hp5 σ
  change p • groupCohomology.H1π _ (TrivialCharacterH1.cocycle f) = 0
  rw [← map_nsmul, hc, map_zero]

/-- 同じ馴分岐固定係数類も、全ての同じ値の p 倍零性から p で消える。 -/
theorem NarrowAbsorptionObstruction.fixed_tame_class_killed
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    p • T.fixedTameH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x = 0 := by
  let f := T.fixedTameCharacter hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
  have hc : p • TrivialCharacterH1.cocycle f = 0 := by
    apply groupCohomology.cocycles₁_ext
    intro t
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective t
    exact h.fixed_character_values_killed hp5 σ
  change p • groupCohomology.H1π _ (TrivialCharacterH1.cocycle f) = 0
  rw [← map_nsmul, hc, map_zero]

/-- 同じ二つの通常の H¹ 類は、非零性と全値の零化から厳密位数 p を持つ。 -/
theorem NarrowAbsorptionObstruction.fixed_H1_order_eq_prime
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    addOrderOf (T.fixedTameH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = p ∧
      addOrderOf (T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = p := by
  exact ⟨addOrderOf_eq_prime_iff.mpr ⟨h.fixed_tame_class_killed hp5, (h.fixed_H1_nonzero hp5).1⟩,
    addOrderOf_eq_prime_iff.mpr ⟨h.fixed_inertia_class_killed hp5, (h.fixed_H1_nonzero hp5).2⟩⟩

end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation CyclotomicKernelField CyclotomicKummerWeight ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)

include hline hζ hp5 hclass in
/-- 同じ算術証明書から、実際の inflation・連結像・厳密位数 p と不変持ち上げ障害を出力する。 -/
theorem residual_exists_connecting_prime_order_H1
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
      addOrderOf (T.fixedTameH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = p ∧
      addOrderOf (T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = p ∧
      T.fixedH1Inflation A (T.fixedTameH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) =
        T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x ∧
      T.fixedConnecting A (T.fixedCosetH0 hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) =
        T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x ∧
      (¬ ∃ z : (T.fullInertiaCoefficient A).ρ.invariants,
        T.fixedCoefficientProjection A z.val =
          (T.fixedCosetInvariant hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x).val) ∧
      groupCohomology.map (MonoidHom.id (inertiaSubgroupIn A ℚ)) (T.fixedCoefficientInclusion A) 1
        (T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = 0 := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  exact ⟨n, T, q, A, τ, y, h, (h.fixed_H1_order_eq_prime hp5).1, (h.fixed_H1_order_eq_prime hp5).2,
    T.fixedTameClass_inflation hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩,
    T.fixedCoset_connecting hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩,
    h.no_invariant_lift hp5,
    T.fixedInertiaClass_map_zero hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩⟩

end
end DkMath.FLT.Frey.Source
