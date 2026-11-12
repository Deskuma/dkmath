/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyGlobalInertiaRestriction
import DkMath.Lib.NumberTheory.ValuationInertiaNormalizer

#print "file: DkMath.FLT.FreyDecompositionFixedCoefficient"

/-! # 分解群は同じ局所固定係数 F を保存する
全 Galois 群による保存を仮定せず、実際の慣性正規化を内部証明に使う。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

/-- 分解群の元の作用は、元の同じ慣性固定部分群を保つ。 -/
theorem ResidualCyclicStage.decomposition_preserves_fixed (A : ValuationSubring (AlgebraicClosure ℚ))
    (σ : A.decompositionSubgroup ℚ) (z : T.inertiaFixedUpperQuotient A) :
    T.upperQuotientAction σ.val z.val ∈ T.inertiaFixedUpperQuotient A := by
  intro τ hτ
  have ht := decomposition_inv_conj_mem_inertia A σ.val τ σ.property hτ
  have hf := z.property (σ.val⁻¹ * τ * σ.val) ht
  have he : τ * σ.val = σ.val * (σ.val⁻¹ * τ * σ.val) := by group
  change T.upperQuotientAction τ (T.upperQuotientAction σ.val z.val) = T.upperQuotientAction σ.val z.val
  have hm (a b : Field.absoluteGaloisGroup ℚ) (v : T.upperQuotient) :
      T.upperQuotientAction (a * b) v = T.upperQuotientAction a (T.upperQuotientAction b v) :=
    congrArg (fun f : AddMonoid.End T.upperQuotient => f v) (T.upperQuotientAction.map_mul a b)
  calc T.upperQuotientAction τ (T.upperQuotientAction σ.val z.val)
      = T.upperQuotientAction (τ * σ.val) z.val := (hm τ σ.val z.val).symm
    _ = T.upperQuotientAction (σ.val * (σ.val⁻¹ * τ * σ.val)) z.val :=
      congrArg (fun g => T.upperQuotientAction g z.val) he
    _ = T.upperQuotientAction σ.val (T.upperQuotientAction (σ.val⁻¹ * τ * σ.val) z.val) :=
      hm σ.val _ z.val
    _ = T.upperQuotientAction σ.val z.val := congrArg (T.upperQuotientAction σ.val) hf

/-- 元の F 上の実際の分解群作用。 -/
def ResidualCyclicStage.fixedDecompositionAction (A : ValuationSubring (AlgebraicClosure ℚ)) :
    A.decompositionSubgroup ℚ →* AddMonoid.End (T.inertiaFixedUpperQuotient A) where
  toFun σ :=
    { toFun := fun z => ⟨T.upperQuotientAction σ.val z.val, T.decomposition_preserves_fixed A σ z⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun z w => Subtype.ext (map_add _ _ _) }
  map_one' := by
    apply AddMonoidHom.ext
    intro z
    apply Subtype.ext
    exact congrArg (fun f : AddMonoid.End T.upperQuotient => f z.val) T.upperQuotientAction.map_one
  map_mul' σ τ := by
    apply AddMonoidHom.ext
    intro z
    apply Subtype.ext
    exact congrArg (fun f : AddMonoid.End T.upperQuotient => f z.val)
      (T.upperQuotientAction.map_mul σ.val τ.val)

/-- 同じ F と同じ作用による分解群の整数線形表現。 -/
def ResidualCyclicStage.fixedDecompositionCoefficient (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Rep ℤ (A.decompositionSubgroup ℚ) := Rep.of
  { toFun := fun σ => (T.fixedDecompositionAction A σ).toIntLinearMap
    map_one' := by
      apply LinearMap.ext
      intro z
      exact congrArg (fun f : AddMonoid.End (T.inertiaFixedUpperQuotient A) => f z)
        (T.fixedDecompositionAction A).map_one
    map_mul' := fun σ τ => by
      apply LinearMap.ext
      intro z
      exact congrArg (fun f : AddMonoid.End (T.inertiaFixedUpperQuotient A) => f z)
        ((T.fixedDecompositionAction A).map_mul σ τ) }

/-- 同じ F の分解群作用は単射である。 -/
theorem ResidualCyclicStage.fixedDecompositionAction_injective (A : ValuationSubring (AlgebraicClosure ℚ))
    (σ : A.decompositionSubgroup ℚ) : Function.Injective (T.fixedDecompositionAction A σ) := by
  intro z w he
  have hh := congrArg (T.fixedDecompositionAction A σ⁻¹) he
  change ((T.fixedDecompositionAction A σ⁻¹) * (T.fixedDecompositionAction A σ)) z =
    ((T.fixedDecompositionAction A σ⁻¹) * (T.fixedDecompositionAction A σ)) w at hh
  rw [← map_mul, inv_mul_cancel, map_one] at hh
  exact hh
end
end DkMath.FLT.Frey.Source

