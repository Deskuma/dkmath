/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.ValuationWildRigidity
import DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

#print "file: DkMath.Lib.NumberTheory.EllipticWildRigidity"

/-!
# 同じ幾何点の周期を座標の野生剛性へ渡す

曲線の点の固定性を同じ座標に戻す。有限性や pro-q 性の provider は要求しない。
周期が q と互いに素であることは利用側で証明する。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open ValuationInertia ValuationWildRigidity
open scoped WeierstrassCurve.Affine
variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-- 同じ野生自己同型の q と互いに素な周期を持つ幾何点は、その自己同型に固定される。 -/
theorem pointAction_fixed_of_wild_coprime_period
    (A : ValuationSubring (AlgebraicClosure K)) {q m : ℕ} (hq : q.Prime) (hA : LiesOverPrime A q)
    (σ : Field.absoluteGaloisGroup K)
    (hwild : ∀ z : AlgebraicClosure K, z ≠ 0 → σ.toAlgHom z * z⁻¹ - 1 ∈ A.nonunits)
    (hm : m.Coprime q) (P : Points E) (hP : pointAction E (σ ^ m) P = P) :
    pointAction E σ P = P := by
  cases P with
  | zero => rfl
  | some x y h =>
    change WeierstrassCurve.Affine.Point.some ((σ ^ m).toAlgHom x) ((σ ^ m).toAlgHom y) _ =
      WeierstrassCurve.Affine.Point.some x y h at hP
    have hxy : (σ ^ m).toAlgHom x = x ∧ (σ ^ m).toAlgHom y = y := by
      simpa only [WeierstrassCurve.Affine.Point.some.injEq] using hP
    obtain ⟨hx, hy⟩ := hxy
    change WeierstrassCurve.Affine.Point.some (σ.toAlgHom x) (σ.toAlgHom y) _ =
      WeierstrassCurve.Affine.Point.some x y h
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨fixed_of_coprime_period A hq hA hwild hm hx,
      fixed_of_coprime_period A hq hA hwild hm hy⟩

/-- 上の座標の固定性を、同じ実際の捩れ表現へ戻す。 -/
theorem representation_fixed_of_wild_coprime_period
    (A : ValuationSubring (AlgebraicClosure K)) {q m N : ℕ} (hq : q.Prime) (hA : LiesOverPrime A q)
    (σ : Field.absoluteGaloisGroup K)
    (hwild : ∀ z : AlgebraicClosure K, z ≠ 0 → σ.toAlgHom z * z⁻¹ - 1 ∈ A.nonunits)
    (hm : m.Coprime q) (x : Torsion E N) (hx : representation E N (σ ^ m) x = x) :
    representation E N σ x = x := by
  apply Subtype.ext
  exact pointAction_fixed_of_wild_coprime_period E A hq hA σ hwild hm x.val
    (congrArg Subtype.val hx)

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
