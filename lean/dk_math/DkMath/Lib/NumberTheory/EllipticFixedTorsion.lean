/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
import DkMath.Lib.RepresentationTheory.FixedCofixed
import Mathlib.FieldTheory.Galois.Infinite

#print "file: DkMath.Lib.NumberTheory.EllipticFixedTorsion"

/-!
# ガロア固定点を有理点へ戻す

標数0の体Kでは、代数閉包の絶対ガロア群の固定体はKである。
有限点の二つの座標にこの定理を適用し、元の曲線上の点へ降下させる。
非特異性とn倍で消える条件も単射な基底変換で引き戻すので、単なる座標の存在で
止まらず、実際のK有理n-torsion点が得られる。

従って「固定n-torsionが零だけ」と「K有理n-torsionが零だけ」は同値である。
Frey曲線について後者を無条件に証明する算術はこの一般的な降下とは区別する。
参考: anthropics/fermats-last-theorem の
`S_FreyPackage_frey_torsion_fixed_eq_zero`。ここではDkMathの実際の点の作用を使い、
固定体と座標の議論を独立に証明する。
-/

namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.RepresentationTheory
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K)

omit [CharZero K] in
/-- 点の基底変換を、元の体上の点群を定義域とする加法準同型として固定する。 -/
noncomputable def baseChangePointHom [DecidableEq K] : E.toAffine.Point →+ Points E := by
  classical
  exact Point.baseChange (W' := E.toAffine) K (AlgebraicClosure K)

omit [CharZero K] in
/-- 基底変換は実際の点を区別する。 -/
theorem baseChangePoint_injective : Function.Injective (baseChangePoint E) := by
  classical
  exact Point.map_injective (W' := E.toAffine) (Algebra.ofId K (AlgebraicClosure K))

/-- 絶対ガロア群が固定する幾何学的な点は、元の体上の点の基底変換である。 -/
theorem exists_baseChangePoint_of_fixed (P : Points E)
    (hP : ∀ σ, pointAction E σ P = P) :
    ∃ Q : E.toAffine.Point, baseChangePoint E Q = P := by
  classical
  rcases P with _ | ⟨x, y, hxy⟩
  · exact ⟨0, rfl⟩
  · have hx : ∀ σ : Field.absoluteGaloisGroup K, σ.toAlgHom x = x := by
      intro σ
      exact (Point.some.inj (hP σ)).1
    have hy : ∀ σ : Field.absoluteGaloisGroup K, σ.toAlgHom y = y := by
      intro σ
      exact (Point.some.inj (hP σ)).2
    obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hx
    obtain ⟨b, hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed y).mpr hy
    have hab : E.toAffine.Nonsingular a b := by
      apply (E.toAffine.baseChange_nonsingular
        (f := Algebra.ofId K (AlgebraicClosure K))
        (algebraMap K (AlgebraicClosure K)).injective a b).mp
      simpa only [Algebra.ofId_apply, ha, hb] using hxy
    refine ⟨Point.some a b hab, ?_⟩
    change Point.some _ _ _ = Point.some x y hxy
    simpa only [Point.some.injEq, Algebra.ofId_apply] using And.intro ha hb

/-- 固定されるn-torsion点は、同じnで消えるK有理点へ降下する。 -/
theorem exists_rational_torsion_of_fixed [DecidableEq K] (n : ℕ) (P : Torsion E n)
    (hP : ∀ σ, representation E n σ P = P) :
    ∃ Q : E.toAffine.Point, n • Q = 0 ∧ baseChangePoint E Q = P.val := by
  classical
  obtain ⟨Q, hQ⟩ := exists_baseChangePoint_of_fixed E P.val
    (fun σ => congrArg Subtype.val (hP σ))
  refine ⟨Q, ?_, hQ⟩
  apply baseChangePoint_injective E
  change baseChangePointHom E (n • Q) = baseChangePointHom E 0
  rw [map_nsmul, map_zero]
  change n • baseChangePoint E Q = 0
  rw [hQ]
  exact P.property

/-- ガロア固定torsionの不存在と、有理torsionの不存在は同値。
右辺の算術的証明を仮定から隠さず、曲線と指数を保持する。 -/
theorem noNonzeroFixed_iff_rational_torsion [DecidableEq K] (n : ℕ) :
    NoNonzeroFixed (representation E n) ↔
      ∀ Q : E.toAffine.Point, n • Q = 0 → Q = 0 := by
  classical
  constructor
  · intro h Q hQ
    let P : Torsion E n := ⟨baseChangePoint E Q, by
      change n • baseChangePointHom E Q = 0
      rw [← map_nsmul, hQ, map_zero]⟩
    have hP : P = 0 := h P (fun σ => Subtype.ext (pointAction_baseChange E σ Q))
    apply baseChangePoint_injective E
    exact congrArg Subtype.val hP
  · intro h P hP
    obtain ⟨Q, hQ, heq⟩ := exists_rational_torsion_of_fixed E n P hP
    apply Subtype.ext
    rw [← heq, h Q hQ]
    rfl

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
