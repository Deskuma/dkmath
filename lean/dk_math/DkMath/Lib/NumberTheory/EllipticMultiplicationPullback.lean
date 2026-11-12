/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
Definitions/Def_EllipticCurve_FunctionFieldPullback.lean.
Upstream blob: ce8783a9e9613db1c4c0323ce93fb0d89917ee65
Generic-point argument also adapted from
P2M/Sol/S_WeierstrassCurve_Affine_zsmul_genericPoint_good.lean
(blob 30497c5e52c4e9998217349ad7763aa4adb60a85).
Modified for DkMath: actual guarded natural-number pullback; textbook APIs and existing geometry.
-/

import DkMath.Lib.NumberTheory.EllipticFunctionFieldNegation
import DkMath.Lib.NumberTheory.EllipticMultiplicationSurjective

#print "file: DkMath.Lib.NumberTheory.EllipticMultiplicationPullback"

/-!
# 非零倍写像の実際の関数体引き戻し

一般点γのn倍が零または定数点なら、γを任意の定数点Sで移動して比較するとnS=0が全点で成立する。
既に証明した倍写像の全射性と非零点の存在がこれを排除する。
従って座標代入は単射となり、分母を壊さず関数体へ延長できる。
n≠0を引数に保持し、悪い指数で恒等写像へ置き換える定義は採用しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticMultiplicationPullback : DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- 非零倍写像は全点を零にできない。全射性と実際の非零2-torsion点を使う。 -/
theorem not_forall_nsmul_eq_zero (n : ℕ) (hn : n ≠ 0) :
    ¬ ∀ S : (E⁄(AlgebraicClosure K)).Point, n • S = 0 := by
  classical
  intro hall
  obtain ⟨T, hT⟩ := exists_nonzero_torsion_of_one_lt E 2 (by decide)
  obtain ⟨Q, hQ⟩ := multiplication_surjective E n hn T.val
  exact hT (Subtype.ext (hQ.symm.trans (hall Q)))

/-- 一般点の非零倍はOではない。全ての定数平行移動を作用させて矛盾を作る。 -/
theorem generic_nsmul_ne_zero (n : ℕ) (hn : n ≠ 0) :
    n • genericPoint E (AlgebraicClosure K) ≠ 0 := by
  classical
  intro h0
  apply not_forall_nsmul_eq_zero E n hn
  intro S
  have h := congrArg (Point.map (transPull E (AlgebraicClosure K) S)) h0
  rw [map_nsmul, map_transPull_genericPoint, map_zero, smul_add, h0, zero_add, ← map_nsmul] at h
  exact Point.map_injective _ (h.trans (map_zero _).symm)

/-- 一般点の非零倍は定数点でもない。分数体への延長を可能にする幾何学的な単射性条件。 -/
theorem generic_nsmul_ne_baseChange (n : ℕ) (hn : n ≠ 0)
    (P : (E⁄(AlgebraicClosure K)).Point) :
    n • genericPoint E (AlgebraicClosure K) ≠ Point.baseChange (AlgebraicClosure K) _ P := by
  classical
  intro hP
  apply not_forall_nsmul_eq_zero E n hn
  intro S
  have h := congrArg (Point.map (transPull E (AlgebraicClosure K) S)) hP
  rw [map_nsmul, map_transPull_genericPoint, Point.map_baseChange, smul_add, hP,
    ← map_nsmul, add_eq_left] at h
  exact Point.map_injective _ (h.trans (map_zero _).symm)

/-- n倍一般点への座標代入は単射である。生成元の選択や次数公式はまだ不要。 -/
theorem multiplicationHom_injective (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (pointHom (n • genericPoint E (AlgebraicClosure K)) (generic_nsmul_ne_zero E n hn)) := by
  classical
  exact pointHom_injective_of_ne_baseChange _ _ (generic_nsmul_ne_baseChange E n hn)

/-- 同じ曲線の非零倍写像[n]の引き戻し。必ずn倍一般点への代入から構成する。 -/
noncomputable def multiplicationPull (n : ℕ) (hn : n ≠ 0) :
    (E.toAffine⁄(AlgebraicClosure K)).FunctionField →ₐ[AlgebraicClosure K]
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField :=
  pointPull _ (generic_nsmul_ne_zero E n hn) (multiplicationHom_injective E n hn)

/-- 引き戻しを座標環に制限すると、n倍一般点での評価に戻る。 -/
theorem multiplicationPull_algebraMap (n : ℕ) (hn : n ≠ 0)
    (g : (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing) :
    multiplicationPull E n hn (algebraMap _ _ g) =
      pointHom (n • genericPoint E (AlgebraicClosure K)) (generic_nsmul_ne_zero E n hn) g :=
  pointPull_algebraMap _ _ _ g

/-- x座標への引き戻しは、同じn倍点のx座標である。 -/
theorem multiplicationPull_genericX (n : ℕ) (hn : n ≠ 0) :
    multiplicationPull E n hn (genericX E (AlgebraicClosure K)) =
      (n • genericPoint E (AlgebraicClosure K)).xc := by
  rw [genericX, multiplicationPull_algebraMap, pointHom_mk_C_X]

/-- y座標への引き戻しも、同じn倍点のy座標である。 -/
theorem multiplicationPull_genericY (n : ℕ) (hn : n ≠ 0) :
    multiplicationPull E n hn (genericY E (AlgebraicClosure K)) =
      (n • genericPoint E (AlgebraicClosure K)).yc := by
  rw [genericY, multiplicationPull_algebraMap, pointHom_mk_Y]

/-- 一般点への作用で、構成した引き戻しが実際の倍写像と一致することを固定する。 -/
theorem map_multiplicationPull_genericPoint (n : ℕ) (hn : n ≠ 0) :
    Point.map (multiplicationPull E n hn) (genericPoint E (AlgebraicClosure K)) =
      n • genericPoint E (AlgebraicClosure K) := map_pointPull_genericPoint _ _ _

/-- 倍写像の引き戻しは体の単射な準同型である。 -/
theorem multiplicationPull_injective (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (multiplicationPull E n hn) := (multiplicationPull E n hn).injective

open Classical in
/-- n-torsionによる移動は倍写像の像の全関数を固定する。[n](γ+S)=[n]γを座標代入へ戻す。 -/
theorem transEquiv_multiplicationPull (n : ℕ) (hn : n ≠ 0)
    (S : (E⁄(AlgebraicClosure K)).Point) (hS : n • S = 0)
    (g : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) :
    transEquiv E (AlgebraicClosure K) S (multiplicationPull E n hn g) = multiplicationPull E n hn g := by
  rw [transEquiv_apply, ← AlgHom.comp_apply]
  congr 1
  apply functionField_algHom_ext
  have hP : Point.map (transPull E (AlgebraicClosure K) S)
      (n • genericPoint E (AlgebraicClosure K)) = n • genericPoint E (AlgebraicClosure K) := by
    rw [map_nsmul, map_transPull_genericPoint, smul_add, ← map_nsmul, hS, map_zero, add_zero]
  have hres : (multiplicationPull E n hn).toRingHom.comp
      (algebraMap (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing
        (E.toAffine⁄(AlgebraicClosure K)).FunctionField) =
      (pointHom (n • genericPoint E (AlgebraicClosure K)) (generic_nsmul_ne_zero E n hn)).toRingHom :=
    RingHom.ext (multiplicationPull_algebraMap E n hn)
  rw [AlgHom.comp_toRingHom, RingHom.comp_assoc]
  change (transPull E (AlgebraicClosure K) S).toRingHom.comp
    ((multiplicationPull E n hn).toRingHom.comp
      (algebraMap (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing
        (E.toAffine⁄(AlgebraicClosure K)).FunctionField)) =
    (multiplicationPull E n hn).toRingHom.comp
      (algebraMap (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing
        (E.toAffine⁄(AlgebraicClosure K)).FunctionField)
  rw [hres]
  change ((transPull E (AlgebraicClosure K) S).comp
    (pointHom (n • genericPoint E (AlgebraicClosure K)) (generic_nsmul_ne_zero E n hn))).toRingHom = _
  exact congrArg AlgHom.toRingHom
    ((transPull_comp_pointHom E (AlgebraicClosure K) S _ _
      (by rw [hP]; exact generic_nsmul_ne_zero E n hn)).trans (pointHom_congr hP _ _))

omit [CharZero K] in
/-- 反転でn倍一般点も負の点へ移る。 -/
theorem map_negEquiv_nsmul_genericPoint (n : ℕ) :
    Point.map (negEquiv E (AlgebraicClosure K) : _ →ₐ[AlgebraicClosure K] _)
      (n • genericPoint E (AlgebraicClosure K)) = -(n • genericPoint E (AlgebraicClosure K)) := by
  rw [map_nsmul, map_negEquiv_genericPoint, smul_neg]

/-- 反転は倍写像のy座標をnegYへ移す。次数評価で必要な反転の情報を保持する。 -/
theorem negEquiv_multiplicationPull_genericY (n : ℕ) (hn : n ≠ 0) :
    negEquiv E (AlgebraicClosure K) (multiplicationPull E n hn (genericY E (AlgebraicClosure K))) =
      (E⁄(E.toAffine⁄(AlgebraicClosure K)).FunctionField).negY
        (n • genericPoint E (AlgebraicClosure K)).xc (n • genericPoint E (AlgebraicClosure K)).yc := by
  rw [multiplicationPull_genericY, ← AlgEquiv.coe_toAlgHom, ← point_yc_map (W := E) (K := AlgebraicClosure K),
    map_negEquiv_nsmul_genericPoint]
  conv_lhs => rw [Point.eq_some_xc_yc (generic_nsmul_ne_zero E n hn), Point.neg_some, Point.yc_some]

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
