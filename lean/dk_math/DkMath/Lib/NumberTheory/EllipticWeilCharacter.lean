/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFunctionEigenvalue
import Mathlib.Algebra.Group.AddChar
import Mathlib.RingTheory.RootsOfUnity.Basic

#print "file: DkMath.Lib.NumberTheory.EllipticWeilCharacter"

/-!
# Weil関数の平行移動固有値から片側の指標へ

NOTE-022の同じ非零関数wを使い、NOTE-024の位数保存を移動比τ*w/wの定数判定へ渡す。
こうして得るc(S,T)は一意であり、非零定数倍で関数を選び直しても変わらない。
合成則と一意性からc(S+R,T)=c(S,T)c(R,T)、nS=Oからc(S,T)^n=1となる。
Tを固定したAddChar E[n] μₙを構成するが、Tに関する加法性・交代性・非退化性は主張しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]

open Classical in
/-- 同じWeil関数の位数保存から、移動の比例定数を一意な係数体の単元として得る。 -/
theorem existsUnique_weilTranslationUnit (n : ℕ) (hn : n ≠ 0) (T S : Torsion E n) :
    ∃! c : (AlgebraicClosure K)ˣ,
      transEquiv E (AlgebraicClosure K) S.val (weilFunction E n hn T.val T.property) =
        algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField
          (c : AlgebraicClosure K) * weilFunction E n hn T.val T.property := by
  apply existsUnique_scalar_of_pointOrder_eq E _ _
    ((transEquiv E (AlgebraicClosure K) S.val).toRingEquiv.map_ne_zero_iff.mpr
      (weilFunction_ne_zero E n hn T.val T.property)) (weilFunction_ne_zero E n hn T.val T.property)
  intro P
  exact pointOrder_transEquiv_weilFunction_of_torsion E n hn T.val T.property P S.val S.property

/-- 実際の移動比から取り出した単元c(S,T)。引数の順は、固定するTを先に置く。 -/
noncomputable def weilTranslationUnit (n : ℕ) (hn : n ≠ 0) (T S : Torsion E n) :
    (AlgebraicClosure K)ˣ := (existsUnique_weilTranslationUnit E n hn T S).exists.choose

open Classical in
/-- 選択した単元は、同じ関数体内の実際の平行移動の固有方程式を満たす。 -/
theorem weilTranslationUnit_spec (n : ℕ) (hn : n ≠ 0) (T S : Torsion E n) :
    transEquiv E (AlgebraicClosure K) S.val (weilFunction E n hn T.val T.property) =
      algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField
        (weilTranslationUnit E n hn T S : AlgebraicClosure K) * weilFunction E n hn T.val T.property :=
  (existsUnique_weilTranslationUnit E n hn T S).exists.choose_spec

open Classical in
/-- 他の単元が同じ固有方程式を満たせば、選択した比例定数と一致する。 -/
theorem weilTranslationUnit_unique (n : ℕ) (hn : n ≠ 0) (T S : Torsion E n)
    (c : (AlgebraicClosure K)ˣ)
    (hc : transEquiv E (AlgebraicClosure K) S.val (weilFunction E n hn T.val T.property) =
      algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField
        (c : AlgebraicClosure K) * weilFunction E n hn T.val T.property) :
    c = weilTranslationUnit E n hn T S :=
  function_scalar_unique E _ (weilFunction_ne_zero E n hn T.val T.property)
    (hc.symm.trans (weilTranslationUnit_spec E n hn T S))

open Classical in
/-- 零点による移動は恒等写像なので、比例定数は1。 -/
theorem weilTranslationUnit_zero (n : ℕ) (hn : n ≠ 0) (T : Torsion E n) :
    weilTranslationUnit E n hn T 0 = 1 := by
  apply Eq.symm
  apply weilTranslationUnit_unique E n hn T 0 1
  change transEquiv E (AlgebraicClosure K) 0 (weilFunction E n hn T.val T.property) = _
  rw [transEquiv_zero]
  simp

/-- 平行移動の合成と、係数体の固定、一意性から左変数の乗法性が従う。 -/
theorem weilTranslationUnit_add (n : ℕ) (hn : n ≠ 0) (T S R : Torsion E n) :
    weilTranslationUnit E n hn T (S + R) =
      weilTranslationUnit E n hn T S * weilTranslationUnit E n hn T R := by
  classical
  apply Eq.symm
  apply weilTranslationUnit_unique E n hn T (S + R) _
  have he : transEquiv E (AlgebraicClosure K) (S + R).val (weilFunction E n hn T.val T.property) =
      transEquiv E (AlgebraicClosure K) S.val
        (transEquiv E (AlgebraicClosure K) R.val (weilFunction E n hn T.val T.property)) :=
    DFunLike.congr_fun (transEquiv_add E (AlgebraicClosure K) S.val R.val) _
  rw [he, weilTranslationUnit_spec E n hn T R, map_mul, AlgEquiv.commutes,
    weilTranslationUnit_spec E n hn T S, Units.val_mul, map_mul]
  ring

/-- 固定したTについて、単元を値に取る加法的指標を構成する。
AddCharは点の加法を単元の乗法へ送るための標準の型である。 -/
noncomputable def weilTranslationUnitChar (n : ℕ) (hn : n ≠ 0) (T : Torsion E n) :
    AddChar (Torsion E n) (AlgebraicClosure K)ˣ where
  toFun := weilTranslationUnit E n hn T
  map_zero_eq_one' := weilTranslationUnit_zero E n hn T
  map_add_eq_mul' := weilTranslationUnit_add E n hn T

/-- 自然数倍の移動は比例定数の自然数冪へ送られる。 -/
theorem weilTranslationUnit_nsmul (n : ℕ) (hn : n ≠ 0) (T S : Torsion E n) (m : ℕ) :
    weilTranslationUnit E n hn T (m • S) = weilTranslationUnit E n hn T S ^ m := by
  induction m with
  | zero => simp only [zero_nsmul, weilTranslationUnit_zero, pow_zero]
  | succ m ih => rw [succ_nsmul, weilTranslationUnit_add, ih, pow_succ]

/-- nS=Oにより、比例定数は実際にn乗根となる。n≠0はWeil関数の構成から保持する。 -/
theorem weilTranslationUnit_pow (n : ℕ) (hn : n ≠ 0) (T S : Torsion E n) :
    weilTranslationUnit E n hn T S ^ n = 1 := by
  have hz : n • S = 0 := by
    apply Subtype.ext
    exact S.property
  rw [← weilTranslationUnit_nsmul, hz, weilTranslationUnit_zero]

/-- μₙに値を制限した片側の指標。右側変数についての双加法性はこの構成には含まれない。 -/
noncomputable def weilTranslationCharacter (n : ℕ) (hn : n ≠ 0) (T : Torsion E n) :
    AddChar (Torsion E n) (rootsOfUnity n (AlgebraicClosure K)) where
  toFun S := ⟨weilTranslationUnit E n hn T S, (mem_rootsOfUnity n _).mpr (weilTranslationUnit_pow E n hn T S)⟩
  map_zero_eq_one' := Subtype.ext (weilTranslationUnit_zero E n hn T)
  map_add_eq_mul' S R := Subtype.ext (weilTranslationUnit_add E n hn T S R)

/-- 指標の値を係数体の単元として見ると、取り出した同じ比例定数である。 -/
theorem weilTranslationCharacter_val (n : ℕ) (hn : n ≠ 0) (T S : Torsion E n) :
    (weilTranslationCharacter E n hn T S).val = weilTranslationUnit E n hn T S := rfl

open Classical in
/-- Weil関数を非零定数倍した固有方程式にも、同じc(S,T)が現れる。 -/
theorem weilTranslationUnit_const_mul_spec (n : ℕ) (hn : n ≠ 0) (T S : Torsion E n)
    (a : (AlgebraicClosure K)ˣ) :
    transEquiv E (AlgebraicClosure K) S.val
      (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (a : AlgebraicClosure K) *
        weilFunction E n hn T.val T.property) =
      algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField
        (weilTranslationUnit E n hn T S : AlgebraicClosure K) *
        (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (a : AlgebraicClosure K) *
          weilFunction E n hn T.val T.property) :=
  transEquiv_const_mul_eigenfunction E S.val _ a _ (weilTranslationUnit_spec E n hn T S)

open Classical in
/-- 非零定数倍した関数に対しても、他の固有値は選択したc(S,T)に一致する。 -/
theorem weilTranslationUnit_const_mul_unique (n : ℕ) (hn : n ≠ 0) (T S : Torsion E n)
    (a c : (AlgebraicClosure K)ˣ)
    (hc : transEquiv E (AlgebraicClosure K) S.val
      (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (a : AlgebraicClosure K) *
        weilFunction E n hn T.val T.property) =
      algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (c : AlgebraicClosure K) *
        (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (a : AlgebraicClosure K) *
          weilFunction E n hn T.val T.property)) : c = weilTranslationUnit E n hn T S :=
  function_scalar_unique E _
    (mul_ne_zero ((map_ne_zero _).mpr a.ne_zero) (weilFunction_ne_zero E n hn T.val T.property))
    (hc.symm.trans (weilTranslationUnit_const_mul_spec E n hn T S a))

/-- 分子と分母を別々の非零定数倍で選び直した商は、a/b倍の同じWeil関数となる。 -/
theorem weilNumerator_rescale_div (n : ℕ) (hn : n ≠ 0) (T : Torsion E n)
    (a b : (AlgebraicClosure K)ˣ) :
    (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (a : AlgebraicClosure K) *
        algebraMap (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing (E.toAffine⁄(AlgebraicClosure K)).FunctionField
          (weilNumerator E n hn T.val T.property)) /
      (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (b : AlgebraicClosure K) *
        algebraMap (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing (E.toAffine⁄(AlgebraicClosure K)).FunctionField
          (weilNumerator E n hn 0 (smul_zero n))) =
      algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField ((a / b : _) : AlgebraicClosure K) *
        weilFunction E n hn T.val T.property := by
  simp only [weilFunction, Units.val_div_eq_div_val, map_div₀, div_mul_div_comm]

open Classical in
/-- 二つの分子生成元を独立に定数倍で選び直しても、固有方程式の解は同じc(S,T)だけである。 -/
theorem weilTranslationUnit_rescaled_numerators (n : ℕ) (hn : n ≠ 0) (T S : Torsion E n)
    (a b c : (AlgebraicClosure K)ˣ) :
    let g :=
      (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (a : AlgebraicClosure K) *
        algebraMap (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing (E.toAffine⁄(AlgebraicClosure K)).FunctionField
          (weilNumerator E n hn T.val T.property)) /
      (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (b : AlgebraicClosure K) *
        algebraMap (E.toAffine⁄(AlgebraicClosure K)).CoordinateRing (E.toAffine⁄(AlgebraicClosure K)).FunctionField
          (weilNumerator E n hn 0 (smul_zero n)))
    transEquiv E (AlgebraicClosure K) S.val g =
      algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (c : AlgebraicClosure K) * g ↔
      c = weilTranslationUnit E n hn T S := by
  dsimp only
  rw [weilNumerator_rescale_div]
  constructor
  · exact weilTranslationUnit_const_mul_unique E n hn T S (a / b) c
  · rintro rfl
    exact weilTranslationUnit_const_mul_spec E n hn T S (a / b)

open Classical in
/-- 零目標では元の商が1なので、全ての移動で比例定数は1。
これは右変数の零での値だけであり、右変数の加法性を仮定しない。 -/
theorem weilTranslationUnit_zero_target (n : ℕ) (hn : n ≠ 0) (S : Torsion E n) :
    weilTranslationUnit E n hn 0 S = 1 := by
  apply Eq.symm
  apply weilTranslationUnit_unique E n hn 0 S 1
  change transEquiv E (AlgebraicClosure K) S.val (weilFunction E n hn 0 (smul_zero n)) =
    algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (1 : AlgebraicClosure K) *
      weilFunction E n hn 0 (smul_zero n)
  simp only [weilFunction_zero, map_one, mul_one]

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
