/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_weilPairing0_add_right.lean.
Upstream blob: b879635a2748bd9456704403fac7c8db141b2895
Modified for DkMath: use natural torsion, NOTE-024 point orders and NOTE-025 unique scalar;
remove export macros and unported providers.
-/

import DkMath.Lib.NumberTheory.EllipticWeilCharacter
import DkMath.Lib.NumberTheory.EllipticPointOrderAlgebra

#print "file: DkMath.Lib.NumberTheory.EllipticWeilRightAdd"

/-!
# 右変数の加法性は三つの既存関数の比較から従う

nU=Tとなる実際の点Uを倍写像の全射性で選ぶ。
h=w(T)・τ(−U)*w(R)の位数は、中間ファイバーの寄与が相殺してw(T+R)の位数に一致する。
NOTE-025の定数比判定により両者は非零定数倍であり、Sによる移動の固有値の一意性から
c(S,T+R)=c(S,T)c(S,R)を得る。新しいWeil関数や右加法性のproviderを仮定しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField
variable {K : Type*} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]

open Classical in
/-- 平行移動の合成則を、実際の関数への適用として取り出す。 -/
theorem transEquiv_comp_apply (S R : (E⁄(AlgebraicClosure K)).Point)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) :
    transEquiv E (AlgebraicClosure K) S (transEquiv E (AlgebraicClosure K) R f) =
      transEquiv E (AlgebraicClosure K) (S + R) f :=
  (DFunLike.congr_fun (transEquiv_add E (AlgebraicClosure K) S R) f).symm

open Classical in
/-- 点群の可換性により、二つの引き戻し自己同型も関数上で可換である。 -/
theorem transEquiv_comm_apply (S R : (E⁄(AlgebraicClosure K)).Point)
    (f : (E.toAffine⁄(AlgebraicClosure K)).FunctionField) :
    transEquiv E (AlgebraicClosure K) S (transEquiv E (AlgebraicClosure K) R f) =
      transEquiv E (AlgebraicClosure K) R (transEquiv E (AlgebraicClosure K) S f) := by
  rw [transEquiv_comp_apply, transEquiv_comp_apply, add_comm]

variable [CharZero K]

/-- 固定した移動Sについての右加法性。T+Rは実際の同じn-torsion部分群の和である。 -/
theorem weilTranslationUnit_add_right (n : ℕ) (hn : n ≠ 0) (S T R : Torsion E n) :
    weilTranslationUnit E n hn (T + R) S =
      weilTranslationUnit E n hn T S * weilTranslationUnit E n hn R S := by
  classical
  have hT : n • T.val = 0 := T.property
  have hR : n • R.val = 0 := R.property
  have hTR : n • (T + R).val = 0 := (T + R).property
  obtain ⟨U, hU⟩ := multiplication_surjective E n hn T.val
  change n • U = T.val at hU
  let h := weilFunction E n hn T.val hT *
    transEquiv E (AlgebraicClosure K) (-U) (weilFunction E n hn R.val hR)
  have hh : h ≠ 0 := mul_ne_zero (weilFunction_ne_zero E n hn T.val hT)
    ((transEquiv E (AlgebraicClosure K) (-U)).toRingEquiv.map_ne_zero_iff.mpr
      (weilFunction_ne_zero E n hn R.val hR))
  have ho (P : Points E) :
      pointOrder E P (weilFunction E n hn (T + R).val hTR)
        (weilFunction_ne_zero E n hn (T + R).val hTR) = pointOrder E P h hh := by
    have e1 : n • (P + -U) = R.val ↔ n • P = (T + R).val := by
      change n • (P + -U) = R.val ↔ n • P = T.val + R.val
      rw [smul_add, smul_neg, hU, ← sub_eq_add_neg, sub_eq_iff_eq_add, add_comm R.val T.val]
    have e2 : n • (P + -U) = 0 ↔ n • P = T.val := by
      rw [smul_add, smul_neg, hU, ← sub_eq_add_neg, sub_eq_zero]
    have htrans := pointOrder_transEquiv_weilFunction E n hn R.val hR P (-U)
    have hmul := pointOrder_mul E P (weilFunction E n hn T.val hT)
      (transEquiv E (AlgebraicClosure K) (-U) (weilFunction E n hn R.val hR))
      (weilFunction_ne_zero E n hn T.val hT)
      ((transEquiv E (AlgebraicClosure K) (-U)).toRingEquiv.map_ne_zero_iff.mpr
        (weilFunction_ne_zero E n hn R.val hR))
    change pointOrder E P (weilFunction E n hn (T + R).val hTR) _ = _
    rw [show pointOrder E P h hh = _ from hmul,
      pointOrder_weilFunction, pointOrder_weilFunction, htrans]
    simp only [e1, e2]
    omega
  obtain ⟨a, ha, -⟩ := existsUnique_scalar_of_pointOrder_eq E _ h
    (weilFunction_ne_zero E n hn (T + R).val hTR) hh ho
  apply Eq.symm
  apply weilTranslationUnit_unique E n hn (T + R) S _
  have hspecT : transEquiv E (AlgebraicClosure K) S.val (weilFunction E n hn T.val hT) =
      algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField
        (weilTranslationUnit E n hn T S : AlgebraicClosure K) * weilFunction E n hn T.val hT :=
    weilTranslationUnit_spec E n hn T S
  have hspecR : transEquiv E (AlgebraicClosure K) S.val (weilFunction E n hn R.val hR) =
      algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField
        (weilTranslationUnit E n hn R S : AlgebraicClosure K) * weilFunction E n hn R.val hR :=
    weilTranslationUnit_spec E n hn R S
  have hcomm : transEquiv E (AlgebraicClosure K) S.val
      (transEquiv E (AlgebraicClosure K) (-U) (weilFunction E n hn R.val hR)) =
      transEquiv E (AlgebraicClosure K) (-U)
        (transEquiv E (AlgebraicClosure K) S.val (weilFunction E n hn R.val hR)) :=
    transEquiv_comm_apply E S.val (-U) _
  calc
    transEquiv E (AlgebraicClosure K) S.val (weilFunction E n hn (T + R).val hTR) =
        transEquiv E (AlgebraicClosure K) S.val
          (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (a : AlgebraicClosure K) * h) :=
      congrArg (transEquiv E (AlgebraicClosure K) S.val) ha
    _ = algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField
          ((weilTranslationUnit E n hn T S * weilTranslationUnit E n hn R S : _) : AlgebraicClosure K) *
        (algebraMap (AlgebraicClosure K) (E.toAffine⁄(AlgebraicClosure K)).FunctionField (a : AlgebraicClosure K) * h) := by
      dsimp only [h]
      rw [map_mul, AlgEquiv.commutes, map_mul, hspecT,
        hcomm, hspecR, map_mul, AlgEquiv.commutes,
        Units.val_mul, map_mul]
      ring
    _ = _ := congrArg (fun z => algebraMap (AlgebraicClosure K)
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField
      ((weilTranslationUnit E n hn T S * weilTranslationUnit E n hn R S : _) : AlgebraicClosure K) * z) ha.symm

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
