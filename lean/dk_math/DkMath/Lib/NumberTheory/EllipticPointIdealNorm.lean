/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticPointIdealValuation
import Mathlib.LinearAlgebra.FreeModule.Norm

#print "file: DkMath.Lib.NumberTheory.EllipticPointIdealNorm"

/-!
# 中国剰余定理で有限零点を数える

相異なる有限点のイデアルの積を生成するrに対し、座標環を(r)で割った商は
各点の剰余体の直積になる。各剰余体は係数体そのものなので、その次元は有限点の数。
Mathlibの商の次元=ノルム次数を使えば、一般の付値総和や素イデアル冪の濾過を導入せず、
この重複度1の状況で必要な次数公式を直接得られる。Oの単位イデアルは積から除く。
-/
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open IsDedekindDomain
namespace DkMath.Lib.NumberTheory.EllipticPointIdealNorm
open EllipticPrincipalPointIdeal
variable {F : Type*} [Field F] (W : WeierstrassCurve F)

open Classical in
/-- 有限点の点イデアルは極大であり、剰余体の係数体上の次元は1。 -/
theorem finrank_quotient_pointIdeal {P : W.toAffine.Point} (hP : P ≠ 0) :
    Module.finrank F (W.toAffine.CoordinateRing ⧸ pointIdeal P) = 1 := by
  rw [pointIdeal_of_ne_zero hP]
  exact (CoordinateRing.quotientXYIdealEquiv (Point.nonsingular_xc_yc hP).left).toLinearEquiv.finrank_eq.trans
    (Module.finrank_self F)

open Classical in
/-- 相異なる有限点の積を生成する元のノルム次数は点数に等しい。
Oの寄与は単位イデアルなので、集合からOを除いた濃度となる。 -/
theorem natDegree_norm_of_span_eq_prod [IsDedekindDomain W.toAffine.CoordinateRing]
    (s : Finset W.toAffine.Point) {r : W.toAffine.CoordinateRing}
    (hr : Ideal.span {r} = ∏ P ∈ s, pointIdeal P) :
    (Algebra.norm F[X] r).natDegree = (s.filter (· ≠ 0)).card := by
  classical
  let t := s.filter (· ≠ 0)
  have hn (i : t) : (i.val : W.toAffine.Point) ≠ 0 := (Finset.mem_filter.mp i.property).2
  let v (i : t) : HeightOneSpectrum W.toAffine.CoordinateRing :=
    ⟨pointIdeal i.val, (by
      rw [pointIdeal_of_ne_zero (hn i)]
      exact (EllipticCoordinateRing.isMaximal_XYIdeal (Point.nonsingular_xc_yc (hn i)).left).isPrime),
      pointIdeal_ne_bot i.val⟩
  have hv : Function.Injective v := by
    intro i j h
    apply Subtype.ext
    have he := congrArg HeightOneSpectrum.asIdeal h
    change pointIdeal i.val = pointIdeal j.val at he
    rw [pointIdeal_of_ne_zero (hn i), pointIdeal_of_ne_zero (hn j)] at he
    have hc : Point.toClass i.val = Point.toClass j.val := by
      cases hi : i.val with
      | zero => exact ((hn i) hi).elim
      | some x y hxy =>
        cases hj : j.val with
        | zero => exact ((hn j) hj).elim
        | some x' y' hxy' =>
          rw [Point.toClass_some, Point.toClass_some]
          apply congrArg (ClassGroup.mk W.toAffine.FunctionField)
          apply Units.ext
          rw [CoordinateRing.XYIdeal'_eq, CoordinateRing.XYIdeal'_eq]
          congr 1
          simpa only [hi, hj, Point.xc_some, Point.yc_some] using he
    exact Point.toClass_injective hc
  have hp : ∏ i : t, (v i).asIdeal ^ (1 : ℕ) = Ideal.span {r} := by
    simp only [pow_one]
    rw [Finset.prod_coe_sort]
    change (∏ P ∈ t, pointIdeal P) = _
    rw [hr]
    dsimp [t]
    rw [Finset.prod_filter_of_ne]
    intro P _ hP hP0
    exact hP (by rw [hP0, pointIdeal_zero, Ideal.one_eq_top])
  let e : (W.toAffine.CoordinateRing ⧸ Ideal.span {r}) ≃ₐ[F]
      (∀ i : t, W.toAffine.CoordinateRing ⧸ (v i).asIdeal ^ (1 : ℕ)) :=
    AlgEquiv.ofRingEquiv
      (f := HeightOneSpectrum.quotientEquivPiOfProdEq _ v (fun _ => 1)
        (fun i j hij => hv.ne hij) hp) (fun _ => rfl)
  have hr0 : r ≠ 0 := by
    intro h
    apply prod_pointIdeal_ne_bot s id
    change (∏ P ∈ s, pointIdeal P) = ⊥
    rw [← hr, h, Ideal.span_singleton_eq_bot.mpr rfl]
  have : ∀ i : t, Module.Finite F (W.toAffine.CoordinateRing ⧸ (v i).asIdeal ^ (1 : ℕ)) := fun i => by
    change Module.Finite F (W.toAffine.CoordinateRing ⧸ pointIdeal i.val ^ (1 : ℕ))
    rw [pow_one, pointIdeal_of_ne_zero (hn i)]
    exact Module.Finite.equiv
      (CoordinateRing.quotientXYIdealEquiv (Point.nonsingular_xc_yc (hn i)).left).toLinearEquiv.symm
  rw [← finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis W.toAffine) hr0,
    e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  have hc (i : t) : Module.finrank F
      (W.toAffine.CoordinateRing ⧸ (v i).asIdeal ^ (1 : ℕ)) = 1 := by
    change Module.finrank F (W.toAffine.CoordinateRing ⧸ pointIdeal i.val ^ (1 : ℕ)) = 1
    rw [pow_one]
    exact finrank_quotient_pointIdeal W (hn i)
  simp only [hc, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_coe]
  rfl

end DkMath.Lib.NumberTheory.EllipticPointIdealNorm
