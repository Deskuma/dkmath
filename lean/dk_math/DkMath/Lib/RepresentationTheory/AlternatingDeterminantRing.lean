/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.AlternatingDeterminant

#print "file: DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing"

/-!
# 可換環上の二次元交代対と係数の忠実性

法 p 冪は一般に体でない。非零ベクトルの scalar 消去を使わず、
非退化性から基底対の値に作用する係数の単射性を直接証明する。
-/
namespace DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing
open Module
variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W]
    (e : V →ₗ[R] V →ₗ[R] W) (halt : ∀ x, e x x = 0) (b : Basis (Fin 2) R V)

include halt

/-- 可換環上でも交代性は反対称性を与える。 -/
theorem skew (x y : V) : e y x = - e x y := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- 環上の基底座標による交代対の実際の展開。 -/
theorem coordinates (x y : V) :
    e x y = (b.repr x 0 * b.repr y 1 - b.repr x 1 * b.repr y 0) • e (b 0) (b 1) := by
  have hx : x = b.repr x 0 • b 0 + b.repr x 1 • b 1 := by
    simpa only [Fin.sum_univ_two] using (b.sum_repr x).symm
  have hy : y = b.repr y 0 • b 0 + b.repr y 1 • b 1 := by
    simpa only [Fin.sum_univ_two] using (b.sum_repr y).symm
  conv_lhs => rw [hx, hy]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, halt,
    smul_zero, zero_add, add_zero, skew e halt (b 0) (b 1)]
  module

/-- 非退化性は基底対の値に対する scalar 作用を忠実にする。体の仮定は不要。 -/
theorem coefficient_injective (hnd : ∀ x, (∀ y, e x y = 0) → x = 0) :
    Function.Injective (fun a : R => a • e (b 0) (b 1)) := by
  intro a c h
  dsimp only at h
  have hz : (a - c) • e (b 0) (b 1) = 0 := by rw [sub_smul, h, sub_self]
  have hx : (a - c) • b 0 = 0 := by
    apply hnd
    intro y
    rw [map_smul, LinearMap.smul_apply]
    have hb : e (b 0) y = b.repr y 1 • e (b 0) (b 1) := by
      rw [coordinates e halt b]
      simp
    rw [hb, smul_comm, hz, smul_zero]
  have hc := congrArg (fun x : V => b.repr x 0) hx
  have hd : a - c = 0 := by simpa using hc
  exact sub_eq_zero.mp hd

/-- 同じ線形作用の前後で、対の値は実際の行列式倍になる。 -/
theorem map_eq_det_smul (f : V →ₗ[R] V) :
    e (f (b 0)) (f (b 1)) = LinearMap.det f • e (b 0) (b 1) := by
  rw [coordinates e halt b, ← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply]
  congr 2
  ring

/-- 同変性と忠実性から行列式の係数を同定する。 -/
theorem det_eq_of_equivariant (hnd : ∀ x, (∀ y, e x y = 0) → x = 0)
    (f : V →ₗ[R] V) (c : R) (heq : e (f (b 0)) (f (b 1)) = c • e (b 0) (b 1)) :
    LinearMap.det f = c :=
  coefficient_injective e halt b hnd ((map_eq_det_smul e halt b f).symm.trans heq)

end DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing
