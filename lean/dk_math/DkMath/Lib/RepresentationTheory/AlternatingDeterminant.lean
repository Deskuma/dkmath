/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.MatrixRealization
import Mathlib.LinearAlgebra.BilinearMap

#print "file: DkMath.Lib.RepresentationTheory.AlternatingDeterminant"

/-!
# 二次元の交代対が記録する行列式

対の値を取る空間Wも係数体上の加法的な空間として扱う。乗法的な根の群は
Additiveによってこの形に翻訳できる。交代性は特に標数2でも対角値が零であるという条件であり、
単なる反対称性で置き換えてはいけない。二次元では交代対の全ての値が基底対の値で決まり、
線形作用の前後でその値は行列式倍される。非退化性により基底対の値が非零なら、
対の値への作用指標と行列式指標を等しいと結論できる。
楕円曲線のWeil対の存在や非退化性を、この線形代数から作ったとは主張しない。
-/
namespace DkMath.Lib.RepresentationTheory
open Module
variable {k V W G : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- 二次元では交代対の基底を逆順にした値は、元の値の負となる。標数2も許す。 -/
theorem alternating_skew (e : V →ₗ[k] V →ₗ[k] W) (halt : ∀ x, e x x = 0) (x y : V) :
    e y x = -e x y := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- 任意の二つのベクトルへの交代対は、座標の2×2行列式と基底対の値で決まる。 -/
theorem alternating_coordinates (e : V →ₗ[k] V →ₗ[k] W) (halt : ∀ x, e x x = 0)
    (b : Basis (Fin 2) k V) (x y : V) :
    e x y = (b.repr x 0 * b.repr y 1 - b.repr x 1 * b.repr y 0) • e (b 0) (b 1) := by
  have hx : x = b.repr x 0 • b 0 + b.repr x 1 • b 1 := by
    simpa only [Fin.sum_univ_two] using (b.sum_repr x).symm
  have hy : y = b.repr y 0 • b 0 + b.repr y 1 • b 1 := by
    simpa only [Fin.sum_univ_two] using (b.sum_repr y).symm
  conv_lhs => rw [hx, hy]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, halt,
    smul_zero, zero_add, add_zero, alternating_skew e halt (b 0) (b 1)]
  module

/-- 非退化交代対は、基底対において非零である。値空間の次元を仮定する必要はない。 -/
theorem alternating_basis_ne_zero (e : V →ₗ[k] V →ₗ[k] W) (halt : ∀ x, e x x = 0)
    (hnd : ∀ x, (∀ y, e x y = 0) → x = 0) (b : Basis (Fin 2) k V) :
    e (b 0) (b 1) ≠ 0 := by
  intro h
  apply b.ne_zero 0
  apply hnd
  intro y
  rw [alternating_coordinates e halt b, h, smul_zero]

/-- 同じ線形作用を両変数に施すと、交代対の値は作用素の行列式倍になる。 -/
theorem alternating_map_eq_det_smul (e : V →ₗ[k] V →ₗ[k] W) (halt : ∀ x, e x x = 0)
    (b : Basis (Fin 2) k V) (f : V →ₗ[k] V) :
    e (f (b 0)) (f (b 1)) = LinearMap.det f • e (b 0) (b 1) := by
  rw [alternating_coordinates e halt b, ← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply]
  congr 2
  ring

variable [Group G]

/-- 対の同変性を与えた場合の行列式指標の同定。対の存在・非退化性・同変性は明示入力。
円分根の群を値空間に選べば、このχが円分指標となる。 -/
theorem determinantCharacter_eq_of_equivariant_pairing
    (ρ : Representation k G V) (χ : G →* kˣ) (b : Basis (Fin 2) k V)
    (e : V →ₗ[k] V →ₗ[k] W) (halt : ∀ x, e x x = 0)
    (hnd : ∀ x, (∀ y, e x y = 0) → x = 0)
    (heq : ∀ g x y, e (ρ g x) (ρ g y) = (χ g : k) • e x y) :
    determinantCharacterWithBasis ρ b = χ := by
  have hn := alternating_basis_ne_zero e halt hnd b
  ext g
  rw [determinantCharacterWithBasis_val]
  apply (smul_left_injective k hn)
  exact (alternating_map_eq_det_smul e halt b (ρ g)).symm.trans (heq g (b 0) (b 1))

end DkMath.Lib.RepresentationTheory
