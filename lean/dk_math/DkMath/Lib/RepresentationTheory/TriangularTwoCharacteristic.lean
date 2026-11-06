/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.TriangularTwoCharacter
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

#print "file: DkMath.Lib.RepresentationTheory.TriangularTwoCharacteristic"

/-!
# 上三角作用の特性多項式と実際の二次関係

係数環は可換環。非対角成分を零と仮定せず、全行列について証明する。
-/
namespace DkMath.Lib.RepresentationTheory.TriangularTwoCharacter
open Polynomial
variable {Γ R : Type*} [Group Γ] [CommRing R]
    (ρ : Γ →* Matrix (Fin 2) (Fin 2) R) (ht : ∀ g, ρ g 1 0 = 0)

/-- 実際の trace は同じ二つの対角指標の和。 -/
theorem trace (g : Γ) :
    (ρ g).trace = (first ρ ht g : R) + (second ρ ht g : R) := Matrix.trace_fin_two _

/-- 二つの対角指標が特性多項式を因数分解する。分裂するのは多項式であり表現ではない。 -/
theorem charpoly_factor [Nontrivial R] (g : Γ) :
    (ρ g).charpoly = (X - C (first ρ ht g : R)) * (X - C (second ρ ht g : R)) := by
  rw [Matrix.charpoly_fin_two, trace ρ ht, determinant ρ ht, map_add, map_mul]
  ring

/-- 同じ行列自体の二次関係。上右成分を含めて直接確認する。 -/
theorem quadratic (g : Γ) :
    ρ g * ρ g + ((first ρ ht g : R) * (second ρ ht g : R)) • (1 : Matrix (Fin 2) (Fin 2) R) =
      ((first ρ ht g : R) + (second ρ ht g : R)) • ρ g := by
  change ρ g * ρ g + (ρ g 0 0 * ρ g 1 1) • (1 : Matrix (Fin 2) (Fin 2) R) =
    (ρ g 0 0 + ρ g 1 1) • ρ g
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ht] <;> ring

/-- 任意の二次行列の二次関係。三角性さえ必要ない。 -/
theorem matrix_quadratic (M : Matrix (Fin 2) (Fin 2) R) :
    M * M + M.det • (1 : Matrix (Fin 2) (Fin 2) R) = M.trace • M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

/-- 実際の基底での行列の二次関係を、同じ線形作用そのものへ戻す。 -/
theorem linear_quadratic {V : Type*} [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin 2) R V) (f : V →ₗ[R] V) (a c : R)
    (htrace : (LinearMap.toMatrix b b f).trace = a)
    (hdet : (LinearMap.toMatrix b b f).det = c) (x : V) :
    f (f x) + c • x = a • f x := by
  have hm := matrix_quadratic (LinearMap.toMatrix b b f)
  rw [htrace, hdet] at hm
  have hf : f * f + c • (1 : V →ₗ[R] V) = a • f := by
    apply (LinearMap.toMatrixAlgEquiv b).injective
    simp only [map_add, map_mul, map_smul, map_one]
    change (LinearMap.toMatrix b b f) * (LinearMap.toMatrix b b f) + c • 1 = a • (LinearMap.toMatrix b b f)
    exact hm
  exact congrArg (fun g : V →ₗ[R] V => g x) hf

end DkMath.Lib.RepresentationTheory.TriangularTwoCharacter
