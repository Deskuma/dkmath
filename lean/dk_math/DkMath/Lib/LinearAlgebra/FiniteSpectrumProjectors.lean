/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Algebra.DirectSum.Module

#print "file: DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors"

/-!
# IRR-009: 有限スペクトルの補間射影

相異なる節点 vᵢ の消失多項式 ∏ᵢ(X−vᵢ) が T を消すなら、Lagrange 基底多項式を
T に代入すると、固有成分への射影になる。射影の和は恒等写像、異なる射影の積は0、
各射影は冪等となり、実際の有限直和への線形同型が得られる。
有限次元性は不要。成分の次元・非自明性や、特定の算術類の存在も仮定しない。
-/
namespace DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors
open Polynomial Module
open scoped DirectSum
variable {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
  [Fintype ι] [DecidableEq ι]
  (v : ι → F) (T : End F V)

/-- 補間基底の T における評価。数値的な固有ベクトルの選択は行わない。 -/
noncomputable def projector (i : ι) : End F V := aeval T (Lagrange.basis Finset.univ v i)

/-- Lagrange 基底を対応する一次因子で掛けると、消失多項式の定数倍になる。 -/
theorem linear_factor_mul_basis (i : ι) :
    (X - C (v i)) * Lagrange.basis Finset.univ v i =
      C (Lagrange.nodalWeight Finset.univ v i) * Lagrange.nodal Finset.univ v := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ i),
    ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ i),
    Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ i)]
  ring

/-- 消失多項式が T を消す時、射影の値は対応する固有空間に入る。 -/
theorem projector_eigen (hT : aeval T (Lagrange.nodal Finset.univ v) = 0)
    (i : ι) (x : V) : T (projector v T i x) = v i • projector v T i x := by
  have h := congrArg (aeval T) (linear_factor_mul_basis v i)
  rw [map_mul, map_sub, aeval_X, aeval_C, map_mul, hT, mul_zero] at h
  have hx := LinearMap.congr_fun h x
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply,
    LinearMap.zero_apply, sub_eq_zero, projector] using hx

/-- 各固有空間上で、対応する射影は恒等写像、他の射影は0となる。 -/
theorem projector_apply_eigen (hv : Function.Injective v) {i j : ι} {x : V}
    (hx : T x = v j • x) : projector v T i x = if i = j then x else 0 := by
  rw [projector, Module.End.aeval_apply_of_mem_apply_eq_smul hx]
  by_cases hij : i = j
  · subst i
    rw [ite_eq_left rfl, Lagrange.eval_basis_self hv.injOn (Finset.mem_univ _), one_smul]
  · rw [ite_eq_right hij, Lagrange.eval_basis_of_ne hij (Finset.mem_univ _), zero_smul]

/-- 相異なる節点の射影の和は恒等写像。 -/
theorem sum_projector [Nonempty ι] (hv : Function.Injective v) : ∑ i, projector v T i = 1 := by
  change ∑ i, aeval T (Lagrange.basis Finset.univ v i) = 1
  rw [← map_sum, Lagrange.sum_basis hv.injOn Finset.univ_nonempty, map_one]

/-- 射影された成分を足すと、元のベクトルを正確に復元する。 -/
theorem sum_projector_apply [Nonempty ι] (hv : Function.Injective v) (x : V) :
    ∑ i, projector v T i x = x := by
  have h := LinearMap.congr_fun (sum_projector v T hv) x
  simpa only [LinearMap.sum_apply, Module.End.one_apply] using h

/-- 射影は冪等。値の算術的な消滅とは異なる、線形作用素の恒等式である。 -/
theorem projector_idempotent (hv : Function.Injective v)
    (hT : aeval T (Lagrange.nodal Finset.univ v) = 0) (i : ι) :
    projector v T i * projector v T i = projector v T i := by
  ext x
  exact (projector_apply_eigen v T hv (projector_eigen v T hT i x)).trans (ite_eq_left rfl)

/-- 異なる成分の射影は直交する。 -/
theorem projector_orthogonal (hv : Function.Injective v)
    (hT : aeval T (Lagrange.nodal Finset.univ v) = 0) {i j : ι} (hij : i ≠ j) :
    projector v T i * projector v T j = 0 := by
  ext x
  exact (projector_apply_eigen v T hv (projector_eigen v T hT j x)).trans (ite_eq_right hij)

/-- 有限個の固有成分への分解と、和による復元を持つ本当の線形同型。 -/
noncomputable def decompose [Nonempty ι] (hv : Function.Injective v)
    (hT : aeval T (Lagrange.nodal Finset.univ v) = 0) :
    V ≃ₗ[F] (∀ i, T.eigenspace (v i)) where
  toFun x i := ⟨projector v T i x, Module.End.mem_eigenspace_iff.mpr (projector_eigen v T hT i x)⟩
  invFun f := ∑ i, (f i : V)
  left_inv x := sum_projector_apply v T hv x
  right_inv f := by
    funext i
    apply Subtype.ext
    change projector v T i (∑ j, (f j : V)) = (f i : V)
    rw [map_sum]
    simp_rw [projector_apply_eigen v T hv (Module.End.mem_eigenspace_iff.mp (f _).property)]
    simp
  map_add' x y := by
    funext i
    apply Subtype.ext
    exact (projector v T i).map_add x y
  map_smul' c x := by
    funext i
    apply Subtype.ext
    exact (projector v T i).map_smul c x

/-- 有限積と有限直和の標準同型を通じた、固有空間の直和への線形同型。 -/
noncomputable def directSumEquiv [Nonempty ι] (hv : Function.Injective v)
    (hT : aeval T (Lagrange.nodal Finset.univ v) = 0) :
    V ≃ₗ[F] ⨁ i, T.eigenspace (v i) :=
  (decompose v T hv hT).trans (DirectSum.linearEquivFunOnFintype F ι _).symm

/-- 元が非零なら、少なくとも一つの射影が非零。非零元そのものは構成しない。 -/
theorem exists_nonzero_projector [Nonempty ι] (hv : Function.Injective v) {x : V} (hx : x ≠ 0) :
    ∃ i, projector v T i x ≠ 0 := by
  by_contra h
  push Not at h
  have he := sum_projector_apply v T hv x
  simp only [h, Finset.sum_const_zero] at he
  exact hx he.symm

end DkMath.Lib.LinearAlgebra.FiniteSpectrumProjectors
