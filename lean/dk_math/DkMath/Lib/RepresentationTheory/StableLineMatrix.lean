/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.MatrixRealization

#print "file: DkMath.Lib.RepresentationTheory.StableLineMatrix"

/-!
# 安定直線に適合する基底と上三角行列

第一基底ベクトルのspanが安定なら、各作用行列の左下成分は零になる。
従って対角成分の積は行列式に等しい。これは安定直線が存在した場合の制約であり、
直線の不存在を意味しない。円分行列式が別途得られれば、その値が対角成分の積になる。
-/
namespace DkMath.Lib.RepresentationTheory
open Module
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- 安定直線を第一基底ベクトルのspanに置くと、作用行列は上三角となる。 -/
theorem stable_basis_line_lower_left_zero (ρ : Representation k G V) (b : Basis (Fin 2) k V)
    (hstable : IsStable ρ (Submodule.span k ({b 0} : Set V))) (g : G) :
    (matrixGroupHom ρ b g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
  have hm := hstable g (b 0) (Submodule.mem_span_singleton_self (b 0))
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  rw [matrixGroupHom_val, LinearMap.toMatrix_apply]
  rw [← ha, map_smul, Finsupp.smul_apply, b.repr_self]
  simp

/-- 適合基底での対角成分の積は、基底に依存しない行列式と一致する。 -/
theorem stable_basis_line_diagonal_product (ρ : Representation k G V) (b : Basis (Fin 2) k V)
    (hstable : IsStable ρ (Submodule.span k ({b 0} : Set V))) (g : G) :
    (matrixGroupHom ρ b g : Matrix (Fin 2) (Fin 2) k) 0 0 *
      (matrixGroupHom ρ b g : Matrix (Fin 2) (Fin 2) k) 1 1 = LinearMap.det (ρ g) := by
  rw [← matrixGroupHom_det ρ b g, Matrix.det_fin_two,
    stable_basis_line_lower_left_zero ρ b hstable g, mul_zero, sub_zero]

end DkMath.Lib.RepresentationTheory
