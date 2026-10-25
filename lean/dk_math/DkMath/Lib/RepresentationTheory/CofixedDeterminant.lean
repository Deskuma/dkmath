/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.FixedCofixed
import DkMath.Lib.RepresentationTheory.StableLineMatrix
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Determinant

#print "file: DkMath.Lib.RepresentationTheory.CofixedDeterminant"

/-!
# NOTE-032-005B: Cofixed直線上の作用は行列式によるスカラー倍

[DkMath.Lib] f(x)−xが常に一次元部分空間Lへ入るとき、商V/Lの作用は恒等である。
det(f)=det(f|L)det(f on V/L)と、一次元の自己準同型はスカラー倍であることから、
L上の作用はdet(f)倍となる。周囲の有限次元空間の次元2、fの可逆性、標数条件は不要。

群表現へ適用するとCofixed直線の作用指標が行列式となる。
円分指標との一致はここでは入力であり、Weil対の所有者を利用側で供給する。
二次元の適合基底では行列は[det,*;0,1]となるが、右上成分が零とは結論しない。
直線の存在、表現の分裂、hnoの否定・肯定はこの章の結論ではない。
-/
namespace DkMath.Lib.RepresentationTheory.CofixedDeterminant
open Module
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- [DkMath.Lib] 商を固定する自己準同型は、一次元部分空間上でその行列式倍として作用する。
直線の保存は差の所属から内部供給し、商の恒等性と行列式の積公式を明示的に使う。 -/
theorem apply_eq_det_smul_of_sub_mem (f : V →ₗ[k] V) (L : Submodule k V)
    (hline : finrank k L = 1) (hcofixed : ∀ x, f x - x ∈ L) {x : V} (hx : x ∈ L) :
    f x = LinearMap.det f • x := by
  have hstable : L ≤ L.comap f := by
    intro y hy
    change f y ∈ L
    simpa only [sub_add_cancel] using L.add_mem (hcofixed y) hy
  obtain ⟨c, hres, -⟩ := (f.restrict hstable).existsUnique_eq_smul_id_of_finrank_eq_one hline
  have hQ : L.mapQ L f hstable = LinearMap.id := by
    ext y
    exact (Submodule.Quotient.eq L).mpr (hcofixed y)
  have hd := f.det_eq_det_mul_det L hstable
  rw [hres, hQ, LinearMap.det_smul, hline, pow_one, LinearMap.det_id,
    LinearMap.det_id, mul_one, mul_one] at hd
  have he := LinearMap.congr_fun hres (⟨x, hx⟩ : L)
  have hfx : f x = c • x := congrArg Subtype.val he
  rwa [← hd] at hfx

variable {G : Type*} [Group G]

/-- [DkMath.Lib] 群表現のCofixed直線上の作用は行列式倍である。
直線の安定性を重複して要求せず、Cofixed条件を同じ作用素へ適用する。 -/
theorem apply_eq_det_smul_of_cofixed (ρ : Representation k G V) (L : Submodule k V)
    (hline : finrank k L = 1) (hcofixed : IsCofixedOn ρ L) (g : G) {x : V} (hx : x ∈ L) :
    ρ g x = LinearMap.det (ρ g) • x :=
  apply_eq_det_smul_of_sub_mem (ρ g) L hline (hcofixed g) hx

/-- [DkMath.Lib] 行列式指標χを供給すれば、同じCofixed直線上の作用はχ倍となる。
χの値と行列式の向きを明示し、逆指標へ取り違えない。 -/
theorem apply_eq_character_smul_of_cofixed (ρ : Representation k G V) (L : Submodule k V)
    (hline : finrank k L = 1) (hcofixed : IsCofixedOn ρ L)
    (χ : G →* kˣ) (hdet : ∀ g, (χ g : k) = LinearMap.det (ρ g))
    (g : G) {x : V} (hx : x ∈ L) : ρ g x = (χ g : k) • x := by
  rw [hdet]
  exact apply_eq_det_smul_of_cofixed ρ L hline hcofixed g hx

omit [FiniteDimensional k V] in
/-- [DkMath.Lib] 二次元の適合基底では、Cofixed条件が右下成分1を強制する。
商の第二座標に差を射影して証明する。 -/
theorem basis_line_lower_right_one (ρ : Representation k G V) (b : Basis (Fin 2) k V)
    (hcofixed : IsCofixedOn ρ (Submodule.span k ({b 0} : Set V))) (g : G) :
    (matrixGroupHom ρ b g : Matrix (Fin 2) (Fin 2) k) 1 1 = 1 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hcofixed g (b 1))
  have he := congrArg (fun x => b.repr x 1) hc
  simp only [map_smul, Finsupp.smul_apply, b.repr_self, map_sub, Finsupp.sub_apply] at he
  simp at he
  rw [matrixGroupHom_val, LinearMap.toMatrix_apply]
  linear_combination -he

omit [FiniteDimensional k V] in
/-- [DkMath.Lib] Cofixed直線に適合した行列の形は[det,*;0,1]である。
右上成分を元の同じ行列から保持し、直和分解や対角化を先取りしない。 -/
theorem basis_line_matrix (ρ : Representation k G V) (b : Basis (Fin 2) k V)
    (hcofixed : IsCofixedOn ρ (Submodule.span k ({b 0} : Set V))) (g : G) :
    (matrixGroupHom ρ b g : Matrix (Fin 2) (Fin 2) k) =
      !![LinearMap.det (ρ g), (matrixGroupHom ρ b g : Matrix (Fin 2) (Fin 2) k) 0 1; 0, 1] := by
  have h₁₀ := stable_basis_line_lower_left_zero ρ b hcofixed.isStable g
  have h₁₁ := basis_line_lower_right_one ρ b hcofixed g
  have h₀₀ : (matrixGroupHom ρ b g : Matrix (Fin 2) (Fin 2) k) 0 0 = LinearMap.det (ρ g) := by
    simpa only [h₁₁, mul_one] using stable_basis_line_diagonal_product ρ b hcofixed.isStable g
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h₀₀, h₁₀, h₁₁]

end DkMath.Lib.RepresentationTheory.CofixedDeterminant
