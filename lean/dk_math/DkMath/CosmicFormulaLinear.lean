/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

namespace DkMath
namespace CosmicFormulaLinear

open InnerProductSpace

/-
宇宙式を「内積空間の恒等式」として言い換えた線形代数版。

中心（平均）  M = (A + C) / 2
余白（半差）  D = (C - A) / 2

すると（ℝ-内積空間では）
  ‖M‖^2 - ⟪A, C⟫ = ‖D‖^2
が常に成り立つ。

一次元（V=ℝ）に落とすと
  (x+u)^2 - x(x+2u) = u^2
がただちに復元される。
-/

section RealInner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Center (mean) vector. -/
noncomputable def M (A C : V) : V := (1/2 : ℝ) • (A + C)

/-- Gap (half-difference) vector. -/
noncomputable def D (A C : V) : V := (1/2 : ℝ) • (C - A)

/--
Linear-algebraic cosmic formula (ℝ-inner product space):

`‖(A+C)/2‖^2 - ⟪A,C⟫ = ‖(C-A)/2‖^2`
-/
theorem cosmic_formula_LA (A C : V) :
    ‖M (A := A) (C := C)‖ ^ 2 - (@inner ℝ V _ A C) = ‖D (A := A) (C := C)‖ ^ 2 := by
  -- convert `‖·‖^2` into inner products
  have hM :
      ‖M (A := A) (C := C)‖ ^ 2
        = @inner ℝ V _ (M (A := A) (C := C)) (M (A := A) (C := C)) := by
    simp [sq]
  have hD :
      ‖D (A := A) (C := C)‖ ^ 2
        = @inner ℝ V _ (D (A := A) (C := C)) (D (A := A) (C := C)) := by
    simp [sq]
  -- rewrite goal in terms of inner products
  rw [hM, hD]
  -- unfold M, D
  unfold M D
  -- expand by bilinearity
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  -- Show ⟪C, A⟫ = ⟪A, C⟫ and apply
  have : @inner ℝ V _ C A = @inner ℝ V _ A C := (inner_conj_symm C A).symm
  rw [this]
  ring

end RealInner

/-
A convenient one-dimensional corollary (V = ℝ):

The inner product is multiplication and `‖r‖^2 = r^2`,
so the LA identity collapses to the usual scalar cosmic formula.
-/
section Real1D

theorem cosmic_formula_real (x u : ℝ) :
    (x + u)^2 - x * (x + 2*u) = u^2 := by
  ring

end Real1D

end CosmicFormulaLinear
end DkMath
