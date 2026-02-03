/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

import DkMath.CosmicFormula.Defs  -- Basic Definitions

#print "file: DkMath.CosmicFormula.Basic"

namespace DkMath.CosmicFormula.Basic

/-- A: 宇宙式 Basic Cosmic Formula -/
def cosmic_formula_one (x : ℝ) : ℝ :=
  (x + 1)^2 - x * (x + 2)
  -- 宇宙式の基本形（恒等式）

/-- A': 宇宙式 Basic Cosmic Formula Alt. -/
def cosmic_formula_one_alt (x : ℝ) : ℝ :=
  (x + 1)^2 - x^2 - 2 * x
  -- 宇宙式の基本形（トロミノ構造式）

/-- B: 単位宇宙式 Unit Cosmic Formula -/
def cosmic_formula_unit (x u : ℝ) : ℝ :=
  (x + u)^2 - x * (x + 2 * u)
  -- u を任意の実数に拡張した形

/-- B': 単位宇宙式 Unit Cosmic Formula Alt. -/
def cosmic_formula_unit_alt (x u : ℝ) : ℝ :=
  (x + u)^2 - x^2 - 2 * x * u
  -- u を任意の実数に拡張した形（トロミノ構造式）

/-- C: 基本単位宇宙式 Basic Unit Cosmic Formula -/
def cosmic_formula_unit_one (x : ℝ) : ℝ :=
  cosmic_formula_unit x 1  -- A == B(1)
  -- 単位宇宙式の基本単位形（定義参照版）

/-- D: 宇宙式 Cosmic Formula -/
abbrev cosmic_formula := cosmic_formula_one  -- 宇宙式の標準名

-- 上記の定義の等価性を示す補題群

/-- 宇宙式 Basic Cosmic Formula と単位宇宙式 Basic Unit Cosmic Formula の等価性 -/
lemma cosmic_formula_one_eq_unit_one (x : ℝ) :
    cosmic_formula_one x = cosmic_formula_unit_one x := by
  -- 定義展開で等しい
  simp [cosmic_formula_one, cosmic_formula_unit_one, cosmic_formula_unit]

/-- 宇宙式 Basic Cosmic Formula とその別形の等価性 -/
lemma cosmic_formula_one_eq_alt (x : ℝ) :
    cosmic_formula_one x = cosmic_formula_one_alt x := by
  simp [cosmic_formula_one, cosmic_formula_one_alt]
  ring

/-- 単位宇宙式 Unit Cosmic Formula とその別形の等価性 -/
lemma cosmic_formula_unit_eq_alt (x u : ℝ) :
    cosmic_formula_unit x u = cosmic_formula_unit_alt x u := by
  simp [cosmic_formula_unit, cosmic_formula_unit_alt]
  ring

-- Additional definitions and theorems related to the cosmic formula can be added here.

-- 宇宙式の恒等式を証明する例
@[simp] theorem cosmic_formula_one_theorem (x : ℝ) : cosmic_formula_one x = 1 :=
  by
    simp [cosmic_formula_one]
    ring

example : ∀ x : ℝ, cosmic_formula_one x = 1 := cosmic_formula_one_theorem

-- 単位宇宙式の恒等式を証明する例
@[simp] theorem cosmic_formula_unit_theorem (x u : ℝ) : cosmic_formula_unit x u = u^2 :=
  by
    simp [cosmic_formula_unit]
    ring

-- test
example : ∀ x u : ℝ, cosmic_formula_unit x u = u^2 := cosmic_formula_unit_theorem

/-- 全ての関数 f(x) において 1 を返す -/
theorem cosmic_formula_one_func :
    ∀ (f : ℝ → ℝ) (x : ℝ), cosmic_formula_one (f x) = 1 := by
  intro f x
  simp [cosmic_formula_one_theorem]

/-- 全ての関数 f(x), g(u) において g(u) ↦ (g(u))^2 を返す -/
theorem cosmic_formula_unit_func :
    ∀ (f : ℝ → ℝ) (g : ℝ → ℝ) (x u : ℝ),
      cosmic_formula_unit (f x) (g u) = (g u)^2 := by
  intro f g x u
  simp [cosmic_formula_unit_theorem]

/-- 宇宙式の 1 + 1 = 2 -/
theorem cosmic_formula_one_add :
    ∀ x y : ℝ, cosmic_formula_one x + cosmic_formula_one y = 2 := by
  intro x y
  simp only [cosmic_formula_one_theorem]
  norm_num

/-- 単位宇宙式による異なる単位の加法 -/
theorem cosmic_formula_unit_add :
    ∀ x y u v : ℝ,
      cosmic_formula_unit x u + cosmic_formula_unit y v = u^2 + v^2 := by
  intro x y u v
  simp only [cosmic_formula_unit_theorem]

/-- 宇宙式の加法（関数版）f(x) + f(y) = 2 -/
theorem cosmic_formula_one_func_add :
    ∀ (f : ℝ → ℝ) (x y : ℝ),
      cosmic_formula_one (f x) + cosmic_formula_one (f y) = 2 := by
  intro f x y
  simp only [cosmic_formula_one_theorem]
  norm_num

/-- 単位宇宙式による異なる単位の加法（関数版）
  ⟨ f(x), g(u) ⟩ + ⟨ f(y), g(v) ⟩ = (g(u))^2 + (g(v))^2 -/
theorem cosmic_formula_unit_func_add :
    ∀ (f : ℝ → ℝ) (g : ℝ → ℝ) (x y u v : ℝ),
      cosmic_formula_unit (f x) (g u) + cosmic_formula_unit (f y) (g v) = (g u)^2 + (g v)^2 := by
  intro f g x y u v
  simp only [cosmic_formula_unit_theorem]

-- More theorems and proofs can be added here.

-- 「差」版（減法が要るので CommRing）
def cosmic_formula_unit_sub {R : Type*} [CommRing R] (x u : R) : R :=
  (x + u)^2 - x * (x + 2 * u)

@[simp] theorem cosmic_formula_unit_sub_eq {R : Type*} [CommRing R] (x u : R) :
    cosmic_formula_unit_sub x u = u^2 := by
  unfold cosmic_formula_unit_sub
  ring

@[simp] theorem cosmic_formula_one_sub_eq {R : Type*} [CommRing R] (x : R) :
    cosmic_formula_unit_sub x (1 : R) = 1 := by
  simp [cosmic_formula_unit_sub_eq]

-- 「加法」版（こちらが宇宙式の素顔。減法なしで済むので CommSemiring まで下げられる）
def N {R : Type*} [CommSemiring R] (x u : R) : R := x * (x + 2 * u)
def P {R : Type*} [CommSemiring R] (x u : R) : R := (x + u)^2

theorem cosmic_formula_add {R : Type*} [CommSemiring R] (x u : R) :
    N x u + u^2 = P x u := by
  -- 展開して終わり。ここは純粋に多項式恒等式。
  simp [N, P]
  ring

-- “差=平方” の形にも戻せる（ただし戻すには減法が要る）
theorem cosmic_formula_sub_from_add {R : Type*} [CommRing R] (x u : R) :
    (P x u) - (N x u) = u^2 := by
  -- add 版から引き算して得る
  have h := cosmic_formula_add (R := R) (x := x) (u := u)
  -- N x u + u^2 = P x u  ⇒  P x u - N x u = u^2
  rw [←h]
  ring

-- More theorems and proofs can be added here.

/--
Equality of the two variants of the cosmic formula.

For all real `x` and `u`, the convenience definition `cosmic_formula_unit x u`
coincides with the alternative/subscript definition `cosmic_formula_unit_sub x u`.
The proof proceeds by simplifying/unfolding both definitions.
-/
lemma cosmic_formula_unit_eq_sub (x u : ℝ) :
    cosmic_formula_unit x u = cosmic_formula_unit_sub x u := by
  simp [cosmic_formula_unit, cosmic_formula_unit_sub]

/-- For any real `x`, `cosmic_formula_one x` is definitionally equal to
`cosmic_formula_unit_sub x 1`. This lemma connects the specialized
`cosmic_formula_one` with the more general `cosmic_formula_unit_sub`
instantiated at `u = 1`. It can be used to rewrite `cosmic_formula_one`
into the more general `unit_sub` form when convenient. -/
lemma cosmic_formula_one_eq_sub (x : ℝ) :
    cosmic_formula_one x = cosmic_formula_unit_sub x (1:ℝ) := by
  simp [cosmic_formula_one, cosmic_formula_unit_sub]

-- Additional lemmas and theorems can be added here.

/-- cosmic_formula_unit_sub_u0

For any commutative ring R and element x : R, substituting 0 into the second argument
of `cosmic_formula_unit_sub` yields 0:

  cosmic_formula_unit_sub x (0 : R) = 0

Parameters
- `R` : a type equipped with a `CommRing` instance
- `x` : an element of `R`

Proof sketch: unfold the definition of `cosmic_formula_unit_sub` and finish with `ring`.
-/
@[simp] lemma cosmic_formula_unit_sub_u0 {R : Type*} [CommRing R] (x : R) :
    cosmic_formula_unit_sub x (0:R) = 0 := by
  unfold cosmic_formula_unit_sub
  ring

/--
For any commutative ring R and element `u : R`, evaluating
`cosmic_formula_unit_sub` at `x0 = 0` yields `u^2`. The equality follows
by unfolding the definition of `cosmic_formula_unit_sub` and simplifying.
-/
@[simp] lemma cosmic_formula_unit_sub_x0 {R : Type*} [CommRing R] (u : R) :
    cosmic_formula_unit_sub (0:R) u = u^2 := by
  simp [cosmic_formula_unit_sub]

-- 加法版でも
/-- If the parameter `x` is `0`, then `N` evaluates to `0` for any element `u` of a commutative
semiring `R`. This lemma provides a simplification rule for expressions involving `N` when
`x` is instantiated to `0`. -/
@[simp] lemma N_x0 {R : Type*} [CommSemiring R] (u : R) : N (x := (0:R)) u = 0 := by
  simp [N]

/-- For any commutative semiring R and element u : R, evaluating the polynomial/function P at x = 0
returns u^2. The proof is by simplification (unfolding the definition of `P`). -/
@[simp] lemma P_x0 {R : Type*} [CommSemiring R] (u : R) : P (x := (0:R)) u = u^2 := by
  simp [P]

end DkMath.CosmicFormula.Basic
