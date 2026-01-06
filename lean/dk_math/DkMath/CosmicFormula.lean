import Mathlib

namespace DkMath

namespace CosmicFormula

/-- 宇宙式 Basic Cosmic Formula -/
-- 宇宙式の基本形（恒等式）
def cosmic_formula_one (x : ℝ) : ℝ :=
  (x + 1)^2 - x * (x + 2)

/-- 単位宇宙式 Unit Cosmic Formula -/
-- u を任意の実数に拡張した形
def cosmic_formula_u (x u : ℝ) : ℝ :=
  (x + u)^2 - x * (x + 2 * u)

-- Additional definitions and theorems related to the cosmic formula can be added here.

-- 宇宙式の恒等式を証明する例
theorem example_theorem (x : ℝ) : cosmic_formula_one x = 1 :=
  by
    simp [cosmic_formula_one]
    ring

example : ∀ x : ℝ, cosmic_formula_one x = 1 := example_theorem

-- 単位宇宙式の恒等式を証明する例
theorem example_theorem_u (x u : ℝ) : cosmic_formula_u x u = u^2 :=
  by
    simp [cosmic_formula_u]
    ring

example : ∀ x u : ℝ, cosmic_formula_u x u = u^2 := example_theorem_u

-- More theorems and proofs can be added here.

-- 「差」版（減法が要るので CommRing）
def cosmic_formula_u_sub {R : Type*} [CommRing R] (x u : R) : R :=
  (x + u)^2 - x * (x + 2 * u)

@[simp] theorem cosmic_formula_u_sub_eq {R : Type*} [CommRing R] (x u : R) :
    cosmic_formula_u_sub x u = u^2 := by
  unfold cosmic_formula_u_sub
  ring

@[simp] theorem cosmic_formula_one_sub_eq {R : Type*} [CommRing R] (x : R) :
    cosmic_formula_u_sub x (1 : R) = 1 := by
  simp [cosmic_formula_u_sub_eq]

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

For all real `x` and `u`, the convenience definition `cosmic_formula_u x u`
coincides with the alternative/subscript definition `cosmic_formula_u_sub x u`.
The proof proceeds by simplifying/unfolding both definitions.
-/
@[simp] lemma cosmic_formula_u_eq_sub (x u : ℝ) :
    cosmic_formula_u x u = cosmic_formula_u_sub x u := by
  simp [cosmic_formula_u, cosmic_formula_u_sub]

/-- For any real `x`, `cosmic_formula_one x` is definitionally equal to
`cosmic_formula_u_sub x 1`. This lemma connects the specialized
`cosmic_formula_one` with the more general `cosmic_formula_u_sub`
instantiated at `u = 1`. It is intended as a `@[simp]` lemma so that
`cosmic_formula_one` can be simplified to the `u_sub` form. -/
@[simp] lemma cosmic_formula_one_eq_sub (x : ℝ) :
    cosmic_formula_one x = cosmic_formula_u_sub x (1:ℝ) := by
  simp [cosmic_formula_one, cosmic_formula_u_sub]

-- Additional lemmas and theorems can be added here.

/-- cosmic_formula_u_sub_u0

For any commutative ring R and element x : R, substituting 0 into the second argument
of `cosmic_formula_u_sub` yields 0:

  cosmic_formula_u_sub x (0 : R) = 0

Parameters
- `R` : a type equipped with a `CommRing` instance
- `x` : an element of `R`

Proof sketch: unfold the definition of `cosmic_formula_u_sub` and finish with `ring`.
-/
@[simp] lemma cosmic_formula_u_sub_u0 {R : Type*} [CommRing R] (x : R) :
    cosmic_formula_u_sub x (0:R) = 0 := by
  unfold cosmic_formula_u_sub
  ring

/--
For any commutative ring R and element `u : R`, evaluating
`cosmic_formula_u_sub` at `x0 = 0` yields `u^2`. The equality follows
by unfolding the definition of `cosmic_formula_u_sub` and simplifying.
-/
@[simp] lemma cosmic_formula_u_sub_x0 {R : Type*} [CommRing R] (u : R) :
    cosmic_formula_u_sub (0:R) u = u^2 := by
  simp [cosmic_formula_u_sub]

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

end CosmicFormula

end DkMath
