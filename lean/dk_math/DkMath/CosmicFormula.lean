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

-- 単位宇宙式の恒等式を証明する例
theorem example_theorem_u (x u : ℝ) : cosmic_formula_u x u = u^2 :=
  by
    simp [cosmic_formula_u]
    ring

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

end CosmicFormula

end DkMath
