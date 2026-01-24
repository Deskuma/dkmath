
# Theorems

see: <https://note.com/deal/n/n77bb119f4dfb>

## CosmicFormula.lean

### cosmic_formula_one

```lean
/-- A: 宇宙式 Basic Cosmic Formula -/
def cosmic_formula_one (x : ℝ) : ℝ :=
  (x + 1)^2 - x * (x + 2)
```

### cosmic_formula_one_alt

```lean
/-- A': 宇宙式 Basic Cosmic Formula Alt. -/
def cosmic_formula_one_alt (x : ℝ) : ℝ :=
  (x + 1)^2 - x^2 - 2 * x
```

### cosmic_formula_unit

```lean
/-- B: 単位宇宙式 Unit Cosmic Formula -/
def cosmic_formula_unit (x u : ℝ) : ℝ :=
  (x + u)^2 - x * (x + 2 * u)
```

### cosmic_formula_unit_alt

```lean
/-- B': 単位宇宙式 Unit Cosmic Formula Alt. -/
def cosmic_formula_unit_alt (x u : ℝ) : ℝ :=
  (x + u)^2 - x^2 - 2 * x * u
```

### cosmic_formula_unit_one

```lean
/-- C: 基本単位宇宙式 Basic Unit Cosmic Formula -/
def cosmic_formula_unit_one (x : ℝ) : ℝ :=
  cosmic_formula_unit x 1
```

### cosmic_formula_one_theorem

```lean
@[simp] theorem cosmic_formula_one_theorem (x : ℝ) : cosmic_formula_one x = 1 :=
  by
    simp [cosmic_formula_one]
    ring
```

### example#1

```lean
example : ∀ x : ℝ, cosmic_formula_one x = 1 := cosmic_formula_one_theorem
```

### cosmic_formula_unit_theorem

```lean
@[simp] theorem cosmic_formula_unit_theorem (x u : ℝ) : cosmic_formula_unit x u = u^2 :=
  by
    simp [cosmic_formula_unit]
    ring
```

### example#2

```lean
example : ∀ x u : ℝ, cosmic_formula_unit x u = u^2 := cosmic_formula_unit_theorem
```

### cosmic_formula_one_func

```lean
/-- 全ての関数 f(x) において 1 を返す -/
theorem cosmic_formula_one_func :
    ∀ (f : ℝ → ℝ) (x : ℝ), cosmic_formula_one (f x) = 1 := by
  intro f x
  simp [cosmic_formula_one_theorem]
```

### cosmic_formula_unit_func

```lean
/-- 全ての関数 f(x), g(u) において g(u) ↦ (g(u))^2 を返す -/
theorem cosmic_formula_unit_func :
    ∀ (f : ℝ → ℝ) (g : ℝ → ℝ) (x u : ℝ),
      cosmic_formula_unit (f x) (g u) = (g u)^2 := by
  intro f g x u
  simp [cosmic_formula_unit_theorem]
```

### cosmic_formula_one_add

```lean
/-- 宇宙式の 1 + 1 = 2 -/
theorem cosmic_formula_one_add :
    ∀ x y : ℝ, cosmic_formula_one x + cosmic_formula_one y = 2 := by
  intro x y
  simp only [cosmic_formula_one_theorem]
  norm_num
```

### cosmic_formula_unit_add

```lean
/-- 単位宇宙式による異なる単位の加法 -/
theorem cosmic_formula_unit_add :
    ∀ x y u v : ℝ,
      cosmic_formula_unit x u + cosmic_formula_unit y v = u^2 + v^2 := by
  intro x y u v
  simp only [cosmic_formula_unit_theorem]
```

### cosmic_formula_one_func_add

```lean
/-- 宇宙式の加法（関数版）f(x) + f(y) = 2 -/
theorem cosmic_formula_one_func_add :
    ∀ (f : ℝ → ℝ) (x y : ℝ),
      cosmic_formula_one (f x) + cosmic_formula_one (f y) = 2 := by
  intro f x y
  simp only [cosmic_formula_one_theorem]
  norm_num
```

### cosmic_formula_unit_func_add

```lean
/-- 単位宇宙式による異なる単位の加法（関数版）
  ⟨ f(x), g(u) ⟩ + ⟨ f(y), g(v) ⟩ = (g(u))^2 + (g(v))^2 -/
theorem cosmic_formula_unit_func_add :
    ∀ (f : ℝ → ℝ) (g : ℝ → ℝ) (x y u v : ℝ),
      cosmic_formula_unit (f x) (g u) + cosmic_formula_unit (f y) (g v) = (g u)^2 + (g v)^2 := by
  intro f g x y u v
  simp only [cosmic_formula_unit_theorem]
```

### cosmic_formula_unit_sub

```lean
def cosmic_formula_unit_sub {R : Type*} [CommRing R] (x u : R) : R :=
  (x + u)^2 - x * (x + 2 * u)
```

### cosmic_formula_unit_sub_eq

```lean
@[simp] theorem cosmic_formula_unit_sub_eq {R : Type*} [CommRing R] (x u : R) :
    cosmic_formula_unit_sub x u = u^2 := by
  unfold cosmic_formula_unit_sub
  ring
```

### cosmic_formula_one_sub_eq

```lean
@[simp] theorem cosmic_formula_one_sub_eq {R : Type*} [CommRing R] (x : R) :
    cosmic_formula_unit_sub x (1 : R) = 1 := by
  simp [cosmic_formula_unit_sub_eq]
```

### N

```lean
def N {R : Type*} [CommSemiring R] (x u : R) : R := x * (x + 2 * u)
```

### P

```lean
def P {R : Type*} [CommSemiring R] (x u : R) : R := (x + u)^2
```

### cosmic_formula_add

```lean
theorem cosmic_formula_add {R : Type*} [CommSemiring R] (x u : R) :
    N x u + u^2 = P x u := by
  -- 展開して終わり。ここは純粋に多項式恒等式。
  simp [N, P]
  ring
```

### cosmic_formula_sub_from_add

```lean
theorem cosmic_formula_sub_from_add {R : Type*} [CommRing R] (x u : R) :
    (P x u) - (N x u) = u^2 := by
  -- add 版から引き算して得る
  have h := cosmic_formula_add (R := R) (x := x) (u := u)
  -- N x u + u^2 = P x u  ⇒  P x u - N x u = u^2
  rw [←h]
  ring
```
