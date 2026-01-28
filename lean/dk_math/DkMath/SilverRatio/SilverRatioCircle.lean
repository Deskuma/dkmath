/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

/-
# Analytic coordinate development for the White-Silver-Ratio circle (overview)

This file gives a compact, elementary coordinate setup and proves a single
geometric fact: the four points B, C, F, G are concyclic for a specific
unit–square construction.  The development is intentionally minimal and
self-contained: points are represented as plain Euclidean coordinates
(Point = ℝ × ℝ) and all distance reasoning is performed with squared
distances to avoid introducing explicit square roots in proofs.

## File structure and main ideas

- Imports and global setup
  - `Mathlib` is imported and `noncomputable section` is used to allow
    noncomputable real constants such as `Real.sqrt`.
  - `open Real` is used to bring real arithmetic lemmas into scope.
  - Everything is placed in the `SilverRatio` namespace.

- Basic types and operations
  - `Point` is an abbreviation for `ℝ × ℝ`.
  - Coordinate projections `x`, `y` and basic vector operations
    `add`, `sub`, `scale` are defined for readability.
  - `dist_sq` is the squared Euclidean distance between two points;
    using squared distances avoids the need for square roots in equalities.
  - `rotate90` is provided as a helper for 90° rotation (used in point
    constructions).

- Fixed geometric data: unit square and derived points
  - The unit square is represented by the points A(0,0), B(1,0), C(1,1),
    D(0,1).
  - `sqrt2` is defined as `Real.sqrt 2`, together with a set of lemmas
    about its basic algebraic properties:
    - `sqrt2_sq : sqrt2 ^ 2 = 2`
    - `sqrt2_pos`, `sqrt2_ne_zero`, `sqrt2_irrational`
    - rationalizations and reciprocal identities such as
      `sqrt2_inv` and `one_div_sqrt2`, and `(sqrt2 / 2)^2 = 1/2`.
  - The point `E` is the intersection of the diagonal `y = x` with the
    unit circle centered at `A` (explicitly `(1 / sqrt2, 1 / sqrt2)`).
  - Other construction points `F`, `G` and an explicit center `O` are
    given by coordinates chosen so that the intended concyclicity result
    holds.  (The chosen `O` is `((sqrt2 - 1) / 2, 1 / 2)` in the file.)

- Predicate for concyclicity
  - `concyclic4` is a simple predicate asserting that four points lie
    on a common circle: there exists a center `O` and squared radius `r2`
    with equal `dist_sq` to each of the four points.

- Main theorem
  - `bcfg_concyclic : concyclic4 B C F G` exhibits the center `O` and
    proves that `dist_sq O B = dist_sq O C = dist_sq O F = dist_sq O G`.
  - Proof strategy:
    - The proof uses `dist_sq` equalities so square roots are never
      needed explicitly.
    - Algebraic simplification is performed using tactics such as
      `dsimp`, `norm_num`, `field_simp`, `ring`, and `linarith`.
    - The central arithmetic reductions repeatedly use `sqrt2_sq` to
      replace `sqrt2 ^ 2` with `2`, allowing all expressions to be
      simplified to rational combinations of `sqrt2` and constants.
    - For one equality the file uses a short automation step (`grind
      only`) to finish the remaining algebraic verification.

## Design choices and remarks

- Why squared distances?  Replacing distances by their squares keeps
  the algebra purely polynomial (involving √2 only in degree ≤1 after
  simplification), which simplifies symbolic manipulation in Lean and
  avoids dealing with `Real.sqrt` cancellation and sign issues.
- Elementary coordinate approach: this file purposefully avoids metric
  or synthetic geometry libraries and builds the necessary geometric
  facts directly from real arithmetic. This makes the file small and
  readable, which is convenient for an introductory development or for
  embedding into a larger analytic treatment.
- Proof style: lemmas about `sqrt2` centralize algebraic identities
  (`sqrt2_sq`, `sqrt2_inv`, etc.), making later steps short and clearly
  justified. Using `dsimp` and `ring` on polynomial expressions keeps
  calculations easy to follow.
- Possible extensions:
  - Replace explicit coordinate algebra with `euclidean_geometry` or
    `metric` abstractions from mathlib for more general theorems.
  - Generalize the construction to handle other similar ratio circles
    and provide a library of reusable algebraic lemmas for expressions
    involving √2 (or other square roots).

## How to read the proofs

- The key equalities are pure algebraic manipulations of rational
  combinations of `sqrt2`. When you see `dsimp [dist_sq, O, ...]`, Lean
  simply unfolds definitions to obtain concrete polynomial expressions.
- `norm_num` and `field_simp` are used to clear denominators and perform
  numerical simplifications; `ring` normalizes polynomial expressions;
  `linarith` solves linear inequalities or linear equalities where
  applicable.
- The final `grind only` invocation is an automated simplifier used to
  discharge a remaining algebraic goal; it can be replaced by an
  explicit chain of `ring`/`field_simp` steps if desired for clarity.

This file is suitable as a concise example of coordinate reasoning in
Lean: it demonstrates how to represent simple Euclidean geometry, avoid
square roots by working with squared distances, and carry out routine
algebraic verifications with the standard tactic toolbox.
-/

import Mathlib
import DkMath.SilverRatio.Sqrt2Lemmas

/-!
Analytic coordinate development for the White-Silver-Ratio circle.

This file provides a minimal, self-contained coordinate setup and a
first theorem: B, C, F, G are concyclic for the unit-square construction.

The development intentionally stays elementary: `Point` is `ℝ × ℝ` and
we reason about squared distances to avoid unnecessary square roots.
-/

noncomputable section

open Real

namespace DkMath.SilverRatio.SilverRatioCircle

open DkMath.SilverRatio.Sqrt2

abbrev Point := ℝ × ℝ

def x (p : Point) : ℝ := p.fst
def y (p : Point) : ℝ := p.snd

def add (p q : Point) : Point := (p.fst + q.fst, p.snd + q.snd)
def sub (p q : Point) : Point := (p.fst - q.fst, p.snd - q.snd)
def scale (a : ℝ) (p : Point) : Point := (a * p.fst, a * p.snd)

def dist_sq (p q : Point) : ℝ := (p.fst - q.fst) ^ 2 + (p.snd - q.snd) ^ 2

def rotate90 (v : Point) : Point := (-v.snd, v.fst)

-- Unit square A(0,0), B(1,0), C(1,1), D(0,1)
def A : Point := (0, 0)
def B : Point := (1, 0)
def C : Point := (1, 1)
def D : Point := (0, 1)

-- Intersection E of diagonal y = x and circle centered at A radius 1


-- Intersection E of diagonal y = x and circle centered at A radius 1
-- Direct coordinate definition: E = (1/sqrt2, 1/sqrt2)
def E : Point := (1 / sqrt2, 1 / sqrt2)

-- For F and G, we'll compute them via rotate90
def vAE : Point := E
def F : Point := (0, sqrt2)
def G : Point := (-1 / sqrt2, 1 / sqrt2)

-- explicit center O
def O : Point := ((sqrt2 - 1) / 2, 1 / 2)

/-- Predicate: four points are concyclic if there exists a center O and radius r
        such that all four squared distances equal r^2. -/
def concyclic4 (P Q R S : Point) : Prop :=
  ∃ (O : Point) (r2 : ℝ), dist_sq O P = r2 ∧ dist_sq O Q = r2 ∧ dist_sq O R = r2 ∧ dist_sq O S = r2

theorem bcfg_concyclic : concyclic4 B C F G := by
  use O, dist_sq O B
  refine ⟨rfl, ?_, ?_, ?_⟩
  · -- dist_sq O C = dist_sq O B
    dsimp [dist_sq, O, C, B]
    norm_num [sqrt2]
  · -- dist_sq O F = dist_sq O B
    dsimp [dist_sq, O, F, B]
    -- Both sides are polynomials in √2; use sqrt2_sq to reduce
    have h := sqrt2_sq
    suffices ((sqrt2 - 1) / 2) ^ 2 + (1 / 2 - sqrt2) ^ 2 =
             ((sqrt2 - 1) / 2 - 1) ^ 2 + (1 / 2) ^ 2 by
      convert this using 1 <;> simp [sub_zero]
    calc ((sqrt2 - 1) / 2) ^ 2 + (1 / 2 - sqrt2) ^ 2
        = (sqrt2 ^ 2 - 2 * sqrt2 + 1) / 4 + (1 - 4 * sqrt2 + 4 * sqrt2 ^ 2) / 4 := by ring
      _ = (2 - 2 * sqrt2 + 1 + 1 - 4 * sqrt2 + 4 * 2) / 4 := by rw [h]; ring
      _ = (12 - 6 * sqrt2) / 4 := by ring
      _ = ((sqrt2 - 3) / 2) ^ 2 + 1 / 4 := by
          rw [show ((sqrt2 - 3) / 2) ^ 2 = (sqrt2 ^ 2 - 6 * sqrt2 + 9) / 4 by ring]
          rw [h]
          ring
      _ = ((sqrt2 - 1) / 2 - 1) ^ 2 + (1 / 2) ^ 2 := by ring
  · -- dist_sq O G = dist_sq O B
    -- O = ((√2-1)/2, 1/2), G = (-1/√2, 1/√2), B = (1, 0)
    -- dist_sq O G = ((√2-1)/2 + 1/√2)² + (1/2 - 1/√2)²
    -- After rational simplification: (12 - 6√2)/4 = 3 - 3√2/2 ✓
    dsimp [dist_sq, O, G, B]
    have h_ne := sqrt2_ne_zero
    have h_sq := sqrt2_sq
    -- ここで grind で通るが、手動で証明を書くと以下のようになる
    field_simp [h_ne]
    calc (sqrt2 * (sqrt2 - 1) - -2) ^ 2 + (sqrt2 - 2) ^ 2
        = (sqrt2 ^ 2 - sqrt2 + 2) ^ 2 + (sqrt2 - 2) ^ 2 := by ring
      _ = (2 - sqrt2 + 2) ^ 2 + (sqrt2 - 2) ^ 2 := by rw [h_sq]
      _ = (4 - sqrt2) ^ 2 + (sqrt2 - 2) ^ 2 := by ring
      _ = 16 - 8 * sqrt2 + sqrt2 ^ 2 + sqrt2 ^ 2 - 4 * sqrt2 + 4 := by ring
      _ = 16 - 8 * sqrt2 + 2 + 2 - 4 * sqrt2 + 4 := by rw [h_sq]
      _ = 24 - 12 * sqrt2 := by ring
      _ = 2 * (12 - 6 * sqrt2) := by ring
      _ = 2 * ((sqrt2 - 1 - 2) ^ 2 + (1 - 2 * 0) ^ 2) := by
          have : (sqrt2 - 1 - 2) ^ 2 + (1 - 2 * 0) ^ 2 = 12 - 6 * sqrt2 := by
            calc (sqrt2 - 1 - 2) ^ 2 + (1 - 2 * 0) ^ 2
                = (sqrt2 - 3) ^ 2 + 1 := by ring
              _ = sqrt2 ^ 2 - 6 * sqrt2 + 9 + 1 := by ring
              _ = 2 - 6 * sqrt2 + 9 + 1 := by rw [h_sq]
              _ = 12 - 6 * sqrt2 := by ring
          rw [this]
      _ = sqrt2 ^ 2 * ((sqrt2 - 1 - 2) ^ 2 + (1 - 2 * 0) ^ 2) := by rw [h_sq]


end DkMath.SilverRatio.SilverRatioCircle

/- End of analytic development -/
