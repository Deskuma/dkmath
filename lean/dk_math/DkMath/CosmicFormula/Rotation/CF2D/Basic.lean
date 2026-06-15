/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.CosmicFormula.Rotation.CF2D.Basic"

/-!
# Cosmic Formula 2D rotation kernel

This file formalizes the algebraic core of the two-component rotation story:

* `Vec R` is a two-component state.
* `Vec.q2` is the two-component square mass `x^2 + y^2`.
* `Vec.star` is the unit-kernel product
  `(a,b) ⋆ (x,y) = (a*x - b*y, a*y + b*x)`.
* `Vec.q2_star` proves that the square mass is multiplicative under `⋆`.

No trigonometric function, circle theorem, or metric-space statement is used.
The central statement is a polynomial identity over an arbitrary commutative
ring.
-/

namespace DkMath
namespace CosmicFormula
namespace Rotation
namespace CF2D

/-- A two-component state, read as `(core, beam)` in the cosmic-formula vocabulary. -/
structure Vec (R : Type u) where
  core : R
  beam : R
deriving DecidableEq, Repr

namespace Vec

variable {R : Type u}

/-- The two-component square mass `core^2 + beam^2`. -/
def q2 [Semiring R] (z : Vec R) : R :=
  z.core ^ 2 + z.beam ^ 2

/-- The neutral two-component kernel `(1,0)`. -/
def one (R : Type u) [Zero R] [One R] : Vec R :=
  ⟨1, 0⟩

/--
The two-component unit-kernel product.

It is intentionally introduced as a bare algebraic operation, before any
geometric reading as rotation.
-/
def star [Ring R] (r z : Vec R) : Vec R :=
  ⟨r.core * z.core - r.beam * z.beam,
    r.core * z.beam + r.beam * z.core⟩

@[simp]
theorem q2_mk [Semiring R] (x y : R) : q2 (Vec.mk x y) = x ^ 2 + y ^ 2 := rfl

@[simp]
theorem one_core [Zero R] [One R] : (one R).core = 1 := rfl

@[simp]
theorem one_beam [Zero R] [One R] : (one R).beam = 0 := rfl

@[simp]
theorem star_core [Ring R] (r z : Vec R) :
    (star r z).core = r.core * z.core - r.beam * z.beam := rfl

@[simp]
theorem star_beam [Ring R] (r z : Vec R) :
    (star r z).beam = r.core * z.beam + r.beam * z.core := rfl

/--
Expanded square-mass form before the opposite-sign beam terms cancel.

This is the formal version of the document's calculation:
`(a*x - b*y)^2 + (a*y + b*x)^2`.
-/
theorem q2_star_expanded [CommRing R] (a b x y : R) :
    q2 (star (Vec.mk a b) (Vec.mk x y))
      = (a ^ 2 * x ^ 2 - 2 * a * b * x * y + b ^ 2 * y ^ 2)
        + (a ^ 2 * y ^ 2 + 2 * a * b * x * y + b ^ 2 * x ^ 2) := by
  simp [q2, star]
  ring

/-- The two opposite beam terms in the expanded square mass cancel. -/
theorem opposite_beam_cancel [CommRing R] (a b x y : R) :
    -(2 * a * b * x * y) + 2 * a * b * x * y = 0 := by
  ring

/--
The preservation-kernel theorem:
the square mass of a product is the product of square masses.
-/
theorem q2_star [CommRing R] (r z : Vec R) :
    q2 (star r z) = q2 r * q2 z := by
  cases r with
  | mk a b =>
      cases z with
      | mk x y =>
          simp [q2, star]
          ring

@[simp]
theorem star_one [CommRing R] (z : Vec R) : star z (one R) = z := by
  cases z with
  | mk x y =>
      simp [star, one]

@[simp]
theorem one_star [CommRing R] (z : Vec R) : star (one R) z = z := by
  cases z with
  | mk x y =>
      simp [star, one]

theorem star_assoc [CommRing R] (p q z : Vec R) :
    star (star p q) z = star p (star q z) := by
  cases p with
  | mk a b =>
      cases q with
      | mk c d =>
          cases z with
          | mk x y =>
              simp [star]
              constructor <;> ring

theorem star_comm [CommRing R] (r z : Vec R) : star r z = star z r := by
  cases r with
  | mk a b =>
      cases z with
      | mk x y =>
          simp [star]
          constructor <;> ring

end Vec

/-- A map preserves the two-component square mass. -/
def PreservesQ2 {R : Type u} [Semiring R] (f : Vec R → Vec R) : Prop :=
  ∀ z, Vec.q2 (f z) = Vec.q2 z

/--
A unit kernel is a two-component kernel whose square mass is `1`.

Its action is later read as a 2D cosmic rotation.
-/
structure UnitKernel (R : Type u) [Semiring R] where
  val : Vec R
  q2_eq_one : Vec.q2 val = 1

namespace UnitKernel

variable {R : Type u}

instance [Semiring R] : Coe (UnitKernel R) (Vec R) :=
  ⟨UnitKernel.val⟩

@[simp]
theorem coe_q2 [Semiring R] (r : UnitKernel R) : Vec.q2 (r : Vec R) = 1 :=
  r.q2_eq_one

@[ext]
theorem ext [Semiring R] {r s : UnitKernel R} (h : (r : Vec R) = (s : Vec R)) : r = s := by
  cases r with
  | mk rv hr =>
      cases s with
      | mk sv hs =>
          cases h
          rfl

/-- The neutral unit kernel `(1,0)`. -/
def one (R : Type u) [CommRing R] : UnitKernel R :=
  ⟨Vec.one R, by simp [Vec.q2, Vec.one]⟩

/-- Product of two unit kernels. -/
def star [CommRing R] (r s : UnitKernel R) : UnitKernel R :=
  ⟨Vec.star (r : Vec R) (s : Vec R), by
    rw [Vec.q2_star, coe_q2, coe_q2, one_mul]⟩

@[simp]
theorem star_val [CommRing R] (r s : UnitKernel R) :
    (star r s : Vec R) = Vec.star (r : Vec R) (s : Vec R) := rfl

@[simp]
theorem star_q2 [CommRing R] (r s : UnitKernel R) : Vec.q2 (star r s : Vec R) = 1 :=
  coe_q2 (star r s)

@[simp]
theorem star_one [CommRing R] (r : UnitKernel R) : star r (one R) = r := by
  cases r with
  | mk val q2_eq_one =>
      simp [star, one]

@[simp]
theorem one_star [CommRing R] (r : UnitKernel R) : star (one R) r = r := by
  cases r with
  | mk val q2_eq_one =>
      simp [star, one]

theorem star_assoc [CommRing R] (p q r : UnitKernel R) :
    star (star p q) r = star p (star q r) := by
  cases p with
  | mk pv hp =>
      cases q with
      | mk qv hq =>
          cases r with
          | mk rv hr =>
              simp [star, Vec.star_assoc]

theorem star_comm [CommRing R] (r s : UnitKernel R) : star r s = star s r := by
  cases r with
  | mk rv hr =>
      cases s with
      | mk sv hs =>
          simp [star, Vec.star_comm]

/-- The action of a unit kernel on a two-component state. -/
def act [CommRing R] (r : UnitKernel R) (z : Vec R) : Vec R :=
  Vec.star (r : Vec R) z

@[simp]
theorem act_one [CommRing R] (z : Vec R) : act (one R) z = z := by
  simp [act, one]

theorem act_star [CommRing R] (r s : UnitKernel R) (z : Vec R) :
    act (star r s) z = act r (act s z) := by
  change Vec.star ((star r s : UnitKernel R) : Vec R) z
      = Vec.star (r : Vec R) (Vec.star (s : Vec R) z)
  rw [star_val]
  exact Vec.star_assoc (r : Vec R) (s : Vec R) z

@[simp]
theorem act_core [CommRing R] (r : UnitKernel R) (z : Vec R) :
    (act r z).core = (r : Vec R).core * z.core - (r : Vec R).beam * z.beam := rfl

@[simp]
theorem act_beam [CommRing R] (r : UnitKernel R) (z : Vec R) :
    (act r z).beam = (r : Vec R).core * z.beam + (r : Vec R).beam * z.core := rfl

/-- A unit-kernel action preserves the two-component square mass. -/
theorem q2_act [CommRing R] (r : UnitKernel R) (z : Vec R) :
    Vec.q2 (act r z) = Vec.q2 z := by
  rw [act, Vec.q2_star, coe_q2, one_mul]

theorem preservesQ2_act [CommRing R] (r : UnitKernel R) : PreservesQ2 (act r) :=
  q2_act r

end UnitKernel

/--
The level set of the square mass `q2 = rho2`.

This is the algebraic object that later receives the geometric name "circle".
-/
def LevelSet (R : Type u) [Semiring R] (rho2 : R) :=
  { z : Vec R // Vec.q2 z = rho2 }

namespace LevelSet

variable {R : Type u} [CommRing R] {rho2 : R}

/-- Unit-kernel action stays inside every square-mass level set. -/
def act (r : UnitKernel R) (z : LevelSet R rho2) : LevelSet R rho2 :=
  ⟨UnitKernel.act r z.1, by
    have h := UnitKernel.q2_act r z.1
    simpa [z.2] using h⟩

@[simp]
theorem act_val (r : UnitKernel R) (z : LevelSet R rho2) :
    (act r z).1 = UnitKernel.act r z.1 := rfl

end LevelSet

end CF2D
end Rotation
end CosmicFormula
end DkMath
