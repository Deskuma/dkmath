/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Nat.Basic

#print "file: DkMath.NumberTheory.StructuralArithmetic.PowerGauge"

/-!
## Power-gauge structural projection

This module is the first Lean kernel for the DkMath red-ribbon / structural
arithmetic integration.

The central distinction is between a raw exponent structure and a period-`d`
observation of that structure.  The projection

```text
n |-> n % d
```

forgets additions by whole `d`-periods.  Coordinatewise, this gives the
minimal abstract model for prime-valuation vectors before any dependency on a
specific factorization API is introduced.

Two boundary cases are intentionally theorem-level facts:

- period `0` is the identity/unprojected view because `n % 0 = n`;
- period `1` collapses all exponent coordinates because `n % 1 = 0`.

Thus an ordinary raw prime world must not be identified with a `mod 1`
quotient.  KUS remains the DkMath layer for retaining source/support structure;
this module only defines the observation/projection kernel.
-/

namespace DkMath.NumberTheory.StructuralArithmetic

/-- Observable exponent coordinate at gauge period `d`. -/
def projectExponent (d n : ℕ) : ℕ :=
  n % d

/-- Two exponent coordinates occupy the same visible period-`d` sector. -/
def SamePowerSector (d a b : ℕ) : Prop :=
  projectExponent d a = projectExponent d b

@[simp] theorem projectExponent_period_zero (n : ℕ) :
    projectExponent 0 n = n := by
  simp [projectExponent]

@[simp] theorem projectExponent_period_one (n : ℕ) :
    projectExponent 1 n = 0 := by
  simp [projectExponent]

/--
Red-ribbon law for one exponent coordinate: adding whole gauge periods does not
change the visible sector.
-/
@[simp] theorem projectExponent_add_period (d n k : ℕ) :
    projectExponent d (n + d * k) = projectExponent d n := by
  simpa [projectExponent] using Nat.add_mul_mod_self_left n d k

/-- A pure multiple of the gauge period projects to the zero sector. -/
@[simp] theorem projectExponent_period_mul (d k : ℕ) :
    projectExponent d (d * k) = 0 := by
  simpa [projectExponent] using Nat.mul_mod_right d k

namespace SamePowerSector

@[refl] theorem refl (d a : ℕ) : SamePowerSector d a a :=
  rfl

@[symm] theorem symm {d a b : ℕ} (h : SamePowerSector d a b) :
    SamePowerSector d b a :=
  h.symm

@[trans] theorem trans {d a b c : ℕ}
    (hab : SamePowerSector d a b) (hbc : SamePowerSector d b c) :
    SamePowerSector d a c :=
  hab.trans hbc

/-- Period zero retains exact exponent information. -/
@[simp] theorem period_zero_iff {a b : ℕ} :
    SamePowerSector 0 a b ↔ a = b := by
  simp [SamePowerSector]

/-- Period one collapses every pair of exponent coordinates to one sector. -/
@[simp] theorem period_one (a b : ℕ) :
    SamePowerSector 1 a b := by
  simp [SamePowerSector]

/-- Red-ribbon law stated as sector equivalence. -/
theorem add_period (d n k : ℕ) :
    SamePowerSector d n (n + d * k) := by
  unfold SamePowerSector
  exact (projectExponent_add_period d n k).symm

end SamePowerSector

/-! ## Coordinatewise structural projection -/

/--
Project every exponent coordinate through the same gauge period.

The index type `ι` is intentionally abstract.  A later prime-coordinate bridge
will specialize `ι` to prime directions and the coordinate function to
valuations.
-/
def projectCoordinates {ι : Type*} (d : ℕ) (v : ι → ℕ) : ι → ℕ :=
  fun i => projectExponent d (v i)

/-- Two raw coordinate structures have the same period-`d` observation. -/
def SamePowerStructure {ι : Type*} (d : ℕ) (v w : ι → ℕ) : Prop :=
  projectCoordinates d v = projectCoordinates d w

@[simp] theorem projectCoordinates_period_zero {ι : Type*} (v : ι → ℕ) :
    projectCoordinates 0 v = v := by
  funext i
  simp [projectCoordinates]

@[simp] theorem projectCoordinates_period_one {ι : Type*} (v : ι → ℕ) :
    projectCoordinates 1 v = fun _ => 0 := by
  funext i
  simp [projectCoordinates]

/--
Coordinatewise red-ribbon law: adding `d * k i` in every direction leaves the
period-`d` observation unchanged.
-/
theorem projectCoordinates_add_period {ι : Type*}
    (d : ℕ) (v k : ι → ℕ) :
    projectCoordinates d (fun i => v i + d * k i) =
      projectCoordinates d v := by
  funext i
  exact projectExponent_add_period d (v i) (k i)

namespace SamePowerStructure

@[refl] theorem refl {ι : Type*} (d : ℕ) (v : ι → ℕ) :
    SamePowerStructure d v v :=
  rfl

@[symm] theorem symm {ι : Type*} {d : ℕ} {v w : ι → ℕ}
    (h : SamePowerStructure d v w) :
    SamePowerStructure d w v :=
  h.symm

@[trans] theorem trans {ι : Type*} {d : ℕ} {u v w : ι → ℕ}
    (huv : SamePowerStructure d u v)
    (hvw : SamePowerStructure d v w) :
    SamePowerStructure d u w :=
  huv.trans hvw

/-- Period zero is equality of the complete raw coordinate structure. -/
@[simp] theorem period_zero_iff {ι : Type*} {v w : ι → ℕ} :
    SamePowerStructure 0 v w ↔ v = w := by
  simp [SamePowerStructure]

/-- Period one forgets every exponent coordinate. -/
@[simp] theorem period_one {ι : Type*} (v w : ι → ℕ) :
    SamePowerStructure 1 v w := by
  simp [SamePowerStructure]

/--
The coordinatewise red-ribbon theorem: whole gauge-period motion is invisible
to the projected observer while the raw source remains available separately.
-/
theorem add_period {ι : Type*} (d : ℕ) (v k : ι → ℕ) :
    SamePowerStructure d v (fun i => v i + d * k i) := by
  unfold SamePowerStructure
  exact (projectCoordinates_add_period d v k).symm

end SamePowerStructure

end DkMath.NumberTheory.StructuralArithmetic
