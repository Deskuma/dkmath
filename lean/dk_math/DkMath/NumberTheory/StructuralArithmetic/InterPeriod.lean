/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates

#print "file: DkMath.NumberTheory.StructuralArithmetic.InterPeriod"

/-!
## Canonical forgetting between power-gauge periods

A period-`d` observation may be projected again to period `m` without changing
the result exactly when `m ∣ d`.  At one exponent coordinate this is the
standard remainder identity

```text
(n % d) % m = n % m.
```

The theorems below lift that identity to arbitrary exponent-coordinate
structures and then to prime-valuation coordinates.  They include the boundary
periods: divisibility forces `d = 0` when `m = 0`, while `m = 1` gives the
already established total collapse.  No raw coordinate source is reconstructed;
the maps only forget additional periodic information.
-/

namespace DkMath.NumberTheory.StructuralArithmetic

/--
Projecting a period-`d` exponent observation to a divisor period `m` is the
same as projecting the raw exponent directly to period `m`.
-/
@[simp] theorem projectExponent_project_of_dvd
    {m d n : ℕ} (hmd : m ∣ d) :
    projectExponent m (projectExponent d n) = projectExponent m n := by
  simpa [projectExponent] using Nat.mod_mod_of_dvd n hmd

/--
Coordinatewise projection from period `d` to a divisor period `m` agrees with
direct period-`m` projection of the retained raw coordinate structure.
-/
@[simp] theorem projectCoordinates_project_of_dvd
    {ι : Type*} {m d : ℕ} (hmd : m ∣ d) (v : ι → ℕ) :
    projectCoordinates m (projectCoordinates d v) = projectCoordinates m v := by
  funext i
  exact projectExponent_project_of_dvd hmd

namespace SamePowerSector

/--
Indistinguishability at period `d` descends to every divisor period `m`.
This is a one-way loss of information; no converse is claimed.
-/
theorem of_dvd
    {m d a b : ℕ} (hmd : m ∣ d) (h : SamePowerSector d a b) :
    SamePowerSector m a b := by
  unfold SamePowerSector at h ⊢
  calc
    projectExponent m a = projectExponent m (projectExponent d a) :=
      (projectExponent_project_of_dvd hmd).symm
    _ = projectExponent m (projectExponent d b) :=
      congrArg (projectExponent m) h
    _ = projectExponent m b := projectExponent_project_of_dvd hmd

end SamePowerSector

namespace SamePowerStructure

/--
Equality of period-`d` coordinate observations descends canonically to period
`m` whenever `m ∣ d`.  The raw functions `v` and `w` remain the sources of both
observations.
-/
theorem of_dvd
    {ι : Type*} {m d : ℕ} (hmd : m ∣ d) {v w : ι → ℕ}
    (h : SamePowerStructure d v w) :
    SamePowerStructure m v w := by
  unfold SamePowerStructure at h ⊢
  calc
    projectCoordinates m v = projectCoordinates m (projectCoordinates d v) :=
      (projectCoordinates_project_of_dvd hmd v).symm
    _ = projectCoordinates m (projectCoordinates d w) :=
      congrArg (projectCoordinates m) h
    _ = projectCoordinates m w := projectCoordinates_project_of_dvd hmd w

end SamePowerStructure

/-! ## Prime-coordinate specialization -/

/--
Reprojecting a period-`d` prime-valuation observation to a divisor period `m`
is direct period-`m` observation of the original prime valuations.
-/
@[simp] theorem projectPrimeCoordinates_coarsen_of_dvd
    {m d n : ℕ} (hmd : m ∣ d) :
    projectCoordinates m (projectPrimeCoordinates d n) =
      projectPrimeCoordinates m n := by
  unfold projectPrimeCoordinates
  exact projectCoordinates_project_of_dvd hmd (primeExponentCoordinates n)

/--
If two natural numbers have equal projected prime coordinates at period `d`,
then their projected prime coordinates are equal at every divisor period `m`.
-/
theorem projectPrimeCoordinates_eq_of_dvd
    {m d a b : ℕ} (hmd : m ∣ d)
    (h : projectPrimeCoordinates d a = projectPrimeCoordinates d b) :
    projectPrimeCoordinates m a = projectPrimeCoordinates m b := by
  calc
    projectPrimeCoordinates m a =
        projectCoordinates m (projectPrimeCoordinates d a) :=
      (projectPrimeCoordinates_coarsen_of_dvd hmd).symm
    _ = projectCoordinates m (projectPrimeCoordinates d b) :=
      congrArg (projectCoordinates m) h
    _ = projectPrimeCoordinates m b :=
      projectPrimeCoordinates_coarsen_of_dvd hmd

end DkMath.NumberTheory.StructuralArithmetic
