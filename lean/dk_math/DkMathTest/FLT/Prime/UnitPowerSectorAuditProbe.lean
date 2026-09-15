/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.UnitPowerSector
import DkMath.FLT.Three.EisensteinUnitSectors
import DkMath.FLT.Five.GoldenUnitClassification
import DkMath.FLT.Seven.QuadraticUnits

#print "file: DkMathTest.FLT.Prime.UnitPowerSectorAuditProbe"

namespace DkMathTest.FLT.Prime.UnitPowerSectorAuditProbe

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Three
open DkMath.FLT.Five
open DkMath.FLT.Seven

/-- The generic normalization theorem keeps the sector and exponent explicit. -/
example {R : Type*} [CommMonoidWithZero R] {p : ℕ}
    (S : UnitPowerSectorSystem R p)
    {a gamma : R} (u : Rˣ)
    (h : a = (u : R) * gamma ^ p) :
    ∃ s : S.Sector, ∃ delta : R,
      a = (S.rep s : R) * delta ^ p :=
  exists_sector_mul_pow_of_unit_mul_pow S u h

/-! The p=3 specialized theorem has the exact carrier-level shape needed for
the generic adapter.  The adapter below is test-only; the old proof remains
untouched. -/

noncomputable def eisensteinUnitSectorSystem :
    UnitPowerSectorSystem EisensteinInt 3 where
  Sector := EisensteinUnitSector
  rep := fun sector => sector.rep_isUnit.unit
  complete := by
    intro epsilon
    rcases exists_sector_mul_cube_of_unit epsilon with
      ⟨sector, delta, hdelta, hepsilon⟩
    refine ⟨sector, hdelta.unit, ?_⟩
    apply Units.ext
    change (epsilon : EisensteinInt) =
      ((sector.rep_isUnit.unit : EisensteinIntˣ) : EisensteinInt) *
        ((hdelta.unit : EisensteinIntˣ) : EisensteinInt) ^ 3
    rw [sector.rep_isUnit.unit_spec, hdelta.unit_spec]
    exact hepsilon

example (epsilon : EisensteinIntˣ) (gamma : EisensteinInt)
    (h : (epsilon : EisensteinInt) = (epsilon : EisensteinInt) * gamma ^ 3) :
    ∃ sector : eisensteinUnitSectorSystem.Sector, ∃ delta : EisensteinInt,
      (epsilon : EisensteinInt) =
        (eisensteinUnitSectorSystem.rep sector : EisensteinInt) * delta ^ 3 :=
  exists_sector_mul_pow_of_unit_mul_pow eisensteinUnitSectorSystem epsilon
    h

/-! The p=7 result is a singleton sector after the existing unit theorem. -/

noncomputable def quadraticUnitSectorSystem :
    UnitPowerSectorSystem (TraceOneInt (-2)) 7 where
  Sector := PUnit
  rep := fun _ => 1
  complete := by
    intro u
    rcases exists_seventh_power_eq_of_isUnit u.isUnit with ⟨e, he⟩
    have hepow : IsUnit (e ^ 7) := by
      rw [← he]
      exact u.isUnit
    have heunit : IsUnit e :=
      (isUnit_pow_iff (by decide : 7 ≠ 0)).mp hepow
    let E : (TraceOneInt (-2))ˣ := heunit.unit
    refine ⟨PUnit.unit, E, ?_⟩
    apply Units.ext
    change (u : TraceOneInt (-2)) =
      (1 : TraceOneInt (-2)) * (E : TraceOneInt (-2)) ^ 7
    rw [one_mul]
    rw [he, ← heunit.unit_spec]

example (u : (TraceOneInt (-2))ˣ) :
    ∃ e : TraceOneInt (-2), (u : TraceOneInt (-2)) = e ^ 7 := by
  exact exists_seventh_power_eq_of_isUnit u.isUnit

example (u : (TraceOneInt (-2))ˣ) (gamma : TraceOneInt (-2))
    (h : (u : TraceOneInt (-2)) = (u : TraceOneInt (-2)) * gamma ^ 7) :
    ∃ s : quadraticUnitSectorSystem.Sector, ∃ delta : TraceOneInt (-2),
      (u : TraceOneInt (-2)) =
        (quadraticUnitSectorSystem.rep s : TraceOneInt (-2)) * delta ^ 7 :=
  exists_sector_mul_pow_of_unit_mul_pow quadraticUnitSectorSystem u
    h

/-! p=5 remains a carrier audit only: the existing theorem is stated for the
predicate `GoldenUnit` on `GoldenInt`, not for `GoldenIntˣ`. -/

example : GoldenUnitClassesModFifth := goldenUnitClassesModFifth

#check DkMath.FLT.Five.GoldenInt
#check DkMath.FLT.Five.GoldenUnit
#check DkMath.FLT.Five.goldenUnitClassesModFifth

end DkMathTest.FLT.Prime.UnitPowerSectorAuditProbe
