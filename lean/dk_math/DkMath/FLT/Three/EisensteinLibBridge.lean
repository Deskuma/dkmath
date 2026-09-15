/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Three.EisensteinUnitSectors
import DkMath.Lib.NumberTheory.EisensteinCoordinates
import DkMath.Lib.NumberTheory.UnitPowerSector
import DkMath.NumberTheory.PrimeQuadraticDiscriminant

#print "file: DkMath.FLT.Three.EisensteinLibBridge"

/-!
# FLT3 compatibility with the promoted Eisenstein API

The FLT3 carrier and the generic p=3 TraceOne carrier are both
`TraceOneInt (-1)`.  This bridge records that definitional carrier alignment,
the omega/tau coordinate sign conversion, and the existing FLT3 cube-unit
sectors through the neutral `UnitPowerSectorSystem` interface.
-/

namespace DkMath.FLT.Three

open DkMath.Lib.NumberTheory
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic

local notation "tqNorm" => DkMath.NumberTheory.TraceOneQuadratic.norm

/-- The generic p=3 carrier is definitionally the FLT3 carrier after the
signed-parameter computation. -/
theorem traceOneInt_signedPrimeParameter_three_type :
    TraceOneInt (signedPrimeParameter 3) = TraceOneInt (-1) := by
  rw [signedPrimeParameter_three]

/-- The Lib omega convention equals the FLT3 tau convention after negating the
second coordinate. -/
theorem lib_eisensteinCoord_eq_FLT3_coord (m n : ℤ) :
    DkMath.Lib.NumberTheory.eisensteinCoord m n =
      DkMath.FLT.Three.eisensteinCoord m (-n) := rfl

/-- The neutral norm is unchanged by the omega/tau coordinate conversion. -/
theorem lib_eisensteinCoord_norm_eq_FLT3_coord_norm (m n : ℤ) :
    tqNorm (DkMath.Lib.NumberTheory.eisensteinCoord m n) =
      tqNorm (DkMath.FLT.Three.eisensteinCoord m (-n)) := rfl

/-- The existing three FLT3 cube-unit sectors as a generic unit-power system. -/
noncomputable def eisensteinCubeUnitPowerSectorSystem :
    UnitPowerSectorSystem (TraceOneInt (-1)) 3 := {
  Sector := EisensteinUnitSector
  rep := fun sector => (EisensteinUnitSector.rep_isUnit sector).unit
  complete := by
    intro u
    rcases exists_sector_mul_cube_of_unit u with
      ⟨sector, delta, hdelta, hEq⟩
    let e : (TraceOneInt (-1))ˣ := hdelta.unit
    refine ⟨sector, e, ?_⟩
    apply Units.ext
    change (u : TraceOneInt (-1)) =
      ((EisensteinUnitSector.rep_isUnit sector).unit : TraceOneInt (-1)) *
        (e : TraceOneInt (-1)) ^ 3
    rw [hEq]
    simp [e]
}

/-- Completeness of the promoted p=3 unit-sector system. -/
theorem eisensteinCubeUnitPowerSectorSystem_complete
    (u : (TraceOneInt (-1))ˣ) :
    ∃ s : EisensteinUnitSector, ∃ e : (TraceOneInt (-1))ˣ,
      u = eisensteinCubeUnitPowerSectorSystem.rep s * e ^ 3 := by
  exact eisensteinCubeUnitPowerSectorSystem.complete u

end DkMath.FLT.Three

#print axioms DkMath.FLT.Three.traceOneInt_signedPrimeParameter_three_type
#print axioms DkMath.FLT.Three.lib_eisensteinCoord_eq_FLT3_coord
#print axioms DkMath.FLT.Three.lib_eisensteinCoord_norm_eq_FLT3_coord_norm
#print axioms DkMath.FLT.Three.eisensteinCubeUnitPowerSectorSystem_complete
