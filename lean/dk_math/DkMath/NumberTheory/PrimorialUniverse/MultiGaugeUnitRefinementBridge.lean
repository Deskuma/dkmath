/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.NumberTheory.MultiGauge.RawNormalization
import DkMath.NumberTheory.PrimorialUniverse.UnitCoordinateRefinement

#print "file: DkMath.NumberTheory.PrimorialUniverse.MultiGaugeUnitRefinementBridge"

/-!
# PUU bridge for raw multi-gauge unit refinement

This module connects the existing real-unit coordinate refinement to the raw
multi-gauge layer.  The generic multi-gauge module remains independent of
PrimorialUniverse: only this bridge knows that the synchronized raw pair is
the coordinate pair of two unchanged absolute points.
-/

namespace DkMath.NumberTheory.PrimorialUniverse

open DkMath.NumberTheory.MultiGauge

/-! ## Raw coordinate packets -/

/-- The raw stage represented by two coarse natural coordinates. -/
def coarseRawStage (d x u : ℕ) : GNRawGaugeStage d :=
  { x := x
    u := u }

/-- The raw stage represented by the refined coordinates. -/
def refinedRawStage (d k x u : ℕ) : GNRawGaugeStage d :=
  { x := x * k
    u := u * k }

/-- Two absolute points retain their values while their natural coordinates
are synchronously multiplied by the unit-refinement factor. -/
theorem unitRefinement_raw_stage_packet
    {fine coarse : PositiveUnit} {d k x u : ℕ} {X Y : ℝ}
    (href : UnitRefinesBy fine coarse k)
    (hX : HasUnitCoordinate coarse x X)
    (hY : HasUnitCoordinate coarse u Y) :
    HasUnitCoordinate fine (x * k) X ∧
      HasUnitCoordinate fine (u * k) Y ∧
      refinedRawStage d k x u =
        GNRawGaugeStage.scaleBy k (coarseRawStage d x u) := by
  refine ⟨unitCoordinate_refine href hX, unitCoordinate_refine href hY, ?_⟩
  simp [refinedRawStage, coarseRawStage, GNRawGaugeStage.scaleBy, Nat.mul_comm]

/-! ## Prime-support transport -/

/-- A prime newly captured by the refined raw observer, after escaping the
coarse raw observer, must divide the common refinement factor. -/
theorem prime_dvd_refinement_factor_of_rawEscape_of_refinedCaught
    {d q k x u : ℕ} (hq : Nat.Prime q)
    (hEscape : RawPrimeEscapes q (coarseRawStage d x u))
    (hCaught : RawPrimeCaught q (refinedRawStage d k x u)) :
    q ∣ k := by
  apply prime_dvd_scale_factor_of_rawEscape_of_scaledCaught hq
    (coarseRawStage d x u) hEscape
  simpa [refinedRawStage, coarseRawStage, GNRawGaugeStage.scaleBy, Nat.mul_comm]
    using hCaught

/-- Unit-coordinate and raw-observer consequences can be carried together in
one refinement packet. -/
theorem unitRefinement_raw_capture_packet
    {fine coarse : PositiveUnit} {d q k x u : ℕ} {X Y : ℝ}
    (href : UnitRefinesBy fine coarse k)
    (hX : HasUnitCoordinate coarse x X)
    (hY : HasUnitCoordinate coarse u Y)
    (hq : Nat.Prime q)
    (hEscape : RawPrimeEscapes q (coarseRawStage d x u))
    (hCaught : RawPrimeCaught q (refinedRawStage d k x u)) :
    HasUnitCoordinate fine (x * k) X ∧
      HasUnitCoordinate fine (u * k) Y ∧
      q ∣ k := by
  have hcoords := unitRefinement_raw_stage_packet (d := d) href hX hY
  refine ⟨hcoords.1, hcoords.2.1, ?_⟩
  exact prime_dvd_refinement_factor_of_rawEscape_of_refinedCaught hq
    hEscape hCaught

/-! ## Concrete bridge regression -/

theorem regression_unit_refinement_raw_stage_packet :
    UnitRefinesBy fineUnitOne coarseUnitFive 5 ∧
      HasUnitCoordinate coarseUnitFive 1 5 ∧
      HasUnitCoordinate fineUnitOne (1 * 5) 5 ∧
      refinedRawStage 2 5 1 2 =
        GNRawGaugeStage.scaleBy 5 (coarseRawStage 2 1 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [UnitRefinesBy, fineUnitOne, coarseUnitFive]
  · norm_num [HasUnitCoordinate, coarseUnitFive]
  · exact unitCoordinate_refine
      (fine := fineUnitOne) (coarse := coarseUnitFive) (k := 5) (n := 1) (X := 5)
      (by norm_num [UnitRefinesBy, fineUnitOne, coarseUnitFive])
      (by norm_num [HasUnitCoordinate, coarseUnitFive])
  · simp [refinedRawStage, coarseRawStage, GNRawGaugeStage.scaleBy, Nat.mul_comm]

end DkMath.NumberTheory.PrimorialUniverse
