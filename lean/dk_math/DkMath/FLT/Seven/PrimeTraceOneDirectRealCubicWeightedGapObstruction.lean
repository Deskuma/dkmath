/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicLocalClass

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicWeightedGapObstruction"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ## Direct scalar residue of the transport unit -/

theorem directOrbitPairAxisUnitOne_thetaResidue :
    thetaResidue (directOrbitPairAxisUnitOne : SevenRealCubicInt) = 4 := by
  rw [directOrbitPairAxisUnitOne_val,
    pairAxisUnit_thetaResidue_eq_pairPhase, pairPhase_one_val]

/-! The projective-log exponent is reduced modulo `7`, whereas this scalar
residue calculation uses the multiplicative period `6` of the nonzero field
`ZMod 7`. -/

theorem directOrbit_twistedExponent_thetaResidue (k : ℕ) :
    (4 : ZMod 7) ^ (32 + 42 * k) = 2 := by
  have he : 32 + 42 * k = 2 + 6 * (5 + 7 * k) := by omega
  have hsix : (4 : ZMod 7) ^ 6 = 1 := by decide
  rw [he, pow_add, pow_mul]
  rw [hsix]
  norm_num
  decide

theorem thetaResidue_coe_unit_ne_zero (u : SevenRealCubicIntˣ) :
    thetaResidue (u : SevenRealCubicInt) ≠ 0 := by
  intro hu
  have hmul :
      thetaResidue (u : SevenRealCubicInt) *
          thetaResidue ((u⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) = 1 := by
    rw [← map_mul]
    simp
  rw [hu, zero_mul] at hmul
  exact one_ne_zero hmul.symm

theorem thetaResidue_coe_unit_inv (u : SevenRealCubicIntˣ) :
    thetaResidue ((u⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) =
      (thetaResidue (u : SevenRealCubicInt))⁻¹ := by
  have hmul :
      thetaResidue (u : SevenRealCubicInt) *
          thetaResidue ((u⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) = 1 := by
    rw [← map_mul]
    simp
  exact eq_inv_of_mul_eq_one_right hmul

theorem directOrbit_twistedCoeff1_thetaResidue_eq_transport_mul
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    thetaResidue (directOrbitTwistedCoeff1 s : SevenRealCubicInt) =
    thetaResidue (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^
          (32 + 42 * s.gapSplit.k) *
        thetaResidue (directOrbitTwistedCoeff0 s : SevenRealCubicInt) := by
  rw [directOrbitTwistedCoeff1, Units.val_mul, Units.val_pow_eq_pow_val,
    map_mul, map_pow,
    directOrbitRotateUnit_val, thetaResidue_rotateEquiv]
  rfl

theorem directOrbit_twistedCoeff1_thetaResidue_ratio
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    thetaResidue
      ((directOrbitTwistedCoeff1 s *
        (directOrbitTwistedCoeff0 s)⁻¹ : SevenRealCubicInt)) = 2 := by
  have h0 := thetaResidue_coe_unit_ne_zero (directOrbitTwistedCoeff0 s)
  rw [map_mul, thetaResidue_coe_unit_inv,
    directOrbit_twistedCoeff1_thetaResidue_eq_transport_mul s,
    directOrbitPairAxisUnitOne_thetaResidue,
    directOrbit_twistedExponent_thetaResidue]
  simp [h0]

/-! ## The coefficient difference is a theta-unit -/

theorem directOrbit_twistedCoeff1_sub_coeff0_thetaResidue_ne_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    thetaResidue
      ((directOrbitTwistedCoeff1 s : SevenRealCubicInt) -
        (directOrbitTwistedCoeff0 s : SevenRealCubicInt)) ≠ 0 := by
  have h0 := thetaResidue_coe_unit_ne_zero (directOrbitTwistedCoeff0 s)
  have hratio := directOrbit_twistedCoeff1_thetaResidue_ratio s
  rw [map_mul, thetaResidue_coe_unit_inv] at hratio
  have hrel :
      thetaResidue (directOrbitTwistedCoeff1 s : SevenRealCubicInt) =
        2 * thetaResidue (directOrbitTwistedCoeff0 s : SevenRealCubicInt) := by
    calc
      thetaResidue (directOrbitTwistedCoeff1 s : SevenRealCubicInt) =
          thetaResidue (directOrbitTwistedCoeff1 s : SevenRealCubicInt) *
            ((thetaResidue (directOrbitTwistedCoeff0 s : SevenRealCubicInt))⁻¹ *
              thetaResidue (directOrbitTwistedCoeff0 s : SevenRealCubicInt)) := by
                rw [inv_mul_cancel₀ h0, mul_one]
      _ = 2 * thetaResidue (directOrbitTwistedCoeff0 s : SevenRealCubicInt) := by
        rw [← mul_assoc, hratio]
  intro hz
  rw [map_sub] at hz
  have heq :
      thetaResidue (directOrbitTwistedCoeff1 s : SevenRealCubicInt) =
        thetaResidue (directOrbitTwistedCoeff0 s : SevenRealCubicInt) :=
    sub_eq_zero.mp hz
  have hzero : thetaResidue (directOrbitTwistedCoeff0 s : SevenRealCubicInt) = 0 := by
    rw [heq] at hrel
    have hsub := sub_eq_zero.mpr hrel
    have hneg :
        -thetaResidue (directOrbitTwistedCoeff0 s : SevenRealCubicInt) = 0 := by
      calc
        -thetaResidue (directOrbitTwistedCoeff0 s : SevenRealCubicInt) =
            thetaResidue (directOrbitTwistedCoeff0 s : SevenRealCubicInt) -
              2 * thetaResidue (directOrbitTwistedCoeff0 s : SevenRealCubicInt) := by
                ring
        _ = 0 := hsub
    exact neg_eq_zero.mp hneg
  exact h0 hzero

theorem directOrbit_twistedCoeff1_sub_coeff0_not_axis_dvd
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    ¬eisensteinAxis ∣
      ((directOrbitTwistedCoeff1 s : SevenRealCubicInt) -
        (directOrbitTwistedCoeff0 s : SevenRealCubicInt)) := by
  intro hd
  apply directOrbit_twistedCoeff1_sub_coeff0_thetaResidue_ne_zero s
  exact (eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero _).mp hd

/-! ## The transported root gap and the weighted remainder -/

theorem directOrbit_gapRoot_rotate_sub_axis_dvd
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    eisensteinAxis ∣ rotateEquiv s.gapRoot - s.gapRoot := by
  rw [eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero]
  change thetaResidue (rotateEquiv s.gapRoot - s.gapRoot) = 0
  rw [map_sub, thetaResidue_rotateEquiv, sub_self]

theorem directOrbit_gapRoot_pow_not_axis_dvd
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    ¬eisensteinAxis ∣ s.gapRoot ^ 7 := by
  intro hpow
  exact directOrbit_gapRoot_not_axis_dvd s
    (eisensteinAxis_prime.dvd_of_dvd_pow hpow)

def directOrbit_weightedGapRemainder
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) : SevenRealCubicInt :=
  ((directOrbitTwistedCoeff1 s : SevenRealCubicInt) -
      (directOrbitTwistedCoeff0 s : SevenRealCubicInt)) * s.gapRoot ^ 7

theorem directOrbit_weightedGapRemainder_not_axis_dvd
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    ¬eisensteinAxis ∣ directOrbit_weightedGapRemainder s := by
  intro hd
  change eisensteinAxis ∣
    ((directOrbitTwistedCoeff1 s : SevenRealCubicInt) -
      (directOrbitTwistedCoeff0 s : SevenRealCubicInt)) * s.gapRoot ^ 7 at hd
  rcases eisensteinAxis_prime.dvd_mul.mp hd with hcoeff | hroot
  · exact directOrbit_twistedCoeff1_sub_coeff0_not_axis_dvd s hcoeff
  · exact directOrbit_gapRoot_pow_not_axis_dvd s hroot

/-! ## Failure of ordinary root-gap extraction -/

theorem directOrbit_weighted_difference_not_gap_dvd
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    ¬(rotateEquiv s.gapRoot - s.gapRoot) ∣
      ((directOrbitTwistedCoeff1 s : SevenRealCubicInt) *
          (rotateEquiv s.gapRoot) ^ 7 -
        (directOrbitTwistedCoeff0 s : SevenRealCubicInt) *
          s.gapRoot ^ 7) := by
  intro hfull
  have hpowdiff :
      rotateEquiv s.gapRoot - s.gapRoot ∣
        (rotateEquiv s.gapRoot) ^ 7 - s.gapRoot ^ 7 := by
    rw [pow_seven_sub_pow_seven_factorization]
    exact dvd_mul_right _ _
  have hfirst :
      rotateEquiv s.gapRoot - s.gapRoot ∣
        (directOrbitTwistedCoeff1 s : SevenRealCubicInt) *
          ((rotateEquiv s.gapRoot) ^ 7 - s.gapRoot ^ 7) :=
    dvd_mul_of_dvd_right hpowdiff _
  have hidentity := weighted_seventh_difference_remainder
    (directOrbitTwistedCoeff1 s) (directOrbitTwistedCoeff0 s)
    (rotateEquiv s.gapRoot) s.gapRoot
  have hrem :
      rotateEquiv s.gapRoot - s.gapRoot ∣
        directOrbit_weightedGapRemainder s := by
    have hsub := dvd_sub hfull hfirst
    rw [hidentity] at hsub
    simpa [directOrbit_weightedGapRemainder, add_sub_cancel_left] using hsub
  exact directOrbit_weightedGapRemainder_not_axis_dvd s
    (dvd_trans (directOrbit_gapRoot_rotate_sub_axis_dvd s) hrem)

theorem directOrbit_no_ordinary_homogeneous_restart
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    ¬∃ q : SevenRealCubicInt,
      (directOrbitTwistedCoeff1 s : SevenRealCubicInt) *
          (rotateEquiv s.gapRoot) ^ 7 -
        (directOrbitTwistedCoeff0 s : SevenRealCubicInt) *
          s.gapRoot ^ 7 =
        (rotateEquiv s.gapRoot - s.gapRoot) * q := by
  rintro ⟨q, hq⟩
  apply directOrbit_weighted_difference_not_gap_dvd s
  exact ⟨q, hq⟩

/-! The R24 projective class result also rules out a unit seventh-power gauge
normalization.  This is recorded separately from the scalar-residue proof:
the obstruction to ordinary gap extraction above uses the stronger residue
calculation, not projectiveLog. -/

theorem directOrbit_twistedCoeff1_not_unit_gauge
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    ¬∃ v : SevenRealCubicIntˣ,
      directOrbitTwistedCoeff1 s = directOrbitTwistedCoeff0 s * v ^ 7 := by
  apply (directOrbit_twistedCoeff_ratios_not_seventhPower_of_gapClass s
    (directOrbitPowerSplit_gapUnit_projectiveLog s)).1

end
end DkMath.FLT.Seven
