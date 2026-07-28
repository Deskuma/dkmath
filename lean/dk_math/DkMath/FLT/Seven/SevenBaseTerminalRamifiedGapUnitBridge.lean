/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalRamifiedRouting
import DkMath.FLT.Seven.SevenPivotPrimePowerSystem

#print "file: DkMath.FLT.Seven.SevenBaseTerminalRamifiedGapUnitBridge"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

/-- The division-free integral form of the ramified gap-unit bridge. -/
theorem
    PrimitiveRamifiedSummitPacket.cubicGap_mul_sndCore_eq_endpointGap_mul_bridge
    (p : PrimitiveRamifiedSummitPacket) :
    (ramifiedRightCubic p.root.fst p.root.snd -
        ramifiedLeftCubic p.root.fst p.root.snd) *
        seventhPowerSndCore p.root.fst p.root.snd =
      (p.endpointLeft - p.endpointRight) *
        (ramifiedGapQuotient
          (7 ^ 5 * (p.gapRoot : ℤ) ^ 7)
          p.endpointRight).snd *
        norm p.root := by
  have hsnd := p.seventhPowerSnd_eq_gap_mul_quotient
  rw [seventhPowerSnd_eq_seven_mul, ← p.gap_eq] at hsnd
  calc
    _ = (7 * p.root.snd * norm p.root) *
          seventhPowerSndCore p.root.fst p.root.snd := by
        rw [ramifiedRightCubic_sub_left]
    _ = (7 * p.root.snd *
          seventhPowerSndCore p.root.fst p.root.snd) * norm p.root := by
        ring
    _ = ((p.endpointLeft - p.endpointRight) *
          (ramifiedGapQuotient
            (7 ^ 5 * (p.gapRoot : ℤ) ^ 7)
            p.endpointRight).snd) * norm p.root := by
        rw [hsnd]
    _ = _ := by ring

/-- An exact integral equality between two gaps after multiplication by
explicit integers which are units at the ramified prime `7`. -/
structure RamifiedGapUnitBridgePacket : Type where
  endpointGap : ℤ
  cubicGap : ℤ
  leftUnit : ℤ
  rightUnit : ℤ
  leftUnit_not_seven_dvd : ¬ (7 : ℤ) ∣ leftUnit
  rightUnit_not_seven_dvd : ¬ (7 : ℤ) ∣ rightUnit
  bridge_eq : cubicGap * leftUnit = endpointGap * rightUnit

/-- The canonical exact gap-unit bridge attached to a primitive ramified
summit. -/
def PrimitiveRamifiedSummitPacket.ramifiedGapUnitBridge
    (p : PrimitiveRamifiedSummitPacket) :
    RamifiedGapUnitBridgePacket where
  endpointGap := p.endpointLeft - p.endpointRight
  cubicGap :=
    ramifiedRightCubic p.root.fst p.root.snd -
      ramifiedLeftCubic p.root.fst p.root.snd
  leftUnit := seventhPowerSndCore p.root.fst p.root.snd
  rightUnit :=
    (ramifiedGapQuotient
      (7 ^ 5 * (p.gapRoot : ℤ) ^ 7)
      p.endpointRight).snd * norm p.root
  leftUnit_not_seven_dvd := p.sndCore_not_seven_dvd
  rightUnit_not_seven_dvd := by
    intro h
    rcases (show Prime (7 : ℤ) by norm_num).dvd_mul.mp h with hQ | hnorm
    · exact
        (ramifiedGapQuotient_snd_not_seven_dvd
          p.endpointRight_not_seven_dvd) hQ
    · exact p.root_norm_not_seven_dvd hnorm
  bridge_eq := by
    simpa only [mul_assoc] using
      p.cubicGap_mul_sndCore_eq_endpointGap_mul_bridge

theorem RamifiedGapUnitBridgePacket.leftUnit_isUnit
    (p : RamifiedGapUnitBridgePacket) (k : ℕ) :
    IsUnit (p.leftUnit : ZMod (7 ^ k)) :=
  intCast_isUnit_zmod_sevenPower p.leftUnit_not_seven_dvd

theorem RamifiedGapUnitBridgePacket.rightUnit_isUnit
    (p : RamifiedGapUnitBridgePacket) (k : ℕ) :
    IsUnit (p.rightUnit : ZMod (7 ^ k)) :=
  intCast_isUnit_zmod_sevenPower p.rightUnit_not_seven_dvd

/-- The explicit `7`-adic unit transforming the endpoint gap into the cubic
gap modulo `7^k`. -/
noncomputable def RamifiedGapUnitBridgePacket.explicitUnit
    (p : RamifiedGapUnitBridgePacket) (k : ℕ) : ZMod (7 ^ k) :=
  (p.rightUnit : ZMod (7 ^ k)) *
    (↑((p.leftUnit_isUnit k).unit⁻¹) : ZMod (7 ^ k))

theorem RamifiedGapUnitBridgePacket.explicitUnit_isUnit
    (p : RamifiedGapUnitBridgePacket) (k : ℕ) :
    IsUnit (p.explicitUnit k) := by
  exact (p.rightUnit_isUnit k).mul (Units.isUnit _)

/-- Multiplying the displayed quotient unit back by its denominator recovers
the right bridge coefficient. -/
theorem RamifiedGapUnitBridgePacket.explicitUnit_mul_leftUnit
    (p : RamifiedGapUnitBridgePacket) (k : ℕ) :
    p.explicitUnit k * (p.leftUnit : ZMod (7 ^ k)) =
      (p.rightUnit : ZMod (7 ^ k)) := by
  rw [explicitUnit]
  calc
    ((p.rightUnit : ZMod (7 ^ k)) *
        (↑((p.leftUnit_isUnit k).unit⁻¹) : ZMod (7 ^ k))) *
        (p.leftUnit : ZMod (7 ^ k)) =
      (p.rightUnit : ZMod (7 ^ k)) *
        ((↑((p.leftUnit_isUnit k).unit⁻¹) : ZMod (7 ^ k)) *
          (p.leftUnit : ZMod (7 ^ k))) := by ring
    _ = _ := by rw [(p.leftUnit_isUnit k).val_inv_mul, mul_one]

/-- Over every modulus `7^k`, the two ramified gaps differ by the displayed
explicit unit.  The statement includes the degenerate modulus at `k = 0`. -/
theorem RamifiedGapUnitBridgePacket.cubicGap_eq_endpointGap_mul_explicitUnit
    (p : RamifiedGapUnitBridgePacket) (k : ℕ) :
    (p.cubicGap : ZMod (7 ^ k)) =
      (p.endpointGap : ZMod (7 ^ k)) * p.explicitUnit k := by
  have hbridge := congrArg (fun z : ℤ => (z : ZMod (7 ^ k))) p.bridge_eq
  push_cast at hbridge
  have hcancel :
      (p.leftUnit : ZMod (7 ^ k)) *
          (↑((p.leftUnit_isUnit k).unit⁻¹) : ZMod (7 ^ k)) = 1 :=
    (p.leftUnit_isUnit k).mul_val_inv
  calc
    (p.cubicGap : ZMod (7 ^ k)) =
        (p.cubicGap : ZMod (7 ^ k)) *
          ((p.leftUnit : ZMod (7 ^ k)) *
            (↑((p.leftUnit_isUnit k).unit⁻¹) :
              ZMod (7 ^ k))) := by rw [hcancel, mul_one]
    _ = ((p.cubicGap : ZMod (7 ^ k)) *
          (p.leftUnit : ZMod (7 ^ k))) *
            (↑((p.leftUnit_isUnit k).unit⁻¹) :
              ZMod (7 ^ k)) := by ring
    _ = ((p.endpointGap : ZMod (7 ^ k)) *
          (p.rightUnit : ZMod (7 ^ k))) *
            (↑((p.leftUnit_isUnit k).unit⁻¹) :
              ZMod (7 ^ k)) := by rw [hbridge]
    _ = (p.endpointGap : ZMod (7 ^ k)) * p.explicitUnit k := by
      simp only [explicitUnit]
      ring

#print axioms
  PrimitiveRamifiedSummitPacket.cubicGap_mul_sndCore_eq_endpointGap_mul_bridge
#print axioms
  RamifiedGapUnitBridgePacket.cubicGap_eq_endpointGap_mul_explicitUnit

end DkMath.FLT.Seven
