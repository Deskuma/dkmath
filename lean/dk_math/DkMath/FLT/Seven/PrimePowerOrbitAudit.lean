/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimePowerUnitOrbit

#print "file: DkMath.FLT.Seven.PrimePowerOrbitAudit"

namespace DkMath.FLT.Seven

inductive AwayNonSevenPrimePowerOrbitSource {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwayNonSevenPrimeDepthPacket r) :
    RootRoutingColumn → Type
  | sevenV
      (actual model : AwayRoutingPrimePowerSolution p.modulus p.row .sevenV)
      (scale : ZMod p.modulus) (scale_isUnit : IsUnit scale)
      (actual_eq : actual = scalePrimePowerSolution model scale scale_isUnit) :
      AwayNonSevenPrimePowerOrbitSource p .sevenV
  | leftCubic
      (t : ZMod p.modulus) (root : leftCubicNormalizedZMod t = 0)
      (correction_unit : IsUnit (leftCorrectionNormalizedZMod t))
      (actual model : AwayRoutingPrimePowerSolution p.modulus p.row .leftCubic)
      (scale : ZMod p.modulus) (scale_isUnit : IsUnit scale)
      (actual_eq : actual = scalePrimePowerSolution model scale scale_isUnit) :
      AwayNonSevenPrimePowerOrbitSource p .leftCubic
  | rightCubic
      (t : ZMod p.modulus) (root : rightCubicNormalizedZMod t = 0)
      (correction_unit : IsUnit (rightCorrectionNormalizedZMod t))
      (actual model : AwayRoutingPrimePowerSolution p.modulus p.row .rightCubic)
      (scale : ZMod p.modulus) (scale_isUnit : IsUnit scale)
      (actual_eq : actual = scalePrimePowerSolution model scale scale_isUnit) :
      AwayNonSevenPrimePowerOrbitSource p .rightCubic

theorem primePowerOrbitSource_of_depthPacket {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwayNonSevenPrimeDepthPacket r) :
    Nonempty (AwayNonSevenPrimePowerOrbitSource p p.column) := by
  let actual := p.toPrimePowerSolution
  cases hc : p.column with
  | sevenV =>
      have a : AwayRoutingPrimePowerSolution p.modulus p.row .sevenV := by
        simpa [hc] using actual
      rcases sevenV_primePower_orbit_complete a with ⟨w⟩
      exact ⟨.sevenV a (canonicalPrimePowerSolution_sevenV p.modulus p.row)
        w.scale w.scale_isUnit w.actual_eq⟩
  | leftCubic =>
      have a : AwayRoutingPrimePowerSolution p.modulus p.row .leftCubic := by
        simpa [hc] using actual
      let t := a.u * a.v⁻¹
      have ht : leftCubicNormalizedZMod t = 0 :=
        left_normalized_root_of_primePowerSolution a
      have hL := leftCorrection_isUnit_of_leftCubic_eq_zero_primePower
        p.q_prime p.q_ne_seven p.exponent_pos t ht
      rcases leftCubic_primePower_orbit_complete p.q_prime p.q_ne_seven
        p.exponent_pos a with ⟨w⟩
      exact ⟨.leftCubic t ht hL a
        (canonicalPrimePowerSolution_leftCubic p.q_prime p.q_ne_seven
          p.exponent_pos t ht p.row) w.scale w.scale_isUnit w.actual_eq⟩
  | rightCubic =>
      have a : AwayRoutingPrimePowerSolution p.modulus p.row .rightCubic := by
        simpa [hc] using actual
      let t := a.u * a.v⁻¹
      have ht : rightCubicNormalizedZMod t = 0 :=
        right_normalized_root_of_primePowerSolution a
      have hR := rightCorrection_isUnit_of_rightCubic_eq_zero_primePower
        p.q_prime p.q_ne_seven p.exponent_pos t ht
      rcases rightCubic_primePower_orbit_complete p.q_prime p.q_ne_seven
        p.exponent_pos a with ⟨w⟩
      exact ⟨.rightCubic t ht hR a
        (canonicalPrimePowerSolution_rightCubic p.q_prime p.q_ne_seven
          p.exponent_pos t ht p.row) w.scale w.scale_isUnit w.actual_eq⟩

inductive PrimePowerOrbitAuditResult (x y z : ℕ) : Type
  | ramified (packet : RamifiedCoordinateNormalForm x y z)
  | awayOrbitClassified
      (routing : AwayCubicRoutingPacket x y z)
      (constraints : AwayFirstCoordinateRoutingConstraints routing)
      (classification : ∀ p : AwayNonSevenPrimeDepthPacket routing,
        Nonempty (AwayNonSevenPrimePowerOrbitSource p p.column))

theorem primePowerOrbitAuditResult_of_pack {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    Nonempty (PrimePowerOrbitAuditResult x y z) := by
  rcases coordinateCounterexampleRoute_of_pack hPack with ⟨route⟩
  cases route with
  | ramified packet => exact ⟨.ramified packet⟩
  | away packet =>
      rcases nonempty_awayCubicRoutingPacket packet with ⟨routing⟩
      rcases nonempty_awayFirstCoordinateRoutingConstraints routing with ⟨constraints⟩
      exact ⟨.awayOrbitClassified routing constraints
        (fun p => primePowerOrbitSource_of_depthPacket p)⟩

end DkMath.FLT.Seven
