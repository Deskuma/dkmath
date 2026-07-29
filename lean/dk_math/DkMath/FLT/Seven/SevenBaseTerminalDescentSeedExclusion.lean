/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenBaseTerminalDescentProvider

#print "file: DkMath.FLT.Seven.SevenBaseTerminalDescentSeedExclusion"

namespace DkMath.FLT.Seven

/-- A reconstruction seed can only occur in a lifted pivot branch.  Its target
carrier is the old root second coordinate, while every new away carrier has
positive seven-adic depth. -/
theorem AwayDescentReconstructionSeed.two_le_pivotExponent
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r)
    (seed : AwayDescentReconstructionSeed r.cubic.transfer) :
    2 ≤ p.exponent := by
  have hpositive := seed.nextRoute.one_le_carrier_depth
  have hcarrier :
      seed.nextRoute.carrier =
        Int.natAbs r.cubic.transfer.normal.root.snd := rfl
  rw [hcarrier, r.cubic.normal_eq, ← r.cubic.rootTriple.vPart_eq,
    p.root_depth_eq] at hpositive
  omega

/-- The original closure provider likewise forces the old pivot to be lifted. -/
theorem AwayDescentClosureProvider.two_le_pivotExponent
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r)
    (provider :
      AwayDescentClosureProvider x y z r.cubic.transfer) :
    2 ≤ p.exponent :=
  provider.toReconstructionSeed.two_le_pivotExponent p

/-- DESCENT-002 obstruction: the integral reconstruction seed is uninhabited
at terminal depth one. -/
theorem no_descentReconstructionSeed_of_exponent_eq_one
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) (hterminal : p.exponent = 1) :
    ¬ Nonempty (AwayDescentReconstructionSeed r.cubic.transfer) := by
  rintro ⟨seed⟩
  have := seed.two_le_pivotExponent p
  omega

/-- No recursive closure provider can inhabit a depth-one terminal branch. -/
theorem no_descentClosureProvider_of_exponent_eq_one
    {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) (hterminal : p.exponent = 1) :
    ¬ Nonempty
      (AwayDescentClosureProvider x y z r.cubic.transfer) := by
  rw [← nonempty_descentReconstructionSeed_iff_closureProvider]
  exact no_descentReconstructionSeed_of_exponent_eq_one p hterminal

/-- The exact seed obligation stored by DESCENT-001 is false for every actual
terminal packet. -/
theorem AwaySevenBaseTerminalDescentOpenPacket.not_reconstructionObligation
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : AwayCubicRoutingPacket x y z} {p : AwaySevenPivotDepthPacket r}
    {packet : AwaySevenBaseTerminalRoutingPacket (source := source) p}
    {family : AwaySevenBaseTerminalPrimeScaleFamily packet}
    {candidate :
      AwaySevenBaseTerminalProductModulusWeightedCoordinatesPacket family}
    {signed : AwaySevenBaseTerminalSignedRepresentativePacket candidate}
    (openPacket : AwaySevenBaseTerminalDescentOpenPacket signed) :
    ¬ openPacket.reconstructionObligation := by
  rw [openPacket.reconstructionObligation_eq]
  exact no_descentReconstructionSeed_of_exponent_eq_one p
    packet.core.depth_eq_one

end DkMath.FLT.Seven
