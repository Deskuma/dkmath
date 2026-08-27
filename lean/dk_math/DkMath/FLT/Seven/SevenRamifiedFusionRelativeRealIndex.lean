/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionRotationPhase

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionRelativeRealIndex"

namespace DkMath.FLT.Seven

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

namespace RamifiedPairedThetaRootJetPacket

/-- The real-conjugate pair coordinate obtained by forgetting the binary sign
of the cyclotomic index relative to the FUSION slope.  It selects a pair, not
an oriented factor. -/
def relativeRealIndex
    (p : RamifiedPairedThetaRootJetPacket)
    (k : (ZMod 7)ˣ) : SevenTernarySector :=
  ⟨(p.relativeCyclotomicIndex k) ^ 2, by
    change ((p.relativeCyclotomicIndex k) ^ 2) ^ 3 = 1
    rw [← pow_mul]
    norm_num
    exact sevenUnit_pow_six _⟩

theorem relativeRealIndex_eq_one_iff
    (p : RamifiedPairedThetaRootJetPacket)
    (k : (ZMod 7)ˣ) :
    p.relativeRealIndex k = 1 ↔
      k = p.fusionSlopeUnit ∨
      k = -p.fusionSlopeUnit := by
  let x := p.relativeCyclotomicIndex k
  constructor
  · intro h
    have hxUnits : x ^ 2 = 1 := by
      exact congrArg Subtype.val h
    have hx :
        ((x : (ZMod 7)ˣ) : ZMod 7) ^ 2 = 1 := by
      exact congrArg Units.val hxUnits
    rcases sq_eq_one_iff.mp hx with hx | hx
    · left
      apply (p.relativeCyclotomicIndex_eq_one_iff k).mp
      apply Units.ext
      exact hx
    · right
      have hxneg : x = -1 := by
        apply Units.ext
        exact hx
      change k = -p.fusionSlopeUnit
      calc
        k = x * p.fusionSlopeUnit := by
          simp [x, relativeCyclotomicIndex]
        _ = (-1) * p.fusionSlopeUnit := by rw [hxneg]
        _ = -p.fusionSlopeUnit := by simp
  · rintro (rfl | rfl)
    · apply Subtype.ext
      simp [relativeRealIndex, relativeCyclotomicIndex]
    · apply Subtype.ext
      change
        ((-p.fusionSlopeUnit / p.fusionSlopeUnit) ^ 2 :
          (ZMod 7)ˣ) = 1
      have hdiv :
          -p.fusionSlopeUnit / p.fusionSlopeUnit =
            (-1 : (ZMod 7)ˣ) := by
        apply Units.ext
        simp
      rw [hdiv]
      simp

/-- Every real-conjugate pair has exactly the two opposite oriented
cyclotomic representatives supplied by the binary sign. -/
theorem relativeRealIndex_fiber_one
    (p : RamifiedPairedThetaRootJetPacket) :
    {k : (ZMod 7)ˣ | p.relativeRealIndex k = 1} =
      {p.fusionSlopeUnit, -p.fusionSlopeUnit} := by
  ext k
  simp [p.relativeRealIndex_eq_one_iff k]

end RamifiedPairedThetaRootJetPacket


end

end DkMath.FLT.Seven
