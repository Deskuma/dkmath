/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedSignedRootRouting
import DkMath.FLT.Seven.SevenRealCubicThetaCoordinates

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionUnitSector"

namespace DkMath.FLT.Seven

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

namespace RamifiedSignedRootDepthPacket

/-- Division-free refinement of the signed quotient identity. -/
theorem quotientRoot_eq_left_pow_six_add_correction
    (p : RamifiedSignedRootDepthPacket) :
    ∃ correction : ℤ,
      p.quotientRoot =
        p.signedLeftRoot ^ 6 + 7 ^ 3 * correction := by
  let F :=
    signedSeventhQuotientFirstVariation
      p.signedRightRoot p.signedLeftRoot
  have hfactor :
      signedSeventhQuotient p.signedRightRoot p.signedLeftRoot =
        7 * p.signedLeftRoot ^ 6 +
          (p.signedRightRoot - p.signedLeftRoot) * F := by
    rw [← signedSeventhQuotient_sub_seven_mul_pow_six]
    ring
  refine ⟨p.gapRoot * F, ?_⟩
  apply mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0)
  calc
    7 * p.quotientRoot =
        signedSeventhQuotient
          p.signedRightRoot p.signedLeftRoot := p.signedQuotient_eq.symm
    _ = 7 * p.signedLeftRoot ^ 6 +
          (p.signedRightRoot - p.signedLeftRoot) * F := hfactor
    _ = 7 * (p.signedLeftRoot ^ 6 +
          7 ^ 3 * (p.gapRoot * F)) := by
      rw [p.signedGap_eq]
      ring

/-- The quotient root is forced into the positive unit sector modulo seven. -/
theorem quotientRoot_modSeven_eq_one
    (p : RamifiedSignedRootDepthPacket) :
    (p.quotientRoot : ZMod 7) = 1 := by
  rcases p.quotientRoot_eq_left_pow_six_add_correction with
    ⟨correction, hcorrection⟩
  rw [hcorrection]
  push_cast
  have hleft :
      (p.signedLeftRoot : ZMod 7) ≠ 0 := by
    intro hzero
    apply
      (p.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
        ).signedLeftRoot_not_seven_dvd
    rw [← p.signedLeftRoot_eq]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hzero
  have h343 : (343 : ZMod 7) = 0 := by decide
  rw [h343, zero_mul, add_zero]
  simpa using ZMod.pow_card_sub_one_eq_one hleft

/-- The normalized equation and the positive quotient sector determine the
gap-root leading residue. -/
theorem gapRoot_modSeven_eq
    (p : RamifiedSignedRootDepthPacket) :
    (p.gapRoot : ZMod 7) =
      ((p.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
          ).quadratic.innerRoot.fst : ZMod 7) ^ 2 *
        ((p.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
          ).innerSndRoot : ZMod 7) := by
  let q := p.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
  have h := congrArg (fun z : ℤ => (z : ZMod 7)) p.normalizedEquation
  push_cast at h
  have hn :
      (q.quadratic.innerRoot.snd : ZMod 7) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr
    exact q.innerSnd_seven_dvd
  rw [p.quotientRoot_modSeven_eq_one, mul_one, hn, add_zero] at h
  simpa [q, ZMod.pow_card, pow_two, mul_assoc] using h


end RamifiedSignedRootDepthPacket

end

end DkMath.FLT.Seven
