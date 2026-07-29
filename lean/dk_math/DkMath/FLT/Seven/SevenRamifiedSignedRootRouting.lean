/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedSignedRootDepth
import DkMath.FLT.Seven.CoprimeTripleRouting

#print "file: DkMath.FLT.Seven.SevenRamifiedSignedRootRouting"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false in
/-- Canonical `2 × 3` factor-address board for the signed FUSION equation;
the third row is the neutral factor one. -/
structure RamifiedSignedRootRoutingPacket : Type where
  signedDepth : RamifiedSignedRootDepthPacket
  routing : CoprimeTripleRouting
    (Int.natAbs signedDepth.gapRoot)
    (Int.natAbs signedDepth.quotientRoot) 1
    (Int.natAbs
      signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.fst)
    (Int.natAbs
      (signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.fst +
        signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot.snd))
    (Int.natAbs
      signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.innerSndRoot ^ 7)

namespace RamifiedSignedRootDepthPacket

/-- The signed routing board together with coherence to the supplied
signed-depth packet. -/
theorem nonempty_coherent_signedRootRouting
    (p : RamifiedSignedRootDepthPacket) :
    Nonempty {q : RamifiedSignedRootRoutingPacket // q.signedDepth = p} := by
  let q := p.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
  have hAN : IsCoprime q.quadratic.innerRoot.fst
      (q.quadratic.innerRoot.fst + q.quadratic.innerRoot.snd) := by
    simpa [add_comm] using
      q.quadratic.innerRoot_coordinates_isCoprime.add_mul_right_right 1
  have hAM7 : IsCoprime q.quadratic.innerRoot.fst
      (q.innerSndRoot ^ 7) := by
    have h := q.quadratic.innerRoot_coordinates_isCoprime
    rw [q.innerSnd_eq] at h
    exact h.of_mul_right_right
  have hANM7 : IsCoprime
      (q.quadratic.innerRoot.fst + q.quadratic.innerRoot.snd)
      (q.innerSndRoot ^ 7) := by
    rw [q.innerSnd_eq]
    have h := q.rightSource_coordinates_isCoprime
    rw [q.innerSnd_eq] at h
    exact h.of_mul_right_right
  have hprod :
      Int.natAbs p.gapRoot * Int.natAbs p.quotientRoot * 1 =
        Int.natAbs q.quadratic.innerRoot.fst *
          Int.natAbs
            (q.quadratic.innerRoot.fst + q.quadratic.innerRoot.snd) *
          Int.natAbs (q.innerSndRoot ^ 7) := by
    have h := congrArg Int.natAbs p.normalizedEquation
    simpa [q, Int.natAbs_mul] using h
  rcases nonempty_coprimeTripleRouting
      ⟨Int.natAbs_pos.mpr
          (fun h => p.gapRoot_not_seven_dvd (by rw [h]; exact dvd_zero 7)),
        Int.natAbs_pos.mpr
          (fun h => p.quotientRoot_not_seven_dvd (by rw [h]; exact dvd_zero 7)),
        by norm_num⟩
      ⟨Int.natAbs_pos.mpr
          (fun h => q.innerFst_not_seven_dvd (by rw [h]; exact dvd_zero 7)),
        Int.natAbs_pos.mpr
          (fun h => q.innerFst_add_innerSnd_not_seven_dvd
            (by rw [h]; exact dvd_zero 7)),
        Int.natAbs_pos.mpr
          (fun h => q.innerSndRoot_not_seven_dvd
            (by
              have hm : q.innerSndRoot = 0 :=
                eq_zero_of_pow_eq_zero h
              rw [hm]
              exact dvd_zero 7))⟩
      (Int.isCoprime_iff_nat_coprime.mp p.gapRoot_isCoprime_quotientRoot)
      (Nat.coprime_one_right _) (Nat.coprime_one_right _)
      (Int.isCoprime_iff_nat_coprime.mp hAN)
      (Int.isCoprime_iff_nat_coprime.mp hAM7)
      (Int.isCoprime_iff_nat_coprime.mp hANM7)
      hprod with ⟨routing⟩
  exact ⟨⟨⟨p, by simpa [q] using routing⟩, rfl⟩⟩

theorem nonempty_signedRootRouting
    (p : RamifiedSignedRootDepthPacket) :
    Nonempty RamifiedSignedRootRoutingPacket := by
  rcases p.nonempty_coherent_signedRootRouting with ⟨q⟩
  exact ⟨q.1⟩

end RamifiedSignedRootDepthPacket

#print axioms
  RamifiedSignedRootDepthPacket.nonempty_coherent_signedRootRouting
#print axioms RamifiedSignedRootDepthPacket.nonempty_signedRootRouting

end

end DkMath.FLT.Seven
