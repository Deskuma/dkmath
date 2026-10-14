/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry.Phase.SevenTreasure
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixCarrier
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixDomain
import Mathlib.Tactic

#print "file: DkMath.FLT.Seven.NumberGeometryFourteenPhaseBridge"

/-!
# One-way NumberGeometry fourteen-phase calibration

This bridge is owned by the FLT/Seven side. It identifies a concrete lift
inside the existing degree-six carrier without changing that carrier or any
FLT7 theorem.
-/

namespace DkMath.FLT.Seven

noncomputable section

namespace SevenCyclotomicDegreeSixInt

open DkMath.NumberGeometry.Phase

/-- The lifted fourteen-phase generator in the existing degree-six carrier. -/
def eta14 : Ring := -(zeta ^ 4)

/-- Squaring the lifted phase recovers the existing seventh root. -/
theorem eta14_sq : eta14 ^ 2 = zeta := by
  calc
    eta14 ^ 2 = zeta ^ 8 := by
      simp [eta14, ← pow_mul]
    _ = zeta := by
      rw [show (8 : ℕ) = 7 + 1 by norm_num, pow_add, zeta_pow_seven]
      simp

/-- The lifted phase has the required seventh-power half-turn. -/
theorem eta14_pow_seven : eta14 ^ 7 = -1 := by
  change (-(zeta ^ 4)) ^ 7 = -1
  rw [(by decide : Odd 7).neg_pow]
  rw [← pow_mul]
  rw [show (4 : ℕ) * 7 = 7 * 4 by norm_num, pow_mul, zeta_pow_seven]
  simp

/-- The lifted phase has the required fourteenth-power full turn. -/
theorem eta14_pow_fourteen : eta14 ^ 14 = 1 := by
  calc
    eta14 ^ 14 = (eta14 ^ 7) ^ 2 := by
      rw [show (14 : ℕ) = 7 * 2 by norm_num, pow_mul]
    _ = 1 := by rw [eta14_pow_seven]; norm_num


/-- The lifted phase is primitive of exact order fourteen. -/
theorem eta14_isPrimitiveRoot : IsPrimitiveRoot eta14 14 := by
  refine IsPrimitiveRoot.mk_of_lt eta14 (by norm_num) eta14_pow_fourteen ?_
  intro l hl0 hl14 h
  have hpow2 : eta14 ^ (2 * l) = 1 := by
    calc
      eta14 ^ (2 * l) = eta14 ^ (l * 2) := by congr 1; ring
      _ = (eta14 ^ l) ^ 2 := by rw [pow_mul]
      _ = 1 := by rw [h]; norm_num
  have hzeta : zeta ^ l = 1 := by
    calc
      zeta ^ l = (eta14 ^ 2) ^ l := by rw [eta14_sq]
      _ = eta14 ^ (2 * l) := by rw [pow_mul]
      _ = 1 := hpow2
  have hdiv : 7 ∣ l :=
    (zeta_isPrimitiveRoot.pow_eq_one_iff_dvd l).mp hzeta
  rcases hdiv with ⟨k, hk⟩
  have hl7 : l = 7 := by omega
  rw [hl7, eta14_pow_seven] at h
  have hne : (-1 : Ring) ≠ 1 := by
    intro hneg
    have hcoord := congrArg (fun x : Ring => coordinates x 0) hneg
    change (-1 : ℤ) = 1 at hcoord
    norm_num at hcoord
  exact hne h

/-- The existing carrier realizes the generic `FourteenPhase` packet. -/
noncomputable def degreeSixFourteenPhase :
    FourteenPhase Ring where
  eta := eta14
  positive := by norm_num
  primitive := eta14_isPrimitiveRoot

/-- The generic squared generator is exactly the existing carrier generator. -/
@[simp] theorem degreeSixFourteenPhase_zeta :
    degreeSixFourteenPhase.zeta = zeta := by
  change eta14 ^ 2 = zeta
  exact eta14_sq

/-- The existing carrier generator is the even phase at index one. -/
theorem degreeSixFourteenPhase_evenPhase_one :
    degreeSixFourteenPhase.evenPhase 1 = zeta := by
  rw [degreeSixFourteenPhase.evenPhase_eq_zeta_pow,
    degreeSixFourteenPhase_zeta, pow_one]

end SevenCyclotomicDegreeSixInt

end

end DkMath.FLT.Seven
