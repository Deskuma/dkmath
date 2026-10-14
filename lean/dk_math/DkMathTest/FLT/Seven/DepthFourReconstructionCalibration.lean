/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionDepthFourReconstructionAudit

#print "file: DkMathTest.FLT.Seven.DepthFourReconstructionCalibration"

namespace DkMathTest.FLT.Seven

open DkMath.FLT.Seven
open RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- Zero has no positive candidates. This does not apply the positive-carrier
reconstruction equivalence outside its hypotheses. -/
theorem zero_window_empty : prescribedCarrierFiniteCharts 0 = ∅ := by decide

theorem one_window_empty : prescribedCarrierFiniteCharts 1 = ∅ := by decide

theorem two_window_empty : prescribedCarrierFiniteCharts 2 = ∅ := by decide

theorem three_window_empty : prescribedCarrierFiniteCharts 3 = ∅ := by decide

/-- Positivity and coprimality alone do not supply the additive equation. -/
theorem seven_pair_not_a_chart : (1, 2) ∉ prescribedCarrierFiniteCharts 7 := by
  rw [mem_prescribedCarrierFiniteCharts]
  norm_num

/-- Exercise the formerly unbounded right chart, not only the bounded left
chart. The geometric quotient proof is independent of seven-divisibility. -/
theorem right_chart_window {x c z : ℕ} (pack : CounterexamplePack x c z) :
    z ^ 6 ≤ c ^ 7 ∧ x < z ∧ z ≤ c ^ 2 :=
  ⟨pack.right_sixth_power_bound, pack.right_quadratic_bound⟩

/-- Generic equivalence retains both required carrier hypotheses. -/
theorem prescribed_window_receiver {c : ℕ} (hc : 0 < c) (h7 : 7 ∣ c) :
    AwayCarrierReconstruction c ↔ (prescribedCarrierFiniteCharts c).Nonempty :=
  awayCarrierReconstruction_iff_finiteCharts hc h7

theorem depth_four_receiver (p : RamifiedSignedRootRoutingPacket) :
    InternalDepthFourCounterexampleReconstructionObligation p ↔
      (prescribedCarrierFiniteCharts (internalDepthFourCarrier p)).Nonempty :=
  internalDepthFourReconstruction_iff_finiteCharts p

theorem reconstructed_root_depth_three (p : RamifiedSignedRootRoutingPacket)
    {x y z : ℕ} (route : AwayValuationTransferPacket x y z)
    (hc : route.carrier = internalDepthFourCarrier p) :
    padicValNat 7 (Int.natAbs route.normal.root.snd) = 3 :=
  internalDepthFourReconstructedRoute_root_depth p route hc

end DkMathTest.FLT.Seven
