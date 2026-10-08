/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneReconstructionFiniteChart
import DkMath.FLT.Seven.PrimeTraceOneReconstructionChartU16

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionDepthFourReconstructionAudit"

namespace DkMath.FLT.Seven

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- The U1.6 obligation is exactly one finite additive existence condition.
Carrier positivity and seven-divisibility are already proved. A successful
certificate invokes the existing chart constructor, rather than requiring a
new cyclotomic phase normalization or a separately supplied away root. -/
theorem internalDepthFourReconstruction_iff_finiteCharts
    (p : RamifiedSignedRootRoutingPacket) :
    InternalDepthFourCounterexampleReconstructionObligation p ↔
      (prescribedCarrierFiniteCharts (internalDepthFourCarrier p)).Nonempty := by
  have hc := internalDepthFourCarrier_admissible p
  rw [internalDepthFourReconstruction_iff_awayCarrierReconstruction,
    awayCarrierReconstruction_iff_finiteCharts hc.1 hc.2.2]

/-- The new away root would have depth three, not the depth four of the
internal quadratic coordinate. This is forced by the packet's transfer law. -/
theorem internalDepthFourReconstructedRoute_root_depth
    (p : RamifiedSignedRootRoutingPacket) {x y z : ℕ}
    (route : AwayValuationTransferPacket x y z)
    (hcarrier : route.carrier = internalDepthFourCarrier p) :
    padicValNat 7 (Int.natAbs route.normal.root.snd) = 3 := by
  have h := route.valuation_eq
  rw [hcarrier, padicValNat_internalDepthFourCarrier] at h
  omega

/-- Reusing the existing extracted quadratic inner root as the new away root
cannot satisfy valuation transfer at the prescribed carrier. This obstruction
is independent of the degree-six residual generator's phase. -/
theorem internalDepthFourReconstructedRoute_root_ne_innerRoot
    (p : RamifiedSignedRootRoutingPacket) {x y z : ℕ}
    (route : AwayValuationTransferPacket x y z)
    (hcarrier : route.carrier = internalDepthFourCarrier p) :
    route.normal.root ≠
      p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.quadratic.innerRoot := by
  intro heq
  have h := internalDepthFourReconstructedRoute_root_depth p route hcarrier
  have hd := padicValNat_internalDepthFourCarrier p
  rw [heq] at h
  change padicValNat 7 (internalDepthFourCarrier p) = 3 at h
  omega

/-- A finite additive certificate assembles every missing route field and
the conditional `4 < 5` comparison. No certificate is asserted to exist. -/
theorem exists_strict_awayCounterexample_of_depthFourFiniteChart
    (p : RamifiedSignedRootRoutingPacket)
    (h : (prescribedCarrierFiniteCharts (internalDepthFourCarrier p)).Nonempty) :
    ∃ (x y z : ℕ) (route : AwayValuationTransferPacket x y z),
      CounterexamplePack x y z ∧
        route.carrier = internalDepthFourCarrier p ∧
        padicValNat 7 route.carrier < padicValNat 7 (outerDepthFiveCarrier p) :=
  exists_strict_awayCounterexample_of_internalDepthFourReconstruction p
    ((internalDepthFourReconstruction_iff_finiteCharts p).mpr h)

open SevenCyclotomicDegreeSixInt

/-- On this very residual ideal, even ideal plus exact seventh power cannot
decode the full coordinates of every valid generator. Both inputs coincide
for the root and its zeta translate, while their coordinate vectors differ.
This rules out that decoder contract, not an invariant natural-chart
extractor, and does not prove that U1.6 is logically impossible. -/
theorem no_fullCoordinate_decoder_on_orientedResidualIdeal
    (p : RamifiedSignedRootRoutingPacket) :
    ¬ ∃ decode : Ideal Ring × Ring → (Fin 6 → ℤ),
      ∀ r : Ring, Ideal.span {r} = globalOrientedResidualIdeal (p := p) →
        decode (Ideal.span {r}, r ^ 7) = coordinates r := by
  rintro ⟨decode, hdecode⟩
  have hbase := hdecode (orientedResidualRoot p) (span_orientedResidualRoot p)
  have htwist := hdecode (zeta * orientedResidualRoot p)
    ((span_zeta_mul_orientedResidualRoot p).trans (span_orientedResidualRoot p))
  have hpow : (zeta * orientedResidualRoot p) ^ 7 = orientedResidualRoot p ^ 7 := by
    rw [mul_pow, zeta_pow_seven, one_mul]
  rw [span_zeta_mul_orientedResidualRoot, hpow] at htwist
  exact coordinates_zeta_mul_orientedResidualRoot_ne p (htwist.symm.trans hbase)

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

end DkMath.FLT.Seven
