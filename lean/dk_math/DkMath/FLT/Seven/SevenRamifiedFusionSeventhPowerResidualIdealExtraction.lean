/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionOrientedCarrierValuationOwnership
import DkMath.FLT.Seven.SevenRamifiedFusionLoadedResidualIdealBridge

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionSeventhPowerResidualIdealExtraction"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

namespace RamifiedFusionRow2LoadFamily

variable {family : RamifiedFusionRow2LoadFamily}
  {p : RamifiedSignedRootRoutingPacket}

theorem primeFactors_cell_subset_quotientRoot
    (family : RamifiedFusionRow2LoadFamily)
    (p : RamifiedSignedRootRoutingPacket) :
    (family.cell p).primeFactors ⊆
      (Int.natAbs p.signedDepth.quotientRoot).primeFactors := by
  intro q hq
  rw [Nat.mem_primeFactors]
  exact
    ⟨Nat.prime_of_mem_primeFactors hq,
      (Nat.dvd_of_mem_primeFactors hq).trans
        (family.cell_dvd_quotientRoot_natAbs p),
      Int.natAbs_ne_zero.mpr <| by
        letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
        intro hzero
        have hmod :=
          p.signedDepth.quotientRoot_modSeven_eq_one
        rw [hzero] at hmod
        exact zero_ne_one hmod⟩

namespace PrimeSupport

/-- Every routed-cell prime belongs canonically to the full signed
quotient-root support. -/
def toQuotientPrimeSupport
    (s : PrimeSupport family p) :
    p.QuotientPrimeSupport :=
  ⟨s.1, family.primeFactors_cell_subset_quotientRoot p s.2⟩

@[simp] theorem toQuotientPrimeSupport_val
    (s : PrimeSupport family p) :
    s.toQuotientPrimeSupport.1 = s.1 :=
  rfl

theorem toQuotientPrimeSupport_injective :
    Function.Injective
      (toQuotientPrimeSupport :
        PrimeSupport family p → p.QuotientPrimeSupport) := by
  intro s t hst
  exact Subtype.ext
    (congrArg
      (fun u : p.QuotientPrimeSupport => u.1) hst)

/-- The full-support and routed-cell constructions use definitionally the
same canonical `mu_7` address; only proofs of divisibility differ. -/
theorem toQuotientPrimeSupport_muSevenAddress
    (s : PrimeSupport family p) :
    s.toQuotientPrimeSupport.muSevenAddress =
      s.address.muSevenAddress := by
  rfl

/-- Consequently both support presentations select the same oriented
degree-six prime. -/
theorem toQuotientPrimeSupport_orientedKernel
    (s : PrimeSupport family p) :
    s.toQuotientPrimeSupport.orientedKernel =
      s.cyclotomicAddress.cyclicKernel 0 := by
  rw [RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.orientedKernel,
    RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.cyclotomicAddress,
    RamifiedSignedRootRoutingPacket.CyclotomicLinearPrimeAddress.cyclicKernel_zero,
    cyclotomicAddress,
    s.toQuotientPrimeSupport_muSevenAddress]
  rfl

/-- The conjugate prime is coherent under the same support inclusion. -/
theorem toQuotientPrimeSupport_conjugateKernel
    (s : PrimeSupport family p) :
    s.toQuotientPrimeSupport.conjugateKernel =
      s.cyclotomicAddress.cyclicConjugateKernel 0 := by
  rw [RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.conjugateKernel,
    RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.cyclotomicAddress,
    RamifiedSignedRootRoutingPacket.CyclotomicLinearPrimeAddress.cyclicConjugateKernel_zero,
    cyclotomicAddress,
    s.toQuotientPrimeSupport_muSevenAddress]
  rfl

end PrimeSupport

end RamifiedFusionRow2LoadFamily

namespace SevenCyclotomicDegreeSixInt

/-- Quadratic conjugation fixes the unique displayed ramified prime above
seven. -/
theorem map_star_ramifiedPrime :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        ramifiedPrime =
      ramifiedPrime := by
  rw [ramifiedPrime_eq_span_uniformizer,
    Ideal.map_span, Set.image_singleton]
  change
    Ideal.span {star ramifiedUniformizer} =
      Ideal.span {ramifiedUniformizer}
  have hstar :
      star ramifiedUniformizer =
        ramifiedUniformizerConj := by
    simp [ramifiedUniformizer, ramifiedUniformizerConj]
  rw [hstar, ramifiedUniformizerConj_eq]
  exact
    Ideal.span_singleton_eq_span_singleton.mpr
      (associated_unit_mul_left
        ramifiedUniformizer (-zetaInv)
        (show IsUnit (-zetaInv) from
          (show IsUnit zetaInv from
            ⟨zetaUnit⁻¹, rfl⟩).neg))

end SevenCyclotomicDegreeSixInt

namespace RamifiedSignedRootRoutingPacket

open SevenCyclotomicDegreeSixInt

namespace QuotientPrimeSupport

variable {p : RamifiedSignedRootRoutingPacket}

/-- One routed load rewritten on the full quotient-root support.  Primes
outside the cell support occur with exponent zero. -/
def globalOrientedFullSupportLoadHalfIdeal
    (family : RamifiedFusionRow2LoadFamily) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  ∏ s : p.QuotientPrimeSupport,
    s.orientedKernel ^
      padicValNat s.1 (family.cell p)

/-- Conjugate full-support presentation of one routed load half. -/
def globalConjugateFullSupportLoadHalfIdeal
    (family : RamifiedFusionRow2LoadFamily) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  ∏ s : p.QuotientPrimeSupport,
    s.conjugateKernel ^
      padicValNat s.1 (family.cell p)

/-- Reindexing one oriented routed load from its cell support to the full
quotient-root support only inserts factors with exponent zero. -/
theorem globalOrientedFullSupportLoadHalfIdeal_eq_globalCyclicOrientedHalfIdeal
    (family : RamifiedFusionRow2LoadFamily) :
    globalOrientedFullSupportLoadHalfIdeal (p := p) family =
      RamifiedFusionRow2LoadFamily.globalCyclicOrientedHalfIdeal
        family p 0 := by
  rw [globalOrientedFullSupportLoadHalfIdeal,
    RamifiedFusionRow2LoadFamily.globalCyclicOrientedHalfIdeal]
  apply
    (Fintype.prod_of_injective
      (RamifiedFusionRow2LoadFamily.PrimeSupport.toQuotientPrimeSupport :
        RamifiedFusionRow2LoadFamily.PrimeSupport family p →
          p.QuotientPrimeSupport)
      RamifiedFusionRow2LoadFamily.PrimeSupport.toQuotientPrimeSupport_injective
      (fun s : RamifiedFusionRow2LoadFamily.PrimeSupport family p =>
        s.cyclicKernelPower 0)
      (fun s : p.QuotientPrimeSupport =>
        s.orientedKernel ^
          padicValNat s.1 (family.cell p))
      ?_ ?_).symm
  · intro s hs
    have hnotmem :
        s.1 ∉ (family.cell p).primeFactors := by
      intro hmem
      let t :
          RamifiedFusionRow2LoadFamily.PrimeSupport family p :=
        ⟨s.1, hmem⟩
      apply hs
      refine ⟨t, ?_⟩
      exact Subtype.ext rfl
    have hnotdvd : ¬s.1 ∣ family.cell p := by
      intro hdvd
      exact hnotmem <|
        (Nat.mem_primeFactors).2
          ⟨s.prime, hdvd, family.cell_ne_zero p⟩
    change
      s.orientedKernel ^
          padicValNat s.1 (family.cell p) =
        1
    rw [padicValNat.eq_zero_of_not_dvd hnotdvd, pow_zero]
  · intro s
    change
      s.cyclotomicAddress.cyclicKernel 0 ^
          padicValNat s.1 (family.cell p) =
        s.toQuotientPrimeSupport.orientedKernel ^
          padicValNat s.1 (family.cell p)
    rw [RamifiedFusionRow2LoadFamily.PrimeSupport.toQuotientPrimeSupport_orientedKernel]

/-- Conjugate reindexing of one routed load; again all newly inserted
full-support factors have exponent zero. -/
theorem globalConjugateFullSupportLoadHalfIdeal_eq_globalCyclicConjugateHalfIdeal
    (family : RamifiedFusionRow2LoadFamily) :
    globalConjugateFullSupportLoadHalfIdeal (p := p) family =
      RamifiedFusionRow2LoadFamily.globalCyclicConjugateHalfIdeal
        family p 0 := by
  rw [globalConjugateFullSupportLoadHalfIdeal,
    RamifiedFusionRow2LoadFamily.globalCyclicConjugateHalfIdeal]
  apply
    (Fintype.prod_of_injective
      (RamifiedFusionRow2LoadFamily.PrimeSupport.toQuotientPrimeSupport :
        RamifiedFusionRow2LoadFamily.PrimeSupport family p →
          p.QuotientPrimeSupport)
      RamifiedFusionRow2LoadFamily.PrimeSupport.toQuotientPrimeSupport_injective
      (fun s : RamifiedFusionRow2LoadFamily.PrimeSupport family p =>
        s.cyclicConjugateKernelPower 0)
      (fun s : p.QuotientPrimeSupport =>
        s.conjugateKernel ^
          padicValNat s.1 (family.cell p))
      ?_ ?_).symm
  · intro s hs
    have hnotmem :
        s.1 ∉ (family.cell p).primeFactors := by
      intro hmem
      let t :
          RamifiedFusionRow2LoadFamily.PrimeSupport family p :=
        ⟨s.1, hmem⟩
      apply hs
      refine ⟨t, ?_⟩
      exact Subtype.ext rfl
    have hnotdvd : ¬s.1 ∣ family.cell p := by
      intro hdvd
      exact hnotmem <|
        (Nat.mem_primeFactors).2
          ⟨s.prime, hdvd, family.cell_ne_zero p⟩
    change
      s.conjugateKernel ^
          padicValNat s.1 (family.cell p) =
        1
    rw [padicValNat.eq_zero_of_not_dvd hnotdvd, pow_zero]
  · intro s
    change
      s.cyclotomicAddress.cyclicConjugateKernel 0 ^
          padicValNat s.1 (family.cell p) =
        s.toQuotientPrimeSupport.conjugateKernel ^
          padicValNat s.1 (family.cell p)
    rw [RamifiedFusionRow2LoadFamily.PrimeSupport.toQuotientPrimeSupport_conjugateKernel]

/-- The two routed row-two loads combined on the full support. -/
def globalOrientedLoadedHalfIdeal :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  ∏ s : p.QuotientPrimeSupport,
    s.orientedKernel ^
      (padicValNat s.1 p.routing.c21 +
        padicValNat s.1 p.routing.c22)

/-- Conjugate combined full-support load half. -/
def globalConjugateLoadedHalfIdeal :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  ∏ s : p.QuotientPrimeSupport,
    s.conjugateKernel ^
      (padicValNat s.1 p.routing.c21 +
        padicValNat s.1 p.routing.c22)

/-- Explicit oriented seventh-power residual ideal. -/
def globalOrientedResidualIdeal :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  ∏ s : p.QuotientPrimeSupport,
    s.orientedKernel ^
      padicValNat s.1 p.row2ResidualNormRoot

/-- Quadratic-conjugate seventh-power residual ideal. -/
def globalConjugateResidualIdeal :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  ∏ s : p.QuotientPrimeSupport,
    s.conjugateKernel ^
      padicValNat s.1 p.row2ResidualNormRoot

/-- The two full-support routed loads combine pointwise. -/
theorem globalOrientedLoadedHalfIdeal_eq_mul :
    globalOrientedLoadedHalfIdeal (p := p) =
      globalOrientedFullSupportLoadHalfIdeal
          (p := p) .cell21 *
        globalOrientedFullSupportLoadHalfIdeal
          (p := p) .cell22 := by
  rw [globalOrientedLoadedHalfIdeal,
    globalOrientedFullSupportLoadHalfIdeal,
    globalOrientedFullSupportLoadHalfIdeal,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro s hs
  rw [← pow_add]
  rfl

/-- Conjugate form of the two-load combination. -/
theorem globalConjugateLoadedHalfIdeal_eq_mul :
    globalConjugateLoadedHalfIdeal (p := p) =
      globalConjugateFullSupportLoadHalfIdeal
          (p := p) .cell21 *
        globalConjugateFullSupportLoadHalfIdeal
          (p := p) .cell22 := by
  rw [globalConjugateLoadedHalfIdeal,
    globalConjugateFullSupportLoadHalfIdeal,
    globalConjugateFullSupportLoadHalfIdeal,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro s hs
  rw [← pow_add]
  rfl

/-- The full-support oriented load presentation is exactly the already
constructed phase-zero load half. -/
theorem globalOrientedLoadedHalfIdeal_eq_orientedLoadedHalfIdeal :
    globalOrientedLoadedHalfIdeal (p := p) =
      p.orientedLoadedHalfIdeal 0 := by
  rw [globalOrientedLoadedHalfIdeal_eq_mul,
    RamifiedSignedRootRoutingPacket.orientedLoadedHalfIdeal,
    globalOrientedFullSupportLoadHalfIdeal_eq_globalCyclicOrientedHalfIdeal,
    globalOrientedFullSupportLoadHalfIdeal_eq_globalCyclicOrientedHalfIdeal]

/-- Conjugate full-support load presentation agrees with the existing
phase-zero conjugate half. -/
theorem globalConjugateLoadedHalfIdeal_eq_conjugateLoadedHalfIdeal :
    globalConjugateLoadedHalfIdeal (p := p) =
      p.conjugateLoadedHalfIdeal 0 := by
  rw [globalConjugateLoadedHalfIdeal_eq_mul,
    RamifiedSignedRootRoutingPacket.conjugateLoadedHalfIdeal,
    globalConjugateFullSupportLoadHalfIdeal_eq_globalCyclicConjugateHalfIdeal,
    globalConjugateFullSupportLoadHalfIdeal_eq_globalCyclicConjugateHalfIdeal]

/-- Quadratic conjugation exchanges the two full-support loaded halves. -/
theorem map_star_globalOrientedLoadedHalfIdeal :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        (globalOrientedLoadedHalfIdeal (p := p)) =
      globalConjugateLoadedHalfIdeal (p := p) := by
  rw [globalOrientedLoadedHalfIdeal_eq_orientedLoadedHalfIdeal,
    globalConjugateLoadedHalfIdeal_eq_conjugateLoadedHalfIdeal,
    p.map_star_orientedLoadedHalfIdeal]

/-- Quadratic conjugation exchanges the two explicit residual seventh-root
ideals, prime by prime. -/
theorem map_star_globalOrientedResidualIdeal :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        (globalOrientedResidualIdeal (p := p)) =
      globalConjugateResidualIdeal (p := p) := by
  rw [globalOrientedResidualIdeal,
    globalConjugateResidualIdeal]
  change
    (Ideal.mapHom
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring))
        (∏ s : p.QuotientPrimeSupport,
          s.orientedKernel ^
            padicValNat s.1 p.row2ResidualNormRoot) =
      ∏ s : p.QuotientPrimeSupport,
        s.conjugateKernel ^
          padicValNat s.1 p.row2ResidualNormRoot
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro s hs
  change
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        (s.orientedKernel ^
          padicValNat s.1 p.row2ResidualNormRoot) =
      s.conjugateKernel ^
        padicValNat s.1 p.row2ResidualNormRoot
  rw [Ideal.map_pow, orientedKernel, conjugateKernel,
    s.cyclotomicAddress.map_star_evalKernel_eq_conjugateEvalKernel]

/-- Full-support exponent reconstruction of the oriented core half. -/
theorem globalOrientedCoreHalfIdeal_eq_loaded_mul_residual_pow :
    globalOrientedCoreHalfIdeal (p := p) =
      globalOrientedLoadedHalfIdeal (p := p) *
        globalOrientedResidualIdeal (p := p) ^ 7 := by
  have hpow :
      globalOrientedResidualIdeal (p := p) ^ 7 =
        ∏ s : p.QuotientPrimeSupport,
          (s.orientedKernel ^
            padicValNat s.1 p.row2ResidualNormRoot) ^ 7 := by
    rw [globalOrientedResidualIdeal]
    simpa only using
      (Finset.prod_pow Finset.univ 7
        (fun s : p.QuotientPrimeSupport =>
          s.orientedKernel ^
            padicValNat s.1 p.row2ResidualNormRoot)).symm
  rw [globalOrientedCoreHalfIdeal,
    globalOrientedLoadedHalfIdeal,
    hpow,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro s hs
  have hexponent :=
    p.padicValNat_quotientRoot_eq_loads_add_seven_mul_residual
      s.prime
  rw [quotientExponent, hexponent]
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

/-- Full-support exponent reconstruction of the conjugate core half. -/
theorem globalConjugateCoreHalfIdeal_eq_loaded_mul_residual_pow :
    globalConjugateCoreHalfIdeal (p := p) =
      globalConjugateLoadedHalfIdeal (p := p) *
        globalConjugateResidualIdeal (p := p) ^ 7 := by
  have hpow :
      globalConjugateResidualIdeal (p := p) ^ 7 =
        ∏ s : p.QuotientPrimeSupport,
          (s.conjugateKernel ^
            padicValNat s.1 p.row2ResidualNormRoot) ^ 7 := by
    rw [globalConjugateResidualIdeal]
    simpa only using
      (Finset.prod_pow Finset.univ 7
        (fun s : p.QuotientPrimeSupport =>
          s.conjugateKernel ^
            padicValNat s.1 p.row2ResidualNormRoot)).symm
  rw [globalConjugateCoreHalfIdeal,
    globalConjugateLoadedHalfIdeal,
    hpow,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro s hs
  have hexponent :=
    p.padicValNat_quotientRoot_eq_loads_add_seven_mul_residual
      s.prime
  rw [quotientExponent, hexponent]
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

/-- The ramified prime together with the two explicit routed load halves:
the complete non-seventh-power part of the oriented carrier ideal. -/
def globalOrientedLoadedCarrierIdeal :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  SevenCyclotomicDegreeSixInt.ramifiedPrime *
    globalOrientedLoadedHalfIdeal (p := p)

/-- Quadratic-conjugate loaded carrier ideal. -/
def globalConjugateLoadedCarrierIdeal :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  SevenCyclotomicDegreeSixInt.ramifiedPrime *
    globalConjugateLoadedHalfIdeal (p := p)

/-- The oriented loaded carrier can equivalently use the previously
constructed phase-zero routed-load half. -/
theorem globalOrientedLoadedCarrierIdeal_eq_ramified_mul_orientedLoadedHalfIdeal :
    globalOrientedLoadedCarrierIdeal (p := p) =
      SevenCyclotomicDegreeSixInt.ramifiedPrime *
        p.orientedLoadedHalfIdeal 0 := by
  rw [globalOrientedLoadedCarrierIdeal,
    globalOrientedLoadedHalfIdeal_eq_orientedLoadedHalfIdeal]

/-- Conjugate phase-zero form of the loaded carrier ideal. -/
theorem globalConjugateLoadedCarrierIdeal_eq_ramified_mul_conjugateLoadedHalfIdeal :
    globalConjugateLoadedCarrierIdeal (p := p) =
      SevenCyclotomicDegreeSixInt.ramifiedPrime *
        p.conjugateLoadedHalfIdeal 0 := by
  rw [globalConjugateLoadedCarrierIdeal,
    globalConjugateLoadedHalfIdeal_eq_conjugateLoadedHalfIdeal]

/-- Quadratic conjugation exchanges the two loaded carrier ideals. -/
theorem map_star_globalOrientedLoadedCarrierIdeal :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        (globalOrientedLoadedCarrierIdeal (p := p)) =
      globalConjugateLoadedCarrierIdeal (p := p) := by
  rw [globalOrientedLoadedCarrierIdeal,
    globalConjugateLoadedCarrierIdeal,
    Ideal.map_mul,
    SevenCyclotomicDegreeSixInt.map_star_ramifiedPrime,
    map_star_globalOrientedLoadedHalfIdeal]

/-- Exact U1.3 extraction: the oriented carrier principal ideal is its
explicit loaded part times the seventh power of the residual ideal. -/
theorem span_carrier_eq_loadedCarrier_mul_residual_pow :
    Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrier} =
      globalOrientedLoadedCarrierIdeal (p := p) *
        globalOrientedResidualIdeal (p := p) ^ 7 := by
  rw [← globalOrientedCarrierFactorIdeal_eq_span_carrier,
    globalOrientedCarrierFactorIdeal,
    globalOrientedCoreHalfIdeal_eq_loaded_mul_residual_pow,
    globalOrientedLoadedCarrierIdeal]
  ring

/-- Exact conjugate U1.3 extraction. -/
theorem span_conjugateCarrier_eq_loadedCarrier_mul_residual_pow :
    Ideal.span
        {p.signedDepth.cyclotomicDegreeSixCarrierConj} =
      globalConjugateLoadedCarrierIdeal (p := p) *
        globalConjugateResidualIdeal (p := p) ^ 7 := by
  rw [← globalConjugateCarrierFactorIdeal_eq_span_conjugateCarrier,
    globalConjugateCarrierFactorIdeal,
    globalConjugateCoreHalfIdeal_eq_loaded_mul_residual_pow,
    globalConjugateLoadedCarrierIdeal]
  ring

/-- Compact exact U1.3 packet: both carrier ideals have the required
load-times-seventh-power extraction, and all selected factors are coherent
under quadratic conjugation. -/
theorem globalSeventhPowerResidualIdealExtractionPacket :
    Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrier} =
        globalOrientedLoadedCarrierIdeal (p := p) *
          globalOrientedResidualIdeal (p := p) ^ 7 ∧
      Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrierConj} =
        globalConjugateLoadedCarrierIdeal (p := p) *
          globalConjugateResidualIdeal (p := p) ^ 7 ∧
      Ideal.map
          (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
          (globalOrientedLoadedCarrierIdeal (p := p)) =
        globalConjugateLoadedCarrierIdeal (p := p) ∧
      Ideal.map
          (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
          (globalOrientedResidualIdeal (p := p)) =
        globalConjugateResidualIdeal (p := p) ∧
      globalOrientedLoadedHalfIdeal (p := p) =
        p.orientedLoadedHalfIdeal 0 ∧
      globalConjugateLoadedHalfIdeal (p := p) =
        p.conjugateLoadedHalfIdeal 0 :=
  ⟨span_carrier_eq_loadedCarrier_mul_residual_pow,
    span_conjugateCarrier_eq_loadedCarrier_mul_residual_pow,
    map_star_globalOrientedLoadedCarrierIdeal,
    map_star_globalOrientedResidualIdeal,
    globalOrientedLoadedHalfIdeal_eq_orientedLoadedHalfIdeal,
    globalConjugateLoadedHalfIdeal_eq_conjugateLoadedHalfIdeal⟩

end QuotientPrimeSupport

end RamifiedSignedRootRoutingPacket


end

end DkMath.FLT.Seven
