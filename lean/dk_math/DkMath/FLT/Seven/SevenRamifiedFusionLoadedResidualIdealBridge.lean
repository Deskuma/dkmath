/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionGlobalOrientedPrimeFactorization
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicRamifiedPrime

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionLoadedResidualIdealBridge"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

namespace SevenCyclotomicDegreeSixInt

/-- Principal-ideal form of the exact square ramification of the real
Eisenstein axis. -/
theorem span_ofReal_eisensteinAxis_eq_ramifiedPrime_sq :
    Ideal.span {ofReal SevenRealCubicInt.eisensteinAxis} =
      ramifiedPrime ^ 2 := by
  rw [ofReal_eisensteinAxis_eq, ramifiedPrime_eq_span_uniformizer,
    Ideal.span_singleton_pow]
  exact
    Ideal.span_singleton_eq_span_singleton.mpr
      (associated_unit_mul_left
        (ramifiedUniformizer ^ 2) zetaInv
        (show IsUnit zetaInv from ⟨zetaUnit⁻¹, rfl⟩))

end SevenCyclotomicDegreeSixInt

namespace RamifiedFusionRow2LoadFamily

open SevenCyclotomicDegreeSixInt

variable (family : RamifiedFusionRow2LoadFamily)
  (p : RamifiedSignedRootRoutingPacket)

/-- The explicit oriented half of one phase-indexed mapped real load. -/
def globalCyclicOrientedHalfIdeal
    (i : Fin 3) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  ∏ s : PrimeSupport family p, s.cyclicKernelPower i

/-- The quadratic-conjugate half of one phase-indexed mapped real load. -/
def globalCyclicConjugateHalfIdeal
    (i : Fin 3) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  ∏ s : PrimeSupport family p, s.cyclicConjugateKernelPower i

/-- The two explicit halves recover the complete mapped-load ideal. -/
theorem globalCyclicHalfIdeal_mul_conjugate_eq_factorIdeal
    (i : Fin 3) :
    globalCyclicOrientedHalfIdeal family p i *
        globalCyclicConjugateHalfIdeal family p i =
      globalCyclicOrientedFactorIdeal family p i := by
  rw [globalCyclicOrientedHalfIdeal,
    globalCyclicConjugateHalfIdeal,
    globalCyclicOrientedFactorIdeal,
    ← Finset.prod_mul_distrib]
  rfl

/-- Principal-ideal form of the explicit load-half pair. -/
theorem globalCyclicHalfIdeal_mul_conjugate_eq_span_ofReal_load
    (i : Fin 3) :
    globalCyclicOrientedHalfIdeal family p i *
        globalCyclicConjugateHalfIdeal family p i =
      Ideal.span {ofReal (family.load p i)} := by
  rw [globalCyclicHalfIdeal_mul_conjugate_eq_factorIdeal,
    globalCyclicOrientedFactorIdeal_eq_span_ofReal_load]

/-- Quadratic conjugation exchanges the two finite load halves. -/
theorem map_star_globalCyclicOrientedHalfIdeal
    (i : Fin 3) :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        (globalCyclicOrientedHalfIdeal family p i) =
      globalCyclicConjugateHalfIdeal family p i := by
  rw [globalCyclicOrientedHalfIdeal,
    globalCyclicConjugateHalfIdeal]
  change
    (Ideal.mapHom
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring))
        (∏ s : PrimeSupport family p, s.cyclicKernelPower i) =
      ∏ s : PrimeSupport family p,
        s.cyclicConjugateKernelPower i
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro s hs
  exact s.map_star_cyclicKernelPower_eq_cyclicConjugateKernelPower i

/-- Reverse quadratic-conjugation exchange of the load halves. -/
theorem map_star_globalCyclicConjugateHalfIdeal
    (i : Fin 3) :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        (globalCyclicConjugateHalfIdeal family p i) =
      globalCyclicOrientedHalfIdeal family p i := by
  rw [globalCyclicConjugateHalfIdeal,
    globalCyclicOrientedHalfIdeal]
  change
    (Ideal.mapHom
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring))
        (∏ s : PrimeSupport family p,
          s.cyclicConjugateKernelPower i) =
      ∏ s : PrimeSupport family p, s.cyclicKernelPower i
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro s hs
  exact s.map_star_cyclicConjugateKernelPower_eq_cyclicKernelPower i

end RamifiedFusionRow2LoadFamily

namespace RamifiedSignedRootRoutingPacket

open SevenCyclotomicDegreeSixInt

/-- Product of the two row-two oriented load halves in one real phase. -/
def orientedLoadedHalfIdeal
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  RamifiedFusionRow2LoadFamily.globalCyclicOrientedHalfIdeal
      .cell21 p i *
    RamifiedFusionRow2LoadFamily.globalCyclicOrientedHalfIdeal
      .cell22 p i

/-- Product of the two conjugate row-two load halves in one real phase. -/
def conjugateLoadedHalfIdeal
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  RamifiedFusionRow2LoadFamily.globalCyclicConjugateHalfIdeal
      .cell21 p i *
    RamifiedFusionRow2LoadFamily.globalCyclicConjugateHalfIdeal
      .cell22 p i

/-- The combined oriented/conjugate load halves recover the extension of
the two canonical real gcd loads. -/
theorem orientedLoadedHalfIdeal_mul_conjugate_eq_span_ofReal_loads
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    p.orientedLoadedHalfIdeal i *
        p.conjugateLoadedHalfIdeal i =
      Ideal.span
        {ofReal
          (p.realPairLoad21 i * p.realPairLoad22 i)} := by
  rw [orientedLoadedHalfIdeal, conjugateLoadedHalfIdeal]
  calc
    (_ * _) * (_ * _) =
        (RamifiedFusionRow2LoadFamily.globalCyclicOrientedHalfIdeal
            .cell21 p i *
          RamifiedFusionRow2LoadFamily.globalCyclicConjugateHalfIdeal
            .cell21 p i) *
        (RamifiedFusionRow2LoadFamily.globalCyclicOrientedHalfIdeal
            .cell22 p i *
          RamifiedFusionRow2LoadFamily.globalCyclicConjugateHalfIdeal
            .cell22 p i) := by
      ring
    _ =
        Ideal.span {ofReal (p.realPairLoad21 i)} *
          Ideal.span {ofReal (p.realPairLoad22 i)} := by
      rw [RamifiedFusionRow2LoadFamily.globalCyclicHalfIdeal_mul_conjugate_eq_span_ofReal_load,
        RamifiedFusionRow2LoadFamily.globalCyclicHalfIdeal_mul_conjugate_eq_span_ofReal_load]
      rfl
    _ =
        Ideal.span
          {ofReal
            (p.realPairLoad21 i * p.realPairLoad22 i)} := by
      rw [Ideal.span_singleton_mul_span_singleton, map_mul]

/-- Quadratic conjugation exchanges the two combined load halves. -/
theorem map_star_orientedLoadedHalfIdeal
    (p : RamifiedSignedRootRoutingPacket) (i : Fin 3) :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        (p.orientedLoadedHalfIdeal i) =
      p.conjugateLoadedHalfIdeal i := by
  rw [orientedLoadedHalfIdeal, conjugateLoadedHalfIdeal,
    Ideal.map_mul,
    RamifiedFusionRow2LoadFamily.map_star_globalCyclicOrientedHalfIdeal,
    RamifiedFusionRow2LoadFamily.map_star_globalCyclicOrientedHalfIdeal]

/-- A canonical natural root for the seventh-power residual in the signed
quotient-root norm decomposition. -/
noncomputable def row2ResidualNormRoot
    (p : RamifiedSignedRootRoutingPacket) : ℕ :=
  Classical.choose p.exists_row2_twoCellSeventhPowerFactor

/-- Exact natural decomposition underlying all residual prime exponents. -/
theorem quotientRoot_natAbs_eq_row2Loads_mul_residualNormRoot_pow
    (p : RamifiedSignedRootRoutingPacket) :
    Int.natAbs p.signedDepth.quotientRoot =
      p.routing.c21 * p.routing.c22 *
        p.row2ResidualNormRoot ^ 7 :=
  Classical.choose_spec p.exists_row2_twoCellSeventhPowerFactor

private theorem quotientRoot_ne_zero
    (p : RamifiedSignedRootRoutingPacket) :
    p.signedDepth.quotientRoot ≠ 0 := by
  let : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro hzero
  have hmod := p.signedDepth.quotientRoot_modSeven_eq_one
  rw [hzero] at hmod
  exact zero_ne_one hmod

private theorem row2Cell21_ne_zero
    (p : RamifiedSignedRootRoutingPacket) :
    p.routing.c21 ≠ 0 := by
  intro hzero
  exact p.activeCells_not_seven_dvd.2.2.2.1
    (by rw [hzero]; exact dvd_zero 7)

private theorem row2Cell22_ne_zero
    (p : RamifiedSignedRootRoutingPacket) :
    p.routing.c22 ≠ 0 := by
  intro hzero
  exact p.activeCells_not_seven_dvd.2.2.2.2.1
    (by rw [hzero]; exact dvd_zero 7)

/-- The selected residual norm root is nonzero. -/
theorem row2ResidualNormRoot_ne_zero
    (p : RamifiedSignedRootRoutingPacket) :
    p.row2ResidualNormRoot ≠ 0 := by
  intro hzero
  have h :=
    p.quotientRoot_natAbs_eq_row2Loads_mul_residualNormRoot_pow
  rw [hzero, zero_pow (by norm_num : 7 ≠ 0), mul_zero] at h
  exact p.quotientRoot_ne_zero
    (Int.natAbs_eq_zero.mp h)

/-- Exact prime-exponent decomposition: every quotient-root exponent is
the sum of the two routed-load exponents and seven times a residual
exponent.  This arithmetic bridge is independent of U1.2's degree-six
carrier ownership theorem. -/
theorem padicValNat_quotientRoot_eq_loads_add_seven_mul_residual
    (p : RamifiedSignedRootRoutingPacket)
    {q : ℕ} (hq : Nat.Prime q) :
    padicValNat q
        (Int.natAbs p.signedDepth.quotientRoot) =
      padicValNat q p.routing.c21 +
        padicValNat q p.routing.c22 +
          7 * padicValNat q p.row2ResidualNormRoot := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have hval :=
    congrArg (padicValNat q)
      p.quotientRoot_natAbs_eq_row2Loads_mul_residualNormRoot_pow
  rw [
    padicValNat.mul
      (mul_ne_zero p.row2Cell21_ne_zero p.row2Cell22_ne_zero)
      (pow_ne_zero 7 p.row2ResidualNormRoot_ne_zero),
    padicValNat.mul p.row2Cell21_ne_zero p.row2Cell22_ne_zero,
    padicValNat.pow (p := q) (a := p.row2ResidualNormRoot) 7] at hval
  omega

namespace RealPairLoadedPowerSplit

variable {p : RamifiedSignedRootRoutingPacket}

/-- The mapped principal residual ideal.  It is the complete conjugate pair,
not yet either of the two oriented halves sought in U1.3. -/
def residualPairIdeal
    (loaded : RealPairLoadedPowerSplit p) (i : Fin 3) :
    Ideal SevenCyclotomicDegreeSixInt.Ring :=
  Ideal.span {ofReal (loaded.residualRoot i)}

/-- The real-cubic loaded packet already gives an exact load-times-seventh-
power ideal decomposition before choosing either degree-six orientation. -/
theorem span_realPairCore_eq_loads_mul_residual_pow
    (loaded : RealPairLoadedPowerSplit p) (i : Fin 3) :
    Ideal.span {p.signedDepth.realPairCore i} =
      Ideal.span
          {p.realPairLoad21 i * p.realPairLoad22 i} *
        Ideal.span {loaded.residualRoot i} ^ 7 := by
  have hcore := loaded.coreAssociated i
  rw [loaded.load21_eq_gcd, loaded.load22_eq_gcd] at hcore
  calc
    Ideal.span {p.signedDepth.realPairCore i} =
        Ideal.span
          {p.realPairLoad21 i * p.realPairLoad22 i *
            loaded.residualRoot i ^ 7} :=
      (Ideal.span_singleton_eq_span_singleton.mpr hcore).symm
    _ =
        Ideal.span
            {p.realPairLoad21 i * p.realPairLoad22 i} *
          Ideal.span {loaded.residualRoot i} ^ 7 := by
      rw [Ideal.span_singleton_pow,
        Ideal.span_singleton_mul_span_singleton]

/-- Extension of the real loaded decomposition to the concrete degree-six
domain.  The residual remains the complete conjugate-pair ideal here. -/
theorem span_ofReal_realPairCore_eq_loads_mul_residualPair_pow
    (loaded : RealPairLoadedPowerSplit p) (i : Fin 3) :
    Ideal.span {ofReal (p.signedDepth.realPairCore i)} =
      Ideal.span
          {ofReal
            (p.realPairLoad21 i * p.realPairLoad22 i)} *
        loaded.residualPairIdeal i ^ 7 := by
  have h :=
    congrArg (Ideal.map ofReal)
      (loaded.span_realPairCore_eq_loads_mul_residual_pow i)
  simpa only [Ideal.map_span, Set.image_singleton,
    Ideal.map_mul, Ideal.map_pow, residualPairIdeal] using h

/-- The mapped residual-pair ideal is fixed by quadratic conjugation. -/
theorem map_star_residualPairIdeal
    (loaded : RealPairLoadedPowerSplit p) (i : Fin 3) :
    Ideal.map
        (starRingEnd SevenCyclotomicDegreeSixInt.Ring)
        (loaded.residualPairIdeal i) =
      loaded.residualPairIdeal i := by
  rw [residualPairIdeal, Ideal.map_span]
  congr
  ext x
  simp [starRingEnd_apply,
    SevenCyclotomicDegreeSixInt.star_ofReal]

/-- Pair-level U1.3 bridge: the product of the two linear carrier ideals is
exactly the square ramified factor, the explicit load-half pair, and the
seventh power of the mapped residual pair.  Splitting the last pair between
the two carriers is deliberately not asserted here. -/
theorem carrierIdealPair_eq_ramified_sq_mul_loadHalves_mul_residualPair_pow
    (loaded : RealPairLoadedPowerSplit p) :
    Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrier} *
        Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrierConj} =
      SevenCyclotomicDegreeSixInt.ramifiedPrime ^ 2 *
        (p.orientedLoadedHalfIdeal 0 *
          p.conjugateLoadedHalfIdeal 0) *
        loaded.residualPairIdeal 0 ^ 7 := by
  calc
    Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrier} *
        Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrierConj} =
        Ideal.span
          {p.signedDepth.cyclotomicDegreeSixCarrier *
            p.signedDepth.cyclotomicDegreeSixCarrierConj} := by
      rw [Ideal.span_singleton_mul_span_singleton]
    _ =
        Ideal.span
          {ofReal (SevenRealCubicInt.eisensteinAxis *
            p.signedDepth.realPairCore 0)} := by
      rw [p.signedDepth.cyclotomicDegreeSixCarrier_mul_conj,
        p.signedDepth.realPairCarrier_eq_eisensteinAxis_mul_core]
    _ =
        Ideal.span
            {ofReal SevenRealCubicInt.eisensteinAxis} *
          Ideal.span
            {ofReal (p.signedDepth.realPairCore 0)} := by
      rw [map_mul, Ideal.span_singleton_mul_span_singleton]
    _ =
        SevenCyclotomicDegreeSixInt.ramifiedPrime ^ 2 *
          (Ideal.span
              {ofReal
                (p.realPairLoad21 0 * p.realPairLoad22 0)} *
            loaded.residualPairIdeal 0 ^ 7) := by
      rw [SevenCyclotomicDegreeSixInt.span_ofReal_eisensteinAxis_eq_ramifiedPrime_sq,
        loaded.span_ofReal_realPairCore_eq_loads_mul_residualPair_pow]
    _ =
        SevenCyclotomicDegreeSixInt.ramifiedPrime ^ 2 *
          (p.orientedLoadedHalfIdeal 0 *
            p.conjugateLoadedHalfIdeal 0) *
          loaded.residualPairIdeal 0 ^ 7 := by
      rw [p.orientedLoadedHalfIdeal_mul_conjugate_eq_span_ofReal_loads]
      ring

end RealPairLoadedPowerSplit

end RamifiedSignedRootRoutingPacket


end

end DkMath.FLT.Seven
