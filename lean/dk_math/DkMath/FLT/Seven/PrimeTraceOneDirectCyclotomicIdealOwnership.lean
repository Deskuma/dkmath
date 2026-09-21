/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicSecondCaseAudit
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicAdditiveChartBoundary

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicIdealOwnership"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

open scoped QuadraticAlgebra

open SevenRealCubicInt
open SevenCyclotomicDegreeSixInt

/-- The tail left after extracting one explicit ramified uniformizer from the
direct endpoint gap.  It uses only the gap data in the current summit. -/
def directRamifiedGapTail
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    SevenCyclotomicDegreeSixInt.Ring :=
  ramifiedUniformizer ^ 35 * ramifiedSevenUnit ^ 6 *
    ofReal (r.summit.gapRoot : SevenRealCubicInt) ^ 7

/-- The quotient after extracting the first ramified uniformizer from the
direct factor. -/
def directRamifiedQuotient
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    SevenCyclotomicDegreeSixInt.Ring :=
  ofReal (r.summit.endpointRight : SevenRealCubicInt) +
    directRamifiedGapTail r

/-- The stored endpoint gap has an explicit uniformizer factorization. -/
theorem directGap_eq_uniformizer_pow
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    ofReal (r.summit.endpointLeft : SevenRealCubicInt) -
        ofReal (r.summit.endpointRight : SevenRealCubicInt) =
      ramifiedUniformizer ^ 36 * ramifiedSevenUnit ^ 6 *
        ofReal (r.summit.gapRoot : SevenRealCubicInt) ^ 7 := by
  have hgap := congrArg
    (fun q : ℤ => ofReal (q : SevenRealCubicInt)) r.summit.gap_eq
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow,
    map_sub, map_mul, map_pow] at hgap
  norm_num only [Int.cast_ofNat] at hgap
  have hcast :
      ((r.summit.gapRoot : ℤ) : SevenRealCubicInt) =
        (r.summit.gapRoot : SevenRealCubicInt) := by
    norm_cast
  rw [hcast] at hgap
  rw [hgap, ofReal_seven_eq_uniformizer_pow_six_mul_unit]
  simp only [mul_pow]
  ring

/-- The direct linear factor is exactly one uniformizer times the explicit
quotient. -/
theorem directLinearFactor_eq_uniformizer_mul_quotient
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    directLinearFactor r =
      ramifiedUniformizer * directRamifiedQuotient r := by
  calc
    directLinearFactor r =
        (ofReal (r.summit.endpointLeft : SevenRealCubicInt) -
          ofReal (r.summit.endpointRight : SevenRealCubicInt)) +
          ramifiedUniformizer *
            ofReal (r.summit.endpointRight : SevenRealCubicInt) := by
      simp only [directLinearFactor, ramifiedUniformizer]
      ring
    _ =
        ramifiedUniformizer ^ 36 * ramifiedSevenUnit ^ 6 *
            ofReal (r.summit.gapRoot : SevenRealCubicInt) ^ 7 +
          ramifiedUniformizer *
            ofReal (r.summit.endpointRight : SevenRealCubicInt) := by
      rw [directGap_eq_uniformizer_pow]
    _ = ramifiedUniformizer * directRamifiedQuotient r := by
      simp only [directRamifiedQuotient, directRamifiedGapTail]
      ring

/-- The quotient has the endpoint-right residue at the ramified prime. -/
theorem ramifiedEval_directRamifiedQuotient
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    ramifiedEval (directRamifiedQuotient r) =
      (r.summit.endpointRight : ZMod 7) := by
  rw [directRamifiedQuotient, map_add, ramifiedEval_ofReal]
  have htail : ramifiedEval (directRamifiedGapTail r) = 0 := by
    simp [directRamifiedGapTail, ramifiedEval_uniformizer]
  rw [htail, add_zero]
  simp [thetaResidue, thetaConstModSeven]

/-- The direct factor belongs to the unique ramified prime. -/
theorem directLinearFactor_mem_ramifiedPrime
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    directLinearFactor r ∈ ramifiedPrime := by
  rw [directLinearFactor_eq_uniformizer_mul_quotient]
  change ramifiedEval
      (ramifiedUniformizer * directRamifiedQuotient r) = 0
  rw [map_mul, ramifiedEval_uniformizer, zero_mul]

/-- The direct factor is not divisible by the square of the ramified prime.
The proof uses the endpoint-right nondivisibility stored in the summit, not
the integer norm identity. -/
theorem directLinearFactor_not_mem_ramifiedPrime_sq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    directLinearFactor r ∉ ramifiedPrime ^ 2 := by
  intro hsquare
  rw [ramifiedPrime_eq_span_uniformizer,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hsquare
  rcases hsquare with ⟨c, hc⟩
  have hcancel :
      ramifiedUniformizer * directRamifiedQuotient r =
        ramifiedUniformizer * (ramifiedUniformizer * c) := by
    rw [← directLinearFactor_eq_uniformizer_mul_quotient r, hc]
    ring
  have hquotient :
      directRamifiedQuotient r = ramifiedUniformizer * c :=
    mul_left_cancel₀ ramifiedUniformizer_ne_zero hcancel
  apply r.summit.endpointRight_not_seven_dvd
  have hzero :
      (r.summit.endpointRight : ZMod 7) = 0 := by
    rw [← ramifiedEval_directRamifiedQuotient r, hquotient,
      map_mul, ramifiedEval_uniformizer, zero_mul]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hzero

/-- The explicit direct factor has the same integral cyclotomic norm as the
source-level norm used by the six-phase product API. -/
theorem cyclotomicNormHom_directLinearFactor
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    cyclotomicNormHom (directLinearFactor r) =
      directCyclotomicNorm r.summit.endpointLeft
        r.summit.endpointRight := by
  have hquad :
      QuadraticAlgebra.norm (directLinearFactor r) =
        directRelativeNorm r.summit.endpointLeft
          r.summit.endpointRight := by
    apply ofReal_injective
    change algebraMap SevenRealCubicInt
      SevenCyclotomicDegreeSixInt.Ring
        (QuadraticAlgebra.norm (directLinearFactor r)) = _
    rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    simpa [directLinearFactor] using
      directLinearFactor_mul_star
        r.summit.endpointLeft r.summit.endpointRight
  rw [cyclotomicNormHom_apply, hquad]
  rfl

/-- The existing six-phase product specializes directly to the residual
seventh-power stored by the same provenance. -/
theorem sixPhaseProduct_directLinearFactor
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    sixPhaseProduct (directLinearFactor r) =
      (7 * (r.summit.residualRoot : ℤ) ^ 7 :
        SevenCyclotomicDegreeSixInt.Ring) := by
  rw [sixPhaseProduct_eq_ofReal_cyclotomicNorm,
    cyclotomicNormHom_directLinearFactor,
    directCyclotomicNorm_eq_seven_mul_residual_pow]
  change
    ((7 * (r.summit.residualRoot : ℤ) ^ 7 : ℤ) :
      SevenCyclotomicDegreeSixInt.Ring) =
      7 * ((r.summit.residualRoot : ℤ) :
        SevenCyclotomicDegreeSixInt.Ring) ^ 7
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]

end
end DkMath.FLT.Seven
