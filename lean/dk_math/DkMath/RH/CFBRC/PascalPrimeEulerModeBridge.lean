/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalPrimeEulerEnergyBridge
import DkMath.RH.CFBRC.PrimeMirrorEtaBridge
import DkMath.RH.CFBRC.PrimeMirrorEtaEnergyBridge
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.PascalPrimeEulerModeBridge"

/-!
# Pascal–Euler primitive-mode bridge

The reciprocal defect of one Euler factor recovers the primitive mode `p⁻ˢ`.
Its complex finite wave retains the vertical phase `t log p`, while its
original/mirror norm ratio recovers the horizontal prime-mirror Gap.  The
wave is prime-only: it is not the full logarithmic derivative, and this
module does not identify the Euler product, wave, and positive energy.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.NumberTheory
open DkMath.RH.EulerZeta
open DkMath.RH.Weave.Analytic

/-- The primitive `p`-mode extracted as the reciprocal defect of an Euler factor. -/
noncomputable def eulerPrimePrimitiveMode (p : ℕ) (s : ℂ) : ℂ :=
  1 - (eulerZetaFactor p s)⁻¹

/-- The Euler reciprocal defect is exactly the inverse complex power `p⁻ˢ`. -/
theorem eulerPrimePrimitiveMode_eq_inv_cpow
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePrimitiveMode p s = (((p : ℂ) ^ s))⁻¹ := by
  unfold eulerPrimePrimitiveMode eulerZetaFactor
  have hpow : (p : ℂ) ^ s ≠ 0 := by
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp.ne_zero))
  field_simp
  ring

/-- The same primitive mode in negative-exponent notation. -/
theorem eulerPrimePrimitiveMode_eq_cpow_neg
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePrimitiveMode p s = (p : ℂ) ^ (-s) := by
  rw [eulerPrimePrimitiveMode_eq_inv_cpow hp]
  rw [← Complex.cpow_neg]

/-- The Euler primitive mode agrees with the unsigned eta mode at index `p - 1`. -/
theorem eulerPrimePrimitiveMode_eq_etaUnsignedVector
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePrimitiveMode p s = etaUnsignedVector s (p - 1) := by
  rw [eulerPrimePrimitiveMode_eq_inv_cpow hp,
    etaUnsignedVector_eq_one_div_cpow]
  have hp0 : 0 < p := hp.pos
  norm_num [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp.ne_zero)]

/-- Original/mirror norm ratio of the Euler primitive mode. -/
noncomputable def eulerPrimePrimitiveMirrorRatio (p : ℕ) (s : ℂ) : ℝ :=
  ‖eulerPrimePrimitiveMode p (criticalMirror s)‖ /
    ‖eulerPrimePrimitiveMode p s‖

/-- The primitive-mode mirror ratio is strictly positive at every prime mode. -/
theorem eulerPrimePrimitiveMirrorRatio_pos
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    0 < eulerPrimePrimitiveMirrorRatio p s := by
  rw [eulerPrimePrimitiveMirrorRatio,
    eulerPrimePrimitiveMode_eq_inv_cpow hp,
    eulerPrimePrimitiveMode_eq_inv_cpow hp]
  apply div_pos
  · exact norm_pos_iff.mpr (inv_ne_zero
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp.ne_zero))))
  · exact norm_pos_iff.mpr (inv_ne_zero
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp.ne_zero))))

/-- The primitive-mode ratio agrees with the eta mirror amplitude ratio. -/
theorem eulerPrimePrimitiveMirrorRatio_eq_etaMirrorAmplitudeRatio
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePrimitiveMirrorRatio p s =
      etaMirrorAmplitudeRatio s (p - 1) := by
  rw [eulerPrimePrimitiveMirrorRatio,
    eulerPrimePrimitiveMode_eq_etaUnsignedVector hp,
    eulerPrimePrimitiveMode_eq_etaUnsignedVector hp]
  simp [etaMirrorAmplitudeRatio, norm_etaSignedVector]

/-- The primitive-mode ratio is the prime-mirror amplitude ratio at `p`. -/
theorem eulerPrimePrimitiveMirrorRatio_eq_primeMirrorAmplitudeRatio
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePrimitiveMirrorRatio p s =
      primeMirrorRightAmplitude p (centeredSigma s.re) /
        primeMirrorLeftAmplitude p (centeredSigma s.re) := by
  rw [eulerPrimePrimitiveMirrorRatio_eq_etaMirrorAmplitudeRatio hp]
  rw [← primeMirrorAmplitudeRatio_eq_etaMirrorAmplitudeRatio s (p - 1)]
  simp [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp.ne_zero)]

/-- Ratio-minus-two is the primitive-mode mirror Gap. -/
noncomputable def eulerPrimePrimitiveMirrorGap (p : ℕ) (s : ℂ) : ℝ :=
  let r := eulerPrimePrimitiveMirrorRatio p s
  r + r⁻¹ - 2

/-- The primitive-mode ratio-gap recovers the existing prime-mirror Gap. -/
theorem eulerPrimePrimitiveMirrorGap_eq_primeMirrorOffsetGapAt
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePrimitiveMirrorGap p s = primeMirrorOffsetGapAt p s := by
  rw [eulerPrimePrimitiveMirrorGap,
    eulerPrimePrimitiveMirrorRatio_eq_etaMirrorAmplitudeRatio hp]
  rw [← etaEndpointIncrementMirrorRatio_eq_etaMirrorAmplitudeRatio]
  change etaEndpointIncrementMirrorGap s (p - 1) = primeMirrorOffsetGapAt p s
  simpa [primeMirrorOffsetGapAt,
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp.ne_zero)] using
    etaEndpointIncrementMirrorGap_eq_primeMirrorOffsetGap s (p - 1)

/-- Primitive-mode mirror Gaps are nonnegative. -/
theorem eulerPrimePrimitiveMirrorGap_nonneg
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    0 ≤ eulerPrimePrimitiveMirrorGap p s := by
  rw [eulerPrimePrimitiveMirrorGap_eq_primeMirrorOffsetGapAt hp]
  exact primeMirrorOffsetGap_nonneg _ _

/-- Primitive-mode mirror balance occurs exactly on the critical line. -/
theorem eulerPrimePrimitiveMirrorGap_eq_zero_iff_re_eq_half
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePrimitiveMirrorGap p s = 0 ↔ s.re = (1 : ℝ) / 2 := by
  rw [eulerPrimePrimitiveMirrorGap_eq_primeMirrorOffsetGapAt hp,
    primeMirrorOffsetGapAt_eq_zero_iff_re_eq_half hp.one_lt]

/-- Finite prime-only complex wave formed from primitive modes and `log p`. -/
noncomputable def pascalPrimeEulerPrimitiveLogWaveUpTo
    (N : ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ pascalPrimeCoordinateSupportUpTo N,
    (Real.log (p : ℝ) : ℂ) * eulerPrimePrimitiveMode p s

/-- The primitive log wave receives one new mode at a prime birth row. -/
@[simp] theorem pascalPrimeEulerPrimitiveLogWaveUpTo_succ_sub
    (N : ℕ) (s : ℂ) :
    pascalPrimeEulerPrimitiveLogWaveUpTo (N + 1) s -
        pascalPrimeEulerPrimitiveLogWaveUpTo N s =
      (pascalPrimeBirthLogMass (N + 1) : ℂ) *
        eulerPrimePrimitiveMode (N + 1) s := by
  by_cases hp : Nat.Prime (N + 1)
  · have hnot : N + 1 ∉ pascalPrimeCoordinateSupportUpTo N := by
      rw [mem_pascalPrimeCoordinateSupportUpTo_iff]
      omega
    have hlog : Complex.log ((N + 1 : ℕ) : ℂ) =
        (Real.log ((N + 1 : ℕ) : ℝ) : ℂ) := by
      simpa using (Complex.ofReal_log (show 0 ≤ ((N + 1 : ℕ) : ℝ) by positivity)).symm
    have hlog' : Complex.log ((N : ℂ) + 1) =
        (Real.log ((N : ℝ) + 1) : ℂ) := by
      convert hlog using 1 <;> norm_num
    simp [pascalPrimeBirthLogMass_eq, pascalPrimeCoordinateSupportUpTo_succ,
      pascalPrimeEulerPrimitiveLogWaveUpTo, hp, hnot, hlog']
  · simp [pascalPrimeBirthLogMass_eq, pascalPrimeCoordinateSupportUpTo_succ,
      pascalPrimeEulerPrimitiveLogWaveUpTo, hp]

/-- Additive form of the primitive log-wave successor update. -/
@[simp] theorem pascalPrimeEulerPrimitiveLogWaveUpTo_succ_eq
    (N : ℕ) (s : ℂ) :
    pascalPrimeEulerPrimitiveLogWaveUpTo (N + 1) s =
      pascalPrimeEulerPrimitiveLogWaveUpTo N s +
        (pascalPrimeBirthLogMass (N + 1) : ℂ) *
          eulerPrimePrimitiveMode (N + 1) s := by
  have h := pascalPrimeEulerPrimitiveLogWaveUpTo_succ_sub N s
  calc
    pascalPrimeEulerPrimitiveLogWaveUpTo (N + 1) s =
        (pascalPrimeEulerPrimitiveLogWaveUpTo (N + 1) s -
          pascalPrimeEulerPrimitiveLogWaveUpTo N s) +
          pascalPrimeEulerPrimitiveLogWaveUpTo N s := by ring
    _ = (pascalPrimeBirthLogMass (N + 1) : ℂ) *
          eulerPrimePrimitiveMode (N + 1) s +
          pascalPrimeEulerPrimitiveLogWaveUpTo N s := by rw [h]
    _ = _ := add_comm _ _

/-- PPW-006 energy rewritten as the sum of primitive-mode ratio-Gaps. -/
theorem pascalPrimeMirrorLogEnergyUpTo_eq_primitiveMirrorGapSum
    (N : ℕ) (s : ℂ) :
    pascalPrimeMirrorLogEnergyUpTo N s =
      ∑ p ∈ pascalPrimeCoordinateSupportUpTo N,
        Real.log (p : ℝ) * eulerPrimePrimitiveMirrorGap p s := by
  apply Finset.sum_congr rfl
  intro p hp
  rw [eulerPrimePrimitiveMirrorGap_eq_primeMirrorOffsetGapAt
    ((mem_pascalPrimeCoordinateSupportUpTo_iff.mp hp).1)]

end DkMath.RH.CFBRCProjection
