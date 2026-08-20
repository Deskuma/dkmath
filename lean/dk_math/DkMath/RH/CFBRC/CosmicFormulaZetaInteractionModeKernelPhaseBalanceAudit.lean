/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaInteractionPrimePowerEventAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideModeKernelPhaseAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideInteractionPhaseBoundaryAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaInteractionModeKernelPhaseBalanceAudit"

/-!
# CFZP-006T: prime-power mode-kernel phase balance

The positive von Mangoldt factor is separated from the signed finite mode
kernel.  The kernel is then represented by a positive scale times the
difference of two real phase primitives.  This exposes the exact balance
condition while leaving the universal ordering and sign provider open.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open Filter
open MeasureTheory
open Set
open scoped ComplexConjugate Interval Topology

/-! ## A. Prime-power event sign reduction -/

theorem cfzpPrimeSideInteractionCutoffIncrement_pos_iff_modeKernel_pos_of_isPrimePow
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (n : ℕ)
    (hPP : IsPrimePow n) :
    0 < cfzpPrimeSideInteractionCutoffIncrement ε W n ↔
      0 < pascalCenteredXiPrimeSideFiniteModeKernel ε W n := by
  have hΛ : 0 < (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_pos_iff.mpr hPP
  have hscale : 0 < 2 * (ArithmeticFunction.vonMangoldt n : ℝ) :=
    mul_pos (by norm_num) hΛ
  unfold cfzpPrimeSideInteractionCutoffIncrement
  constructor
  · intro h
    rcases (mul_pos_iff.mp h) with hcase | hcase
    · exact hcase.2
    · exact False.elim ((not_lt_of_ge hscale.le) hcase.1)
  · intro h
    exact mul_pos hscale h

theorem cfzpPrimeSideInteractionCutoffIncrement_neg_iff_modeKernel_neg_of_isPrimePow
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (n : ℕ)
    (hPP : IsPrimePow n) :
    cfzpPrimeSideInteractionCutoffIncrement ε W n < 0 ↔
      pascalCenteredXiPrimeSideFiniteModeKernel ε W n < 0 := by
  have hΛ : 0 < (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_pos_iff.mpr hPP
  have hscale : 0 < 2 * (ArithmeticFunction.vonMangoldt n : ℝ) :=
    mul_pos (by norm_num) hΛ
  unfold cfzpPrimeSideInteractionCutoffIncrement
  constructor
  · intro h
    rcases (mul_neg_iff.mp h) with hcase | hcase
    · exact hcase.2
    · exact False.elim ((not_lt_of_ge hscale.le) hcase.1)
  · intro h
    exact mul_neg_of_pos_of_neg hscale h

theorem cfzpPrimeSideInteractionCutoffIncrement_nonneg_iff_modeKernel_nonneg_of_isPrimePow
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (n : ℕ)
    (hPP : IsPrimePow n) :
    0 ≤ cfzpPrimeSideInteractionCutoffIncrement ε W n ↔
      0 ≤ pascalCenteredXiPrimeSideFiniteModeKernel ε W n := by
  have hΛ : 0 < (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_pos_iff.mpr hPP
  have hscale : 0 < 2 * (ArithmeticFunction.vonMangoldt n : ℝ) :=
    mul_pos (by norm_num) hΛ
  unfold cfzpPrimeSideInteractionCutoffIncrement
  constructor
  · intro h
    by_contra hkernel
    have hkernel' : pascalCenteredXiPrimeSideFiniteModeKernel ε W n < 0 :=
      lt_of_not_ge hkernel
    exact (not_lt_of_ge h) (mul_neg_of_pos_of_neg hscale hkernel')
  · intro h
    exact mul_nonneg hscale.le h

theorem cfzpPrimeSideInteractionCutoffIncrement_nonpos_iff_modeKernel_nonpos_of_isPrimePow
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (n : ℕ)
    (hPP : IsPrimePow n) :
    cfzpPrimeSideInteractionCutoffIncrement ε W n ≤ 0 ↔
      pascalCenteredXiPrimeSideFiniteModeKernel ε W n ≤ 0 := by
  have hΛ : 0 < (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_pos_iff.mpr hPP
  have hscale : 0 < 2 * (ArithmeticFunction.vonMangoldt n : ℝ) :=
    mul_pos (by norm_num) hΛ
  unfold cfzpPrimeSideInteractionCutoffIncrement
  constructor
  · intro h
    by_contra hkernel
    have hkernel' : 0 < pascalCenteredXiPrimeSideFiniteModeKernel ε W n :=
      lt_of_not_ge hkernel
    exact (not_lt_of_ge h) (mul_pos hscale hkernel')
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos hscale.le h

theorem cfzpPrimeSideInteractionCutoffIncrement_eq_zero_iff_modeKernel_eq_zero_of_isPrimePow
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (n : ℕ)
    (hPP : IsPrimePow n) :
    cfzpPrimeSideInteractionCutoffIncrement ε W n = 0 ↔
      pascalCenteredXiPrimeSideFiniteModeKernel ε W n = 0 := by
  have hΛ : 0 < (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_pos_iff.mpr hPP
  have hscale : 2 * (ArithmeticFunction.vonMangoldt n : ℝ) ≠ 0 :=
    (mul_ne_zero (by norm_num) hΛ.ne')
  unfold cfzpPrimeSideInteractionCutoffIncrement
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hscale
  · intro h
    rw [h, mul_zero]

/-! ## B. CFZP phase coordinates and positive carrier -/

noncomputable def cfzpModePhaseAbscissa
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  W.rectangle.σ - (1 / 2 : ℝ)

noncomputable def cfzpModePhaseFrequencyPlus
    (ε : ℝ) (n : ℕ) : ℝ :=
  ε - Real.log (n : ℝ)

noncomputable def cfzpModePhaseFrequencyMinus
    (ε : ℝ) (n : ℕ) : ℝ :=
  -ε - Real.log (n : ℝ)

noncomputable def cfzpModeCriticalScale (n : ℕ) : ℝ :=
  Real.exp (-(1 / 2 : ℝ) * Real.log (n : ℝ))

theorem cfzpModeCriticalScale_pos (n : ℕ) :
    0 < cfzpModeCriticalScale n := by
  exact Real.exp_pos _

theorem cfzpModeCriticalScale_eq_phaseCarrier
    (ε : ℝ) (n : ℕ) :
    pascalCenteredXiPrimeSidePhaseCarrier ε n =
      (2 * ε)⁻¹ * cfzpModeCriticalScale n := by
  rfl

/-! ## C. Pointwise phase-density identity -/

theorem cfzpPrimeSideFiniteModeBoundaryPhaseIntegrand_eq_phaseDensityDifference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {n : ℕ} (hn : 0 < n)
    (t : ℝ) :
    pascalCenteredXiPrimeSideFiniteModeBoundaryPhaseIntegrand ε W n t =
      (2 * ε)⁻¹ * cfzpModeCriticalScale n *
        (pascalCenteredXiPrimeSidePhaseIntegrand
          (cfzpModePhaseAbscissa W) (cfzpModePhaseFrequencyPlus ε n) t -
          pascalCenteredXiPrimeSidePhaseIntegrand
            (cfzpModePhaseAbscissa W) (cfzpModePhaseFrequencyMinus ε n) t) := by
  simpa [cfzpModePhaseAbscissa, cfzpModePhaseFrequencyPlus,
    cfzpModePhaseFrequencyMinus, cfzpModeCriticalScale,
    pascalCenteredXiPrimeSidePhaseCarrier,
    pascalCenteredXiPrimeSidePhaseFrequencyPlus,
    pascalCenteredXiPrimeSidePhaseFrequencyMinus] using
    (pascalCenteredXiPrimeSideFiniteModeBoundaryPhaseIntegrand_eq_phaseDensityDifference
      hε W hn t)

/-! ## D. Kernel as a scaled difference of real phase primitives -/

theorem cfzpPrimeSideFiniteModeKernel_eq_scaled_phasePrimitiveDifference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {n : ℕ} (hn : 0 < n) :
    pascalCenteredXiPrimeSideFiniteModeKernel ε W n =
      (2 * ε)⁻¹ * cfzpModeCriticalScale n *
        (pascalCenteredXiPrimeSidePhasePrimitive
          (cfzpModePhaseAbscissa W) (cfzpModePhaseFrequencyPlus ε n)
            W.rectangle.T -
          pascalCenteredXiPrimeSidePhasePrimitive
            (cfzpModePhaseAbscissa W) (cfzpModePhaseFrequencyMinus ε n)
            W.rectangle.T) := by
  simpa [cfzpModePhaseAbscissa, cfzpModePhaseFrequencyPlus,
    cfzpModePhaseFrequencyMinus, cfzpModeCriticalScale,
    pascalCenteredXiPrimeSidePhaseCarrier,
    pascalCenteredXiPrimeSidePhaseFrequencyPlus,
    pascalCenteredXiPrimeSidePhaseFrequencyMinus] using
    (pascalCenteredXiPrimeSideFiniteModeKernel_eq_phasePrimitive_difference
      hε W hn)

private theorem cfzpModePhaseScale_pos
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    0 < (2 * ε)⁻¹ * cfzpModeCriticalScale n := by
  exact mul_pos (inv_pos.mpr (mul_pos (by norm_num) hε))
    (cfzpModeCriticalScale_pos n)

/-! ## E. Kernel sign and zero are primitive order statements -/

theorem cfzpPrimeSideFiniteModeKernel_eq_zero_iff_phasePrimitive_eq
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {n : ℕ} (hn : 0 < n) :
    pascalCenteredXiPrimeSideFiniteModeKernel ε W n = 0 ↔
      pascalCenteredXiPrimeSidePhasePrimitive
          (cfzpModePhaseAbscissa W) (cfzpModePhaseFrequencyPlus ε n)
            W.rectangle.T =
        pascalCenteredXiPrimeSidePhasePrimitive
          (cfzpModePhaseAbscissa W) (cfzpModePhaseFrequencyMinus ε n)
            W.rectangle.T := by
  rw [cfzpPrimeSideFiniteModeKernel_eq_scaled_phasePrimitiveDifference hε W hn]
  have hs := cfzpModePhaseScale_pos hε n
  constructor
  · intro h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hs.ne')
  · intro h
    rw [sub_eq_zero.mpr h, mul_zero]

theorem cfzpPrimeSideFiniteModeKernel_pos_iff_phasePrimitive_lt
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {n : ℕ} (hn : 0 < n) :
    0 < pascalCenteredXiPrimeSideFiniteModeKernel ε W n ↔
      pascalCenteredXiPrimeSidePhasePrimitive
          (cfzpModePhaseAbscissa W) (cfzpModePhaseFrequencyMinus ε n)
            W.rectangle.T <
        pascalCenteredXiPrimeSidePhasePrimitive
          (cfzpModePhaseAbscissa W) (cfzpModePhaseFrequencyPlus ε n)
            W.rectangle.T := by
  rw [cfzpPrimeSideFiniteModeKernel_eq_scaled_phasePrimitiveDifference hε W hn]
  have hs := cfzpModePhaseScale_pos hε n
  constructor
  · intro h
    rcases (mul_pos_iff.mp h) with hcase | hcase
    · exact sub_pos.mp hcase.2
    · exact False.elim ((not_lt_of_ge hs.le) hcase.1)
  · intro h
    exact mul_pos hs (sub_pos.mpr h)

theorem cfzpPrimeSideFiniteModeKernel_neg_iff_phasePrimitive_gt
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {n : ℕ} (hn : 0 < n) :
    pascalCenteredXiPrimeSideFiniteModeKernel ε W n < 0 ↔
      pascalCenteredXiPrimeSidePhasePrimitive
          (cfzpModePhaseAbscissa W) (cfzpModePhaseFrequencyPlus ε n)
            W.rectangle.T <
        pascalCenteredXiPrimeSidePhasePrimitive
          (cfzpModePhaseAbscissa W) (cfzpModePhaseFrequencyMinus ε n)
            W.rectangle.T := by
  rw [cfzpPrimeSideFiniteModeKernel_eq_scaled_phasePrimitiveDifference hε W hn]
  have hs := cfzpModePhaseScale_pos hε n
  constructor
  · intro h
    rcases (mul_neg_iff.mp h) with hcase | hcase
    · exact sub_neg.mp hcase.2
    · exact False.elim ((not_lt_of_ge hs.le) hcase.1)
  · intro h
    exact mul_neg_of_pos_of_neg hs (sub_neg.mpr h)

theorem cfzpPrimeSideFiniteModeKernel_nonneg_iff_phasePrimitive_le
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {n : ℕ} (hn : 0 < n) :
    0 ≤ pascalCenteredXiPrimeSideFiniteModeKernel ε W n ↔
      pascalCenteredXiPrimeSidePhasePrimitive
          (cfzpModePhaseAbscissa W) (cfzpModePhaseFrequencyMinus ε n)
            W.rectangle.T ≤
        pascalCenteredXiPrimeSidePhasePrimitive
          (cfzpModePhaseAbscissa W) (cfzpModePhaseFrequencyPlus ε n)
            W.rectangle.T := by
  rw [cfzpPrimeSideFiniteModeKernel_eq_scaled_phasePrimitiveDifference hε W hn]
  have hs := cfzpModePhaseScale_pos hε n
  constructor
  · intro h
    by_contra hnot
    have hdiff :
        pascalCenteredXiPrimeSidePhasePrimitive
            (cfzpModePhaseAbscissa W) (cfzpModePhaseFrequencyPlus ε n)
              W.rectangle.T -
          pascalCenteredXiPrimeSidePhasePrimitive
            (cfzpModePhaseAbscissa W) (cfzpModePhaseFrequencyMinus ε n)
              W.rectangle.T < 0 := by
      linarith
    exact (not_lt_of_ge h) (mul_neg_of_pos_of_neg hs hdiff)
  · intro h
    exact mul_nonneg hs.le (sub_nonneg.mpr h)

theorem cfzpPrimeSideFiniteModeKernel_nonpos_iff_phasePrimitive_ge
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {n : ℕ} (hn : 0 < n) :
    pascalCenteredXiPrimeSideFiniteModeKernel ε W n ≤ 0 ↔
      pascalCenteredXiPrimeSidePhasePrimitive
          (cfzpModePhaseAbscissa W) (cfzpModePhaseFrequencyPlus ε n)
            W.rectangle.T ≤
        pascalCenteredXiPrimeSidePhasePrimitive
          (cfzpModePhaseAbscissa W) (cfzpModePhaseFrequencyMinus ε n)
            W.rectangle.T := by
  rw [cfzpPrimeSideFiniteModeKernel_eq_scaled_phasePrimitiveDifference hε W hn]
  have hs := cfzpModePhaseScale_pos hε n
  constructor
  · intro h
    by_contra hnot
    have hdiff : 0 <
        pascalCenteredXiPrimeSidePhasePrimitive
            (cfzpModePhaseAbscissa W) (cfzpModePhaseFrequencyPlus ε n)
              W.rectangle.T -
          pascalCenteredXiPrimeSidePhasePrimitive
            (cfzpModePhaseAbscissa W) (cfzpModePhaseFrequencyMinus ε n)
              W.rectangle.T := by
      linarith
    exact (not_lt_of_ge h) (mul_pos hs hdiff)
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos hs.le (sub_nonpos.mpr h)

/-! ## F. Prime-power frequencies and phase balance -/

theorem cfzpModePhaseFrequencyPlus_eq_of_eq_prime_pow
    {ε : ℝ} {p k : ℕ} (_hp : Nat.Prime p) (_hk : 0 < k) :
    cfzpModePhaseFrequencyPlus ε (p ^ k) =
      ε - (k : ℝ) * Real.log (p : ℝ) := by
  rw [cfzpModePhaseFrequencyPlus, Nat.cast_pow, Real.log_pow]

theorem cfzpModePhaseFrequencyMinus_eq_of_eq_prime_pow
    {ε : ℝ} {p k : ℕ} (_hp : Nat.Prime p) (_hk : 0 < k) :
    cfzpModePhaseFrequencyMinus ε (p ^ k) =
      -ε - (k : ℝ) * Real.log (p : ℝ) := by
  rw [cfzpModePhaseFrequencyMinus, Nat.cast_pow, Real.log_pow]

theorem cfzpPrimeSideFiniteModeKernel_eq_scaled_primePowerPhasePrimitiveDifference
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    {p k : ℕ} (hp : Nat.Prime p) (hk : 0 < k) :
    pascalCenteredXiPrimeSideFiniteModeKernel ε W (p ^ k) =
      (2 * ε)⁻¹ * cfzpModeCriticalScale (p ^ k) *
        (pascalCenteredXiPrimeSidePhasePrimitive
          (cfzpModePhaseAbscissa W)
          (ε - (k : ℝ) * Real.log (p : ℝ)) W.rectangle.T -
          pascalCenteredXiPrimeSidePhasePrimitive
            (cfzpModePhaseAbscissa W)
            (-ε - (k : ℝ) * Real.log (p : ℝ)) W.rectangle.T) := by
  rw [cfzpPrimeSideFiniteModeKernel_eq_scaled_phasePrimitiveDifference hε W
    (Nat.pow_pos hp.pos),
    cfzpModePhaseFrequencyPlus_eq_of_eq_prime_pow hp hk,
    cfzpModePhaseFrequencyMinus_eq_of_eq_prime_pow hp hk]

private theorem cfzpPrimePower_isPrimePow {p k : ℕ}
    (hp : Nat.Prime p) (hk : 0 < k) : IsPrimePow (p ^ k) := by
  exact (isPrimePow_nat_iff (p ^ k)).mpr ⟨p, k, hp, hk, rfl⟩

theorem cfzpPrimePowerInteractionIncrement_eq_zero_iff_phasePrimitive_eq
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    {p k : ℕ} (hp : Nat.Prime p) (hk : 0 < k) :
    cfzpPrimeSideInteractionCutoffIncrement ε W (p ^ k) = 0 ↔
      pascalCenteredXiPrimeSidePhasePrimitive
          (cfzpModePhaseAbscissa W)
          (ε - (k : ℝ) * Real.log (p : ℝ)) W.rectangle.T =
        pascalCenteredXiPrimeSidePhasePrimitive
          (cfzpModePhaseAbscissa W)
          (-ε - (k : ℝ) * Real.log (p : ℝ)) W.rectangle.T := by
  rw [cfzpPrimeSideInteractionCutoffIncrement_eq_zero_iff_modeKernel_eq_zero_of_isPrimePow
    ε W (p ^ k) (cfzpPrimePower_isPrimePow hp hk),
    cfzpPrimeSideFiniteModeKernel_eq_zero_iff_phasePrimitive_eq hε W
      (Nat.pow_pos hp.pos),
    cfzpModePhaseFrequencyPlus_eq_of_eq_prime_pow hp hk,
    cfzpModePhaseFrequencyMinus_eq_of_eq_prime_pow hp hk]

theorem cfzpPrimePowerInteractionIncrement_pos_iff_phasePrimitive_lt
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    {p k : ℕ} (hp : Nat.Prime p) (hk : 0 < k) :
    0 < cfzpPrimeSideInteractionCutoffIncrement ε W (p ^ k) ↔
      pascalCenteredXiPrimeSidePhasePrimitive
          (cfzpModePhaseAbscissa W)
          (-ε - (k : ℝ) * Real.log (p : ℝ)) W.rectangle.T <
        pascalCenteredXiPrimeSidePhasePrimitive
          (cfzpModePhaseAbscissa W)
          (ε - (k : ℝ) * Real.log (p : ℝ)) W.rectangle.T := by
  rw [cfzpPrimeSideInteractionCutoffIncrement_pos_iff_modeKernel_pos_of_isPrimePow
    ε W (p ^ k) (cfzpPrimePower_isPrimePow hp hk),
    cfzpPrimeSideFiniteModeKernel_pos_iff_phasePrimitive_lt hε W
      (Nat.pow_pos hp.pos),
    cfzpModePhaseFrequencyPlus_eq_of_eq_prime_pow hp hk,
    cfzpModePhaseFrequencyMinus_eq_of_eq_prime_pow hp hk]

theorem cfzpPrimePowerInteractionIncrement_neg_iff_phasePrimitive_gt
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    {p k : ℕ} (hp : Nat.Prime p) (hk : 0 < k) :
    cfzpPrimeSideInteractionCutoffIncrement ε W (p ^ k) < 0 ↔
      pascalCenteredXiPrimeSidePhasePrimitive
          (cfzpModePhaseAbscissa W)
          (ε - (k : ℝ) * Real.log (p : ℝ)) W.rectangle.T <
        pascalCenteredXiPrimeSidePhasePrimitive
          (cfzpModePhaseAbscissa W)
          (-ε - (k : ℝ) * Real.log (p : ℝ)) W.rectangle.T := by
  rw [cfzpPrimeSideInteractionCutoffIncrement_neg_iff_modeKernel_neg_of_isPrimePow
    ε W (p ^ k) (cfzpPrimePower_isPrimePow hp hk),
    cfzpPrimeSideFiniteModeKernel_neg_iff_phasePrimitive_gt hε W
      (Nat.pow_pos hp.pos),
    cfzpModePhaseFrequencyPlus_eq_of_eq_prime_pow hp hk,
    cfzpModePhaseFrequencyMinus_eq_of_eq_prime_pow hp hk]

/-! ## G. Zero-frequency boundary -/

theorem cfzpModePhaseFrequencyMinus_neg_of_prime_pow
    {ε : ℝ} (hε : 0 < ε) {p k : ℕ}
    (hp : Nat.Prime p) (hk : 0 < k) :
    cfzpModePhaseFrequencyMinus ε (p ^ k) < 0 := by
  rw [cfzpModePhaseFrequencyMinus_eq_of_eq_prime_pow hp hk]
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hlog : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hp.one_lt
  nlinarith [mul_pos hkR hlog]

theorem cfzpModePhaseFrequencyPlus_eq_zero_iff_of_prime_pow
    {ε : ℝ} {p k : ℕ} (hp : Nat.Prime p) (hk : 0 < k) :
    cfzpModePhaseFrequencyPlus ε (p ^ k) = 0 ↔
      ε = (k : ℝ) * Real.log (p : ℝ) := by
  rw [cfzpModePhaseFrequencyPlus_eq_of_eq_prime_pow hp hk]
  constructor <;> intro h <;> linarith

inductive CfzpPrimePowerPhasePrimitiveOrderingGap : Prop
  | noIndependentPrimePowerPhasePrimitiveOrderingProvider

end DkMath.RH.CFBRCProjection
