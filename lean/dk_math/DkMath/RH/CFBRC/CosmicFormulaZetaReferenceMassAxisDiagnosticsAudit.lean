/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaUniformReadyGoodEfficiencyFloorAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaReferenceMassAxisDiagnosticsAudit"

/-!
# CFZP-033: reference-mass axis diagnostics

This module rewrites the finite prime-power reference mass in the logarithmic
coordinate `u = j * log p`.  The critical carrier and the boundary profile
recombine to `exp(a * ε) * exp(-σ * u)`, where `a = σ - 1 / 2`.  The remaining
finite shape is compared above and below by constants times `1 / u`.

Only finite identities and finite two-sided comparisons are recorded here.
No infinite sum, density theorem, summability statement, or weighted Good
coverage provider is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Set

/-! ## Gate A: canonical logarithmic coordinate -/

/-- The logarithmic coordinate of a prime-power mode. -/
noncomputable def cfzp033PrimePowerLogCoordinate (p j : ℕ) : ℝ :=
  (j : ℝ) * Real.log (p : ℝ)

/-- The phase center is exactly the canonical logarithmic coordinate. -/
theorem cfzp033PrimePowerPhaseCenter_eq_logCoordinate (p j : ℕ) :
    cfzpPrimePowerPhaseCenter p j =
      cfzp033PrimePowerLogCoordinate p j := by
  rfl

/-- The left phase magnitude is the coordinate minus the safe width. -/
theorem cfzp033PrimePowerPhaseMagnitudeLeft_eq_logCoordinate_sub
    (ε : ℝ) (p j : ℕ) :
    cfzpPrimePowerPhaseMagnitudeLeft ε p j =
      cfzp033PrimePowerLogCoordinate p j - ε := by
  rfl

/-- The right phase magnitude is the coordinate plus the safe width. -/
theorem cfzp033PrimePowerPhaseMagnitudeRight_eq_logCoordinate_add
    (ε : ℝ) (p j : ℕ) :
    cfzpPrimePowerPhaseMagnitudeRight ε p j =
      cfzp033PrimePowerLogCoordinate p j + ε := by
  rfl

/-- The right phase angle is the rectangle scale times the right coordinate. -/
theorem cfzp033PrimePowerPhaseAngleRight_eq_T_mul_logCoordinate_add
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ) :
    cfzpPrimePowerPhaseAngleRight ε W p j =
      W.rectangle.T * (cfzp033PrimePowerLogCoordinate p j + ε) := by
  rw [cfzpPrimePowerPhaseAngleRight_eq_rectangleT_mul_phaseMagnitudeRight,
    cfzp033PrimePowerPhaseMagnitudeRight_eq_logCoordinate_add]

/-- The prime axis is the ordinary logarithmic prime coordinate. -/
theorem cfzp033PrimePowerLogCoordinate_one (p : ℕ) :
    cfzp033PrimePowerLogCoordinate p 1 = Real.log (p : ℝ) := by
  unfold cfzp033PrimePowerLogCoordinate
  norm_num

/-- Increasing the exponent by one adds one prime logarithm. -/
theorem cfzp033PrimePowerLogCoordinate_succ (p j : ℕ) :
    cfzp033PrimePowerLogCoordinate p (j + 1) =
      cfzp033PrimePowerLogCoordinate p j + Real.log (p : ℝ) := by
  unfold cfzp033PrimePowerLogCoordinate
  push_cast
  ring

/-- Positive prime-power coordinates are positive on safe cells. -/
theorem cfzp033PrimePowerLogCoordinate_pos
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    0 < cfzp033PrimePowerLogCoordinate p j := by
  unfold cfzp033PrimePowerLogCoordinate
  exact mul_pos (by exact_mod_cast hj)
    (Real.log_pos (by exact_mod_cast hp.one_lt))

/-! ## Gate B: critical-scale and boundary recombination -/

/-- The critical scale and boundary exponential factors recombine to `σ`. -/
theorem cfzp033CriticalBoundaryExp_recombine_sigma
    (ε u : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    Real.exp (-(1 / 2 : ℝ) * u) *
        Real.exp (-(cfzpModePhaseAbscissa W) * (u - ε)) =
      Real.exp ((cfzpModePhaseAbscissa W) * ε) *
        Real.exp (-(W.rectangle.σ) * u) := by
  rw [← Real.exp_add]
  rw [← Real.exp_add]
  unfold cfzpModePhaseAbscissa
  congr 1
  ring_nf

/-- The recombination identity specialized to a prime-power coordinate. -/
theorem cfzp033CriticalBoundaryExp_recombine_sigma_primePower
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (p j : ℕ) :
    Real.exp (-(1 / 2 : ℝ) * cfzp033PrimePowerLogCoordinate p j) *
        Real.exp (-(cfzpModePhaseAbscissa W) *
          (cfzp033PrimePowerLogCoordinate p j - ε)) =
      Real.exp ((cfzpModePhaseAbscissa W) * ε) *
        Real.exp (-(W.rectangle.σ) * cfzp033PrimePowerLogCoordinate p j) :=
  cfzp033CriticalBoundaryExp_recombine_sigma ε
    (cfzp033PrimePowerLogCoordinate p j) W

/-! ## Gate C: exact reduced reference-mass factorization -/

/-- The finite shape left after removing carrier and sigma-decay factors. -/
noncomputable def cfzp033ReferenceMassReducedShape
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  cfzp029PhaseDerivativeCoreAbsEnvelope
      (cfzpModePhaseAspectRatio W)
      (W.rectangle.T * (u + ε)) /
    (u - ε) ^ 3

/-- Exact reference-mass factorization in the logarithmic coordinate. -/
theorem cfzp033PrimePowerReferenceMass_eq_sigma_decay
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    cfzp031PrimePowerReferenceMass ε W p j =
      2 * Real.log (p : ℝ) *
        Real.exp ((cfzpModePhaseAbscissa W) * ε) *
        Real.exp (-(W.rectangle.σ) *
          cfzp033PrimePowerLogCoordinate p j) *
        cfzp033ReferenceMassReducedShape ε W
          (cfzp033PrimePowerLogCoordinate p j) := by
  have hmag := cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
    hε hε2 hp hj
  unfold cfzp031PrimePowerReferenceMass cfzp030PrimePowerCriticalCarrier
    cfzp030BadLocalShape cfzp029CenteredProfileDerivativeAbsBound
    cfzp029CenteredDerivativePrefactorCeiling
    cfzp033ReferenceMassReducedShape
  rw [cfzp030ModeCriticalScale_prime_pow_eq_exp,
    cfzp033PrimePowerPhaseMagnitudeLeft_eq_logCoordinate_sub,
    cfzp033PrimePowerPhaseAngleRight_eq_T_mul_logCoordinate_add]
  dsimp
  have hexp :
      Real.exp (-(j : ℝ) / 2 * Real.log (p : ℝ)) *
          Real.exp (-(cfzpModePhaseAbscissa W) *
            (cfzp033PrimePowerLogCoordinate p j - ε)) =
        Real.exp ((cfzpModePhaseAbscissa W) * ε) *
          Real.exp (-(W.rectangle.σ) *
            cfzp033PrimePowerLogCoordinate p j) := by
    convert cfzp033CriticalBoundaryExp_recombine_sigma_primePower ε W p j
      using 1; unfold cfzp033PrimePowerLogCoordinate; ring_nf
  rw [show
      2 * Real.log (p : ℝ) *
          Real.exp (-(j : ℝ) / 2 * Real.log (p : ℝ)) *
          (Real.exp (-(cfzpModePhaseAbscissa W) *
            (cfzp033PrimePowerLogCoordinate p j - ε)) /
            (cfzp033PrimePowerLogCoordinate p j - ε) ^ 3 *
            cfzp029PhaseDerivativeCoreAbsEnvelope
              (cfzpModePhaseAspectRatio W)
              (W.rectangle.T *
                (cfzp033PrimePowerLogCoordinate p j + ε))) =
        2 * Real.log (p : ℝ) *
          (Real.exp (-(j : ℝ) / 2 * Real.log (p : ℝ)) *
            Real.exp (-(cfzpModePhaseAbscissa W) *
              (cfzp033PrimePowerLogCoordinate p j - ε))) *
          (cfzp029PhaseDerivativeCoreAbsEnvelope
              (cfzpModePhaseAspectRatio W)
              (W.rectangle.T *
                (cfzp033PrimePowerLogCoordinate p j + ε)) /
            (cfzp033PrimePowerLogCoordinate p j - ε) ^ 3) by ring]
  rw [hexp]
  ring_nf

/-! ## Gate D: reduced-shape polynomial normal form -/

/-- The reduced shape reuses CFZP-032's subcritical polynomial envelope. -/
theorem cfzp033ReferenceMassReducedShape_eq_polynomial
    {ε u : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    (hsub : Cfzp027SubcriticalPhaseAspect W) :
    cfzp033ReferenceMassReducedShape ε W u =
      (cfzp032SubcriticalQuadraticCoefficient
          (cfzpModePhaseAspectRatio W) *
          (W.rectangle.T * (u + ε)) ^ 2 +
        2 * (cfzpModePhaseAspectRatio W + 1) *
          (W.rectangle.T * (u + ε)) + 2) /
        (u - ε) ^ 3 := by
  unfold cfzp033ReferenceMassReducedShape
  rw [cfzp032PhaseEnvelope_eq_quadratic
    (cfzpModePhaseAspectRatio_pos W).le hsub]

/-! ## Gate E: finite two-sided reduced-shape bounds -/

/-- A safe large coordinate gives the reduced shape's lower `1 / u` bound. -/
theorem cfzp033ReferenceMassReducedShape_lower
    {ε u : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hu1 : 1 ≤ u) (h2ε : 2 * ε ≤ u) :
    W.rectangle.T ^ 2 / u ≤
      cfzp033ReferenceMassReducedShape ε W u := by
  have hε0 : 0 ≤ ε := hε.le
  have hu : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hden : 0 < u - ε := by nlinarith
  have hden_le : u - ε ≤ u := by linarith
  have hden_cube : (u - ε) ^ 3 ≤ u ^ 3 := by gcongr
  have hα0 : 0 ≤ cfzpModePhaseAspectRatio W :=
    (cfzpModePhaseAspectRatio_pos W).le
  have hq : 1 ≤ cfzp032SubcriticalQuadraticCoefficient
      (cfzpModePhaseAspectRatio W) :=
    cfzp032SubcriticalQuadraticCoefficient_ge_one hα0 hsub
  have hT : 0 < W.rectangle.T := W.rectangle.hT
  have hR : 0 ≤ W.rectangle.T * (u + ε) := by positivity
  have hRu : W.rectangle.T * u ≤ W.rectangle.T * (u + ε) := by
    exact mul_le_mul_of_nonneg_left (by linarith) hT.le
  have hTu : 0 ≤ W.rectangle.T * u := by positivity
  have hRsq : (W.rectangle.T * u) ^ 2 ≤
      (W.rectangle.T * (u + ε)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hRu)
      (add_nonneg hTu hR)]
  have hnum : W.rectangle.T ^ 2 * u ^ 2 ≤
      cfzp029PhaseDerivativeCoreAbsEnvelope
        (cfzpModePhaseAspectRatio W)
        (W.rectangle.T * (u + ε)) := by
    rw [cfzp032PhaseEnvelope_eq_quadratic hα0 hsub]
    nlinarith [hRsq]
  have hfrac : W.rectangle.T ^ 2 / u ≤
      W.rectangle.T ^ 2 * u ^ 2 / (u - ε) ^ 3 := by
    apply (div_le_div_iff₀ hu (pow_pos hden 3)).2
    have hden_cube' : (u - ε) ^ 3 ≤ u ^ 2 * u := by
      convert hden_cube using 1; ring
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hden_cube' (sq_nonneg W.rectangle.T))
  unfold cfzp033ReferenceMassReducedShape
  exact hfrac.trans (div_le_div_of_nonneg_right hnum (by positivity))

/-- A safe large coordinate gives a coarse upper `1 / u` bound. -/
theorem cfzp033ReferenceMassReducedShape_upper
    {ε u : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hu1 : 1 ≤ u) (h2ε : 2 * ε ≤ u) :
    cfzp033ReferenceMassReducedShape ε W u ≤
      64 * (W.rectangle.T + 1) ^ 2 / u := by
  have hε0 : 0 ≤ ε := hε.le
  have hu : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hden : 0 < u - ε := by nlinarith
  have hden_lower : u / 2 ≤ u - ε := by nlinarith
  have hα0 : 0 ≤ cfzpModePhaseAspectRatio W :=
    (cfzpModePhaseAspectRatio_pos W).le
  have hq : cfzp032SubcriticalQuadraticCoefficient
      (cfzpModePhaseAspectRatio W) ≤ 2 := by
    unfold cfzp032SubcriticalQuadraticCoefficient
    nlinarith [sq_nonneg (1 - cfzpModePhaseAspectRatio W)]
  have hT : 0 < W.rectangle.T := W.rectangle.hT
  have hplus : u + ε ≤ 3 * u / 2 := by nlinarith
  have hR : 0 ≤ W.rectangle.T * (u + ε) := by positivity
  have hRbound : W.rectangle.T * (u + ε) ≤
      3 * W.rectangle.T * u / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hplus hT.le]
  have hRsq : (W.rectangle.T * (u + ε)) ^ 2 ≤
      (3 * W.rectangle.T * u / 2) ^ 2 := by
    nlinarith
  have hαle : cfzpModePhaseAspectRatio W ≤ 1 := hsub.le
  have hnum :
      cfzp029PhaseDerivativeCoreAbsEnvelope
        (cfzpModePhaseAspectRatio W)
        (W.rectangle.T * (u + ε)) ≤
      8 * (W.rectangle.T + 1) ^ 2 * u ^ 2 := by
    rw [cfzp032PhaseEnvelope_eq_quadratic hα0 hsub]
    nlinarith [hRsq, sq_nonneg (W.rectangle.T + 1), sq_nonneg u]
  have hden_cube : u ^ 3 / 8 ≤ (u - ε) ^ 3 := by
    have hpow : (u / 2) ^ 3 ≤ (u - ε) ^ 3 := by gcongr
    convert hpow using 1; norm_num [div_pow]
  have hmain :
      cfzp029PhaseDerivativeCoreAbsEnvelope
        (cfzpModePhaseAspectRatio W)
        (W.rectangle.T * (u + ε)) /
        (u - ε) ^ 3 ≤
      64 * (W.rectangle.T + 1) ^ 2 / u := by
    apply (div_le_iff₀ (pow_pos hden 3)).2
    have hconst : 0 ≤ 8 * (W.rectangle.T + 1) ^ 2 := by positivity
    have hcross : 8 * (W.rectangle.T + 1) ^ 2 * u ^ 2 ≤
        (64 * (W.rectangle.T + 1) ^ 2 / u) * (u - ε) ^ 3 := by
      field_simp
      nlinarith [hden_cube]
    exact hnum.trans hcross
  exact hmain

/-! ## Gate F: finite prime-axis comparison -/

/-- The reference mass restricted to the prime axis `j = 1`. -/
noncomputable def cfzp033PrimeAxisReferenceMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p : ℕ) : ℝ :=
  cfzp031PrimePowerReferenceMass ε W p 1

/-- Prime-axis reference mass has a finite lower exponential comparison. -/
theorem cfzp033PrimeAxisReferenceMass_lower
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    {p : ℕ} (hp : Nat.Prime p)
    (h2ε : 2 * ε ≤ Real.log (p : ℝ))
    (hlog1 : 1 ≤ Real.log (p : ℝ)) :
    2 * W.rectangle.T ^ 2 *
        Real.exp ((cfzpModePhaseAbscissa W) * ε) *
        Real.exp (-(W.rectangle.σ) * Real.log (p : ℝ)) ≤
      cfzp033PrimeAxisReferenceMass ε W p := by
  have hlog : 0 < Real.log (p : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
  have hshape := cfzp033ReferenceMassReducedShape_lower
    hε W hsub hlog1 h2ε
  have hfactor : 0 ≤
      2 * Real.log (p : ℝ) *
        Real.exp ((cfzpModePhaseAbscissa W) * ε) *
        Real.exp (-(W.rectangle.σ) * Real.log (p : ℝ)) := by positivity
  unfold cfzp033PrimeAxisReferenceMass
  rw [cfzp033PrimePowerReferenceMass_eq_sigma_decay hε hε2 W hp
    (by norm_num), cfzp033PrimePowerLogCoordinate_one]
  calc
    2 * W.rectangle.T ^ 2 *
          Real.exp ((cfzpModePhaseAbscissa W) * ε) *
          Real.exp (-(W.rectangle.σ) * Real.log (p : ℝ)) =
        (2 * Real.log (p : ℝ) *
          Real.exp ((cfzpModePhaseAbscissa W) * ε) *
          Real.exp (-(W.rectangle.σ) * Real.log (p : ℝ))) *
          (W.rectangle.T ^ 2 / Real.log (p : ℝ)) := by
      field_simp [ne_of_gt hlog]
    _ ≤ (2 * Real.log (p : ℝ) *
          Real.exp ((cfzpModePhaseAbscissa W) * ε) *
          Real.exp (-(W.rectangle.σ) * Real.log (p : ℝ))) *
          cfzp033ReferenceMassReducedShape ε W (Real.log (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hshape hfactor

/-- Prime-axis reference mass has a finite upper exponential comparison. -/
theorem cfzp033PrimeAxisReferenceMass_upper
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    {p : ℕ} (hp : Nat.Prime p)
    (h2ε : 2 * ε ≤ Real.log (p : ℝ))
    (hlog1 : 1 ≤ Real.log (p : ℝ)) :
    cfzp033PrimeAxisReferenceMass ε W p ≤
      128 * (W.rectangle.T + 1) ^ 2 *
        Real.exp ((cfzpModePhaseAbscissa W) * ε) *
        Real.exp (-(W.rectangle.σ) * Real.log (p : ℝ)) := by
  have hlog : 0 < Real.log (p : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
  have hshape := cfzp033ReferenceMassReducedShape_upper
    hε W hsub hlog1 h2ε
  have hfactor : 0 ≤
      2 * Real.log (p : ℝ) *
        Real.exp ((cfzpModePhaseAbscissa W) * ε) *
        Real.exp (-(W.rectangle.σ) * Real.log (p : ℝ)) := by positivity
  unfold cfzp033PrimeAxisReferenceMass
  rw [cfzp033PrimePowerReferenceMass_eq_sigma_decay hε hε2 W hp
    (by norm_num), cfzp033PrimePowerLogCoordinate_one]
  calc
    (2 * Real.log (p : ℝ) *
          Real.exp ((cfzpModePhaseAbscissa W) * ε) *
          Real.exp (-(W.rectangle.σ) * Real.log (p : ℝ))) *
          cfzp033ReferenceMassReducedShape ε W (Real.log (p : ℝ)) ≤
        (2 * Real.log (p : ℝ) *
          Real.exp ((cfzpModePhaseAbscissa W) * ε) *
          Real.exp (-(W.rectangle.σ) * Real.log (p : ℝ))) *
          (64 * (W.rectangle.T + 1) ^ 2 / Real.log (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hshape hfactor
    _ = 128 * (W.rectangle.T + 1) ^ 2 *
          Real.exp ((cfzpModePhaseAbscissa W) * ε) *
          Real.exp (-(W.rectangle.σ) * Real.log (p : ℝ)) := by
      field_simp [ne_of_gt hlog]
      ring

/-! ## Gate G: finite fixed-prime exponent-axis comparison -/

/-- One step of the fixed-prime exponential axis. -/
noncomputable def cfzp033FixedPrimeSigmaStep
    (W : PascalCenteredXiResidueTransportWindow) (p : ℕ) : ℝ :=
  Real.exp (-(W.rectangle.σ) * Real.log (p : ℝ))

/-- The fixed-prime sigma step is positive for every prime. -/
theorem cfzp033FixedPrimeSigmaStep_pos
    (W : PascalCenteredXiResidueTransportWindow) {p : ℕ}
    (_hp : Nat.Prime p) :
    0 < cfzp033FixedPrimeSigmaStep W p := by
  unfold cfzp033FixedPrimeSigmaStep
  exact Real.exp_pos _

/-- Fixed-prime exponent masses have the finite lower comparison with `1 / j`. -/
theorem cfzp033FixedPrimeReferenceMass_lower
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (h2ε : 2 * ε ≤ cfzp033PrimePowerLogCoordinate p j)
    (hu1 : 1 ≤ cfzp033PrimePowerLogCoordinate p j) :
    2 * W.rectangle.T ^ 2 * Real.exp ((cfzpModePhaseAbscissa W) * ε) /
        j * Real.exp (-(W.rectangle.σ) *
          cfzp033PrimePowerLogCoordinate p j) ≤
      cfzp031PrimePowerReferenceMass ε W p j := by
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hshape := cfzp033ReferenceMassReducedShape_lower
    hε W hsub hu1 h2ε
  have hfactor : 0 ≤
      2 * Real.log (p : ℝ) *
        Real.exp ((cfzpModePhaseAbscissa W) * ε) *
        Real.exp (-(W.rectangle.σ) *
          cfzp033PrimePowerLogCoordinate p j) := by positivity
  rw [cfzp033PrimePowerReferenceMass_eq_sigma_decay hε hε2 W hp hj]
  calc
    2 * W.rectangle.T ^ 2 * Real.exp ((cfzpModePhaseAbscissa W) * ε) /
          j * Real.exp (-(W.rectangle.σ) *
            cfzp033PrimePowerLogCoordinate p j) =
        (2 * Real.log (p : ℝ) *
          Real.exp ((cfzpModePhaseAbscissa W) * ε) *
          Real.exp (-(W.rectangle.σ) *
            cfzp033PrimePowerLogCoordinate p j)) *
          (W.rectangle.T ^ 2 /
            cfzp033PrimePowerLogCoordinate p j) := by
      unfold cfzp033PrimePowerLogCoordinate
      field_simp [ne_of_gt hlog, ne_of_gt hjr]
    _ ≤ (2 * Real.log (p : ℝ) *
          Real.exp ((cfzpModePhaseAbscissa W) * ε) *
          Real.exp (-(W.rectangle.σ) *
            cfzp033PrimePowerLogCoordinate p j)) *
          cfzp033ReferenceMassReducedShape ε W
            (cfzp033PrimePowerLogCoordinate p j) :=
      mul_le_mul_of_nonneg_left hshape hfactor

/-- Fixed-prime exponent masses have the finite upper comparison with `1 / j`. -/
theorem cfzp033FixedPrimeReferenceMass_upper
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (h2ε : 2 * ε ≤ cfzp033PrimePowerLogCoordinate p j)
    (hu1 : 1 ≤ cfzp033PrimePowerLogCoordinate p j) :
    cfzp031PrimePowerReferenceMass ε W p j ≤
      128 * (W.rectangle.T + 1) ^ 2 *
        Real.exp ((cfzpModePhaseAbscissa W) * ε) /
        j * Real.exp (-(W.rectangle.σ) *
          cfzp033PrimePowerLogCoordinate p j) := by
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hshape := cfzp033ReferenceMassReducedShape_upper
    hε W hsub hu1 h2ε
  have hfactor : 0 ≤
      2 * Real.log (p : ℝ) *
        Real.exp ((cfzpModePhaseAbscissa W) * ε) *
        Real.exp (-(W.rectangle.σ) *
          cfzp033PrimePowerLogCoordinate p j) := by positivity
  rw [cfzp033PrimePowerReferenceMass_eq_sigma_decay hε hε2 W hp hj]
  calc
    (2 * Real.log (p : ℝ) *
          Real.exp ((cfzpModePhaseAbscissa W) * ε) *
          Real.exp (-(W.rectangle.σ) *
            cfzp033PrimePowerLogCoordinate p j)) *
          cfzp033ReferenceMassReducedShape ε W
            (cfzp033PrimePowerLogCoordinate p j) ≤
        (2 * Real.log (p : ℝ) *
          Real.exp ((cfzpModePhaseAbscissa W) * ε) *
          Real.exp (-(W.rectangle.σ) *
            cfzp033PrimePowerLogCoordinate p j)) *
          (64 * (W.rectangle.T + 1) ^ 2 /
            cfzp033PrimePowerLogCoordinate p j) :=
      mul_le_mul_of_nonneg_left hshape hfactor
    _ = 128 * (W.rectangle.T + 1) ^ 2 *
          Real.exp ((cfzpModePhaseAbscissa W) * ε) /
          j * Real.exp (-(W.rectangle.σ) *
            cfzp033PrimePowerLogCoordinate p j) := by
      unfold cfzp033PrimePowerLogCoordinate
      field_simp [ne_of_gt hlog, ne_of_gt hjr]
      ring

/-! ## Firewall -/

/-- Axis accumulation and weighted coverage remain explicit gaps. -/
inductive Cfzp033ReferenceMassAxisDiagnosticsGap : Prop
  | noIndependentWeightedGoodReferenceMassCoverageProvider
  | noPrimeAxisWeightedMassAccumulationProvider
  | noPrimeAxisGoodPhaseCoverageProvider
  | noAutomaticSubcriticalWindowProvider
  | noIndependentPrimePhaseRotationIrrationalityProvider

end DkMath.RH.CFBRCProjection
