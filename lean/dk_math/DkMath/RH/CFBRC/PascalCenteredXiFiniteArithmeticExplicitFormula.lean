/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeRightEdgeTransport
import Mathlib.Tactic

/-!
# Finite arithmetic explicit-formula assembly

This module closes XDP-018.  It lifts the three-term ordinary-coordinate
decomposition to finite right-edge interval integrals, then inserts the
XDP-017 Pascal/von Mangoldt cutoff transport into the XDP-016 finite spectral
skeleton.

The archimedean term is obtained by subtraction from the already regular
combined non-prime term.  Thus no independent continuity theorem for the
derivative of `Complex.Gammaℝ` is assumed.  Every statement remains at a
fixed finite rectangle height; no horizontal decay, `T → ∞`, Mellin limit,
defect conclusion, or RH consequence is introduced.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open MeasureTheory
open scoped Interval Topology

/-! ## Gate A: named correction observables -/

/-- The weighted archimedean correction on the ordinary right edge. -/
def pascalXiArchimedeanRightEdgeIntegrand
    (h : ℂ → ℂ) (σ : ℝ) (t : ℝ) : ℂ :=
  (h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t)) *
    pascalXiArchimedeanLogDeriv
      (pascalSymmetricRectangleRightEdge σ t)) * Complex.I

/-- The finite-interval archimedean right-edge integral. -/
def pascalXiArchimedeanRightEdgeIntegral
    (h : ℂ → ℂ) (σ T : ℝ) : ℂ :=
  ∫ t in (-T)..T, pascalXiArchimedeanRightEdgeIntegrand h σ t

/-- The weighted elementary correction on the ordinary right edge. -/
def pascalXiElementaryRightEdgeIntegrand
    (h : ℂ → ℂ) (σ : ℝ) (t : ℝ) : ℂ :=
  (h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t)) *
    pascalXiElementaryLogDerivCorrection
      (pascalSymmetricRectangleRightEdge σ t)) * Complex.I

/-- The finite-interval elementary right-edge integral. -/
def pascalXiElementaryRightEdgeIntegral
    (h : ℂ → ℂ) (σ T : ℝ) : ℂ :=
  ∫ t in (-T)..T, pascalXiElementaryRightEdgeIntegrand h σ t

/-- The combined non-prime correction on the ordinary right edge. -/
def pascalXiNonPrimeRightEdgeIntegrand
    (h : ℂ → ℂ) (σ : ℝ) (t : ℝ) : ℂ :=
  pascalXiArchimedeanRightEdgeIntegrand h σ t +
    pascalXiElementaryRightEdgeIntegrand h σ t

/-- The finite-interval combined non-prime right-edge integral. -/
def pascalXiNonPrimeRightEdgeIntegral
    (h : ℂ → ℂ) (σ T : ℝ) : ℂ :=
  ∫ t in (-T)..T, pascalXiNonPrimeRightEdgeIntegrand h σ t

/-- The complete decomposed weighted right-edge integrand. -/
def pascalXiDecomposedRightEdgeIntegrand
    (h : ℂ → ℂ) (σ : ℝ) (t : ℝ) : ℂ :=
  (h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t)) *
    pascalXiDecomposedNegLogDeriv
      (pascalSymmetricRectangleRightEdge σ t)) * Complex.I

/-- The finite-interval complete decomposed right-edge integral. -/
def pascalXiDecomposedRightEdgeIntegral
    (h : ℂ → ℂ) (σ T : ℝ) : ℂ :=
  ∫ t in (-T)..T, pascalXiDecomposedRightEdgeIntegrand h σ t

/-- The decomposed right-edge integrand is the ordinary-zeta integrand plus
the combined non-prime correction. -/
theorem pascalXiDecomposedRightEdgeIntegrand_eq_zeta_add_nonPrime
    (h : ℂ → ℂ) (σ t : ℝ) :
    pascalXiDecomposedRightEdgeIntegrand h σ t =
      pascalXiOrdinaryZetaRightEdgeIntegrand h σ t +
        pascalXiNonPrimeRightEdgeIntegrand h σ t := by
  simp only [pascalXiDecomposedRightEdgeIntegrand,
    pascalXiOrdinaryZetaRightEdgeIntegrand,
    pascalXiNonPrimeRightEdgeIntegrand,
    pascalXiArchimedeanRightEdgeIntegrand,
    pascalXiElementaryRightEdgeIntegrand,
    pascalXiDecomposedNegLogDeriv]
  ring

/-- The combined non-prime integrand is the archimedean term plus the
elementary term. -/
theorem pascalXiNonPrimeRightEdgeIntegrand_eq_archimedean_add_elementary
    (h : ℂ → ℂ) (σ t : ℝ) :
    pascalXiNonPrimeRightEdgeIntegrand h σ t =
      pascalXiArchimedeanRightEdgeIntegrand h σ t +
        pascalXiElementaryRightEdgeIntegrand h σ t := by
  rfl

/-! ## Gate B: fixed-Xi regularity transported to the right edge -/

/-- The coordinate-safe fixed-Xi weighted negative-log derivative is
interval-integrable on every edge of a finite residue window.

The proof combines the XDP-016 raw regularizer and finite principal-part sum,
then uses their pointwise decomposition.  It deliberately does not start by
proving separate Gamma-term continuity.
-/
theorem pascalCenteredXiRectangleBoundaryIntegrable_weightedNegLogDeriv
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalSymmetricRectangleBoundaryIntegrable
      (fun s => pascalCenteredXiWeightedNegLogDeriv h
        (pascalOrdinaryToCentered s))
      W.rectangle.σ W.rectangle.T := by
  have hraw := pascalCenteredXiRectangleBoundaryIntegrable_diskWeightedRawRegularizer
    hh W
  have hprincipal := pascalCenteredXiRectangleBoundaryIntegrable_diskWeightedPrincipalPartSum
    h W
  have hadd := pascalSymmetricRectangleBoundaryIntegrable_add
    (fun s => pascalCenteredXiDiskWeightedRawRegularizer h W.R
      (pascalOrdinaryToCentered s))
    (fun s => pascalCenteredXiDiskWeightedPrincipalPartSum h W.R
      (pascalOrdinaryToCentered s)) hraw hprincipal
  have hdecomp :
      (fun s => pascalCenteredXiWeightedNegLogDeriv h
        (pascalOrdinaryToCentered s)) =
      (fun s => pascalCenteredXiDiskWeightedRawRegularizer h W.R
        (pascalOrdinaryToCentered s) +
        pascalCenteredXiDiskWeightedPrincipalPartSum h W.R
          (pascalOrdinaryToCentered s)) := by
    funext s
    exact pascalCenteredXiWeightedNegLogDeriv_comp_toCentered_eq_raw_add_principalPartSum
      h W s
  rw [hdecomp]
  exact hadd

/-- The complete decomposed weighted right-edge integrand is interval-
integrable.  It is obtained from the fixed-Xi right-edge integrability and
the automatic right-edge factor decomposition for `1 < σ`.
-/
theorem intervalIntegrable_pascalXiDecomposedRightEdgeIntegrand
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    IntervalIntegrable
      (pascalXiDecomposedRightEdgeIntegrand h W.rectangle.σ)
      volume (-W.rectangle.T) W.rectangle.T := by
  have hboundary := pascalCenteredXiRectangleBoundaryIntegrable_weightedNegLogDeriv
    hh W
  apply hboundary.1.congr
  intro t ht
  change (h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
      pascalCenteredXiNegLogDeriv
        (pascalOrdinaryToCentered
          (pascalSymmetricRectangleRightEdge W.rectangle.σ t))) * Complex.I = _
  rw [pascalCenteredXiNegLogDeriv_rightEdge_eq_decomposed W.rectangle.hσ]
  rfl

/-! ## Gate C: ordinary-zeta limit integrability -/

/-- The ordinary-zeta right-edge limit integrand is interval-integrable on
the finite residue window. -/
theorem intervalIntegrable_pascalXiOrdinaryZetaRightEdgeIntegrand_of_residueWindow
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    IntervalIntegrable
      (pascalXiOrdinaryZetaRightEdgeIntegrand h W.rectangle.σ)
      volume (-W.rectangle.T) W.rectangle.T :=
  DkMath.RH.CFBRCProjection.intervalIntegrable_pascalXiOrdinaryZetaRightEdgeIntegrand
    hh W.rectangle.hσ

/-! ## Gate D: non-prime subtraction and integral split -/

/-- The combined non-prime right-edge integrand is integrable by subtraction
of the ordinary-zeta limit from the complete decomposed integrand.
-/
theorem intervalIntegrable_pascalXiNonPrimeRightEdgeIntegrand
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    IntervalIntegrable
      (pascalXiNonPrimeRightEdgeIntegrand h W.rectangle.σ)
      volume (-W.rectangle.T) W.rectangle.T := by
  have hdec := intervalIntegrable_pascalXiDecomposedRightEdgeIntegrand hh W
  have hzeta := intervalIntegrable_pascalXiOrdinaryZetaRightEdgeIntegrand
    hh (σ := W.rectangle.σ) (T := W.rectangle.T) W.rectangle.hσ
  have hsub := hdec.sub hzeta
  have heq : (fun t : ℝ =>
      pascalXiDecomposedRightEdgeIntegrand h W.rectangle.σ t -
        pascalXiOrdinaryZetaRightEdgeIntegrand h W.rectangle.σ t) =
      (fun t : ℝ => pascalXiNonPrimeRightEdgeIntegrand h W.rectangle.σ t) := by
    funext t
    rw [pascalXiDecomposedRightEdgeIntegrand_eq_zeta_add_nonPrime]
    ring
  apply hsub.congr
  intro t ht
  exact congrFun heq t

/-- The complete decomposed right-edge integral splits into zeta and combined
non-prime terms. -/
theorem pascalXiDecomposedRightEdgeIntegral_eq_zeta_add_nonPrime
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalXiDecomposedRightEdgeIntegral h W.rectangle.σ W.rectangle.T =
      pascalXiOrdinaryZetaRightEdgeIntegral h W.rectangle.σ W.rectangle.T +
        pascalXiNonPrimeRightEdgeIntegral h W.rectangle.σ W.rectangle.T := by
  have hdec := intervalIntegrable_pascalXiDecomposedRightEdgeIntegrand hh W
  have hzeta := intervalIntegrable_pascalXiOrdinaryZetaRightEdgeIntegrand
    hh (σ := W.rectangle.σ) (T := W.rectangle.T) W.rectangle.hσ
  have hnp := intervalIntegrable_pascalXiNonPrimeRightEdgeIntegrand hh W
  unfold pascalXiDecomposedRightEdgeIntegral
    pascalXiOrdinaryZetaRightEdgeIntegral pascalXiNonPrimeRightEdgeIntegral
  have heq : (fun t : ℝ => pascalXiDecomposedRightEdgeIntegrand h W.rectangle.σ t) =
      (fun t => pascalXiOrdinaryZetaRightEdgeIntegrand h W.rectangle.σ t +
        pascalXiNonPrimeRightEdgeIntegrand h W.rectangle.σ t) := by
    funext t
    exact pascalXiDecomposedRightEdgeIntegrand_eq_zeta_add_nonPrime h _ _
  rw [heq, intervalIntegral.integral_add hzeta hnp]

/-! ## Gate E: direct elementary integrability -/

private theorem continuous_pascalXiRightEdgePath (σ : ℝ) :
    Continuous (fun t : ℝ => pascalSymmetricRectangleRightEdge σ t) := by
  change Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I)
  fun_prop

private theorem continuous_pascalCenteredRightEdgeWeight
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) (σ : ℝ) :
    Continuous (fun t : ℝ => h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t))) := by
  apply hh.continuous.comp
  change Continuous (fun t : ℝ =>
    pascalSymmetricRectangleRightEdge σ t - criticalLineCenter)
  convert (continuous_pascalXiRightEdgePath σ).sub continuous_const using 1
  all_goals (ext t; rfl)

/-- The elementary correction is continuous, and hence interval-integrable,
on every safe right edge.  The two denominators are protected by the
right-edge factor theorem.
-/
theorem intervalIntegrable_pascalXiElementaryRightEdgeIntegrand
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    IntervalIntegrable
      (pascalXiElementaryRightEdgeIntegrand h W.rectangle.σ)
      volume (-W.rectangle.T) W.rectangle.T := by
  let s : ℝ → ℂ := fun t => pascalSymmetricRectangleRightEdge W.rectangle.σ t
  have hs : Continuous s := by
    dsimp [s]
    exact continuous_pascalXiRightEdgePath W.rectangle.σ
  have hw : Continuous (fun t => h (pascalOrdinaryToCentered (s t))) := by
    dsimp [s]
    exact continuous_pascalCenteredRightEdgeWeight hh W.rectangle.σ
  have hs0 : ∀ t : ℝ, s t ≠ 0 := by
    intro t
    exact (rightEdge_factor_nonzero_of_one_lt W.rectangle.hσ).1
  have hs1 : ∀ t : ℝ, s t ≠ 1 := by
    intro t
    exact (rightEdge_factor_nonzero_of_one_lt W.rectangle.hσ).2.1
  have hcorr : Continuous (fun t : ℝ =>
      pascalXiElementaryLogDerivCorrection (s t)) := by
    unfold pascalXiElementaryLogDerivCorrection
    have hone : Continuous (fun _ : ℝ => (1 : ℂ)) := continuous_const
    have hminus : Continuous (fun _ : ℝ => (-1 : ℂ)) := continuous_const
    have h1s : ∀ t : ℝ, (1 : ℂ) - s t ≠ 0 := fun t =>
      sub_ne_zero.mpr (hs1 t).symm
    convert hminus.div hs hs0 |>.add
        (hone.div (hone.sub hs) h1s) using 1
    funext t
    rfl
  have htotal : Continuous (fun t : ℝ =>
      pascalXiElementaryRightEdgeIntegrand h W.rectangle.σ t) := by
    dsimp [pascalXiElementaryRightEdgeIntegrand, s]
    exact (hw.mul hcorr).mul continuous_const
  exact htotal.intervalIntegrable _ _

/-! ## Gate F: archimedean subtraction and three-term split -/

/-- The archimedean right-edge integrand is obtained by subtracting the
elementary correction from the combined non-prime term.
-/
theorem intervalIntegrable_pascalXiArchimedeanRightEdgeIntegrand
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    IntervalIntegrable
      (pascalXiArchimedeanRightEdgeIntegrand h W.rectangle.σ)
      volume (-W.rectangle.T) W.rectangle.T := by
  have hnp := intervalIntegrable_pascalXiNonPrimeRightEdgeIntegrand hh W
  have helem := intervalIntegrable_pascalXiElementaryRightEdgeIntegrand hh W
  have hsub := hnp.sub helem
  have heq : (fun t : ℝ =>
      pascalXiNonPrimeRightEdgeIntegrand h W.rectangle.σ t -
        pascalXiElementaryRightEdgeIntegrand h W.rectangle.σ t) =
      (fun t : ℝ => pascalXiArchimedeanRightEdgeIntegrand h W.rectangle.σ t) := by
    funext t
    rw [pascalXiNonPrimeRightEdgeIntegrand_eq_archimedean_add_elementary]
    ring
  apply hsub.congr
  intro t ht
  exact congrFun heq t

/-- The combined non-prime integral splits into archimedean and elementary
integrals. -/
theorem pascalXiNonPrimeRightEdgeIntegral_eq_archimedean_add_elementary
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalXiNonPrimeRightEdgeIntegral h W.rectangle.σ W.rectangle.T =
      pascalXiArchimedeanRightEdgeIntegral h W.rectangle.σ W.rectangle.T +
        pascalXiElementaryRightEdgeIntegral h W.rectangle.σ W.rectangle.T := by
  have hnp := intervalIntegrable_pascalXiNonPrimeRightEdgeIntegrand hh W
  have ha := intervalIntegrable_pascalXiArchimedeanRightEdgeIntegrand hh W
  have he := intervalIntegrable_pascalXiElementaryRightEdgeIntegrand hh W
  unfold pascalXiNonPrimeRightEdgeIntegral
    pascalXiArchimedeanRightEdgeIntegral pascalXiElementaryRightEdgeIntegral
  have heq : (fun t : ℝ => pascalXiNonPrimeRightEdgeIntegrand h W.rectangle.σ t) =
      (fun t => pascalXiArchimedeanRightEdgeIntegrand h W.rectangle.σ t +
        pascalXiElementaryRightEdgeIntegrand h W.rectangle.σ t) := by
    funext t
    exact pascalXiNonPrimeRightEdgeIntegrand_eq_archimedean_add_elementary h _ _
  rw [heq, intervalIntegral.integral_add ha he]

/-! ## Gate G: finite four-term spectral identity -/

/-- The finite fixed-window spectral endpoint splits into ordinary-zeta,
archimedean, elementary, and top-horizontal contributions.  The top term is
retained exactly; no height limit is taken.
-/
theorem pascalCenteredXiFiniteExplicitFormula_eq_zeta_archimedean_elementary_top
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (heven : PascalCenteredEvenWeight h)
    (W : PascalCenteredXiResidueTransportWindow) :
    -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment h W.R =
      2 * pascalXiOrdinaryZetaRightEdgeIntegral h
          W.rectangle.σ W.rectangle.T +
      2 * pascalXiArchimedeanRightEdgeIntegral h
          W.rectangle.σ W.rectangle.T +
      2 * pascalXiElementaryRightEdgeIntegral h
          W.rectangle.σ W.rectangle.T +
      2 * pascalCenteredXiTopHorizontalContribution h
          W.toContourTransportWindow := by
  have hskeleton := pascalCenteredXiFiniteExplicitFormulaSkeleton hh heven W
  have hsplit := pascalXiDecomposedRightEdgeIntegral_eq_zeta_add_nonPrime hh W
  have hsplit' := pascalXiNonPrimeRightEdgeIntegral_eq_archimedean_add_elementary hh W
  change -(2 * Real.pi * Complex.I) *
      pascalCenteredXiZeroDiskWeightedMoment h W.R =
    2 * pascalXiDecomposedRightEdgeIntegral h
      W.rectangle.σ W.rectangle.T +
      2 * pascalCenteredXiTopHorizontalContribution h
        W.toContourTransportWindow at hskeleton
  rw [hsplit, hsplit'] at hskeleton
  convert hskeleton using 1
  ring

/-! ## Gate H: arithmetic approximant and its convergence -/

/-- The finite arithmetic approximant attached to a residue window. -/
def pascalCenteredXiFiniteArithmeticApproximant
    (h : ℂ → ℂ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℂ :=
  2 * pascalPrimePowerRightEdgeCutoffIntegral h
      W.rectangle.σ W.rectangle.T X +
    2 * pascalXiArchimedeanRightEdgeIntegral h
      W.rectangle.σ W.rectangle.T +
    2 * pascalXiElementaryRightEdgeIntegral h
      W.rectangle.σ W.rectangle.T +
    2 * pascalCenteredXiTopHorizontalContribution h
      W.toContourTransportWindow

/-- Finite Pascal/von Mangoldt arithmetic approximants converge to the finite
Xi weighted zero-moment endpoint.  The theorem is for each fixed finite
residue window and does not exchange the cutoff limit with a height limit.
-/
theorem tendsto_pascalCenteredXiFiniteArithmeticExplicitFormula
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (heven : PascalCenteredEvenWeight h)
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto (fun X => pascalCenteredXiFiniteArithmeticApproximant h W X)
      atTop
      (nhds (-(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment h W.R)) := by
  have hcut := tendsto_pascalPrimePowerRightEdgeCutoffIntegral_of_residueTransportWindow
    hh W
  have h2cut : Tendsto (fun X =>
      2 * pascalPrimePowerRightEdgeCutoffIntegral h
        W.rectangle.σ W.rectangle.T X) atTop
      (nhds (2 * pascalXiOrdinaryZetaRightEdgeIntegral h
        W.rectangle.σ W.rectangle.T)) := by
    exact tendsto_const_nhds.mul hcut
  have hconstA : Tendsto (fun _ : ℕ =>
      2 * pascalXiArchimedeanRightEdgeIntegral h
        W.rectangle.σ W.rectangle.T) atTop
      (nhds (2 * pascalXiArchimedeanRightEdgeIntegral h
        W.rectangle.σ W.rectangle.T)) := tendsto_const_nhds
  have hconstE : Tendsto (fun _ : ℕ =>
      2 * pascalXiElementaryRightEdgeIntegral h
        W.rectangle.σ W.rectangle.T) atTop
      (nhds (2 * pascalXiElementaryRightEdgeIntegral h
        W.rectangle.σ W.rectangle.T)) := tendsto_const_nhds
  have hconstT : Tendsto (fun _ : ℕ =>
      2 * pascalCenteredXiTopHorizontalContribution h
        W.toContourTransportWindow) atTop
      (nhds (2 * pascalCenteredXiTopHorizontalContribution h
        W.toContourTransportWindow)) := tendsto_const_nhds
  have hall := ((h2cut.add hconstA).add hconstE).add hconstT
  have hfour := pascalCenteredXiFiniteExplicitFormula_eq_zeta_archimedean_elementary_top
    hh heven W
  have heq :
      2 * pascalXiOrdinaryZetaRightEdgeIntegral h W.rectangle.σ W.rectangle.T +
          2 * pascalXiArchimedeanRightEdgeIntegral h W.rectangle.σ W.rectangle.T +
        2 * pascalXiElementaryRightEdgeIntegral h W.rectangle.σ W.rectangle.T +
      2 * pascalCenteredXiTopHorizontalContribution h W.toContourTransportWindow =
      -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment h W.R := by
    exact hfour.symm
  rw [heq] at hall
  simpa [pascalCenteredXiFiniteArithmeticApproximant] using hall

/-! ## Gate I: explicit finite von Mangoldt surface -/

/-- The finite arithmetic approximant expands into a finite von Mangoldt
weighted kernel sum plus the two fixed correction terms and the finite top
horizontal term. -/
theorem pascalCenteredXiFiniteArithmeticApproximant_eq_vonMangoldt_sum
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiFiniteArithmeticApproximant h W X =
      2 * (∑ n ∈ Finset.range (X + 1),
        ∫ t in (-W.rectangle.T)..W.rectangle.T,
          (h (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            ((ArithmeticFunction.vonMangoldt n : ℂ) *
              ((n : ℂ) ^
                (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t)))) *
            Complex.I)) +
      2 * pascalXiArchimedeanRightEdgeIntegral h
        W.rectangle.σ W.rectangle.T +
      2 * pascalXiElementaryRightEdgeIntegral h
        W.rectangle.σ W.rectangle.T +
      2 * pascalCenteredXiTopHorizontalContribution h
        W.toContourTransportWindow := by
  unfold pascalCenteredXiFiniteArithmeticApproximant
  rw [pascalPrimePowerRightEdgeCutoffIntegral_eq_vonMangoldt_sum hh]

end DkMath.RH.CFBRCProjection
