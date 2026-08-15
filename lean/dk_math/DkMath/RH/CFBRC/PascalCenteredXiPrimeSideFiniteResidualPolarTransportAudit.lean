/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteResidualPhaseAmplitudeChannelAudit
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-!
# CS32: branch-free finite residual polar transport

The residual is transported on the safe finite top edge through two carriers:
`Complex.normSq F` for amplitude and `F / conj F` for phase.  This module
uses neither `Complex.arg` nor a logarithm branch.  It records exact finite
ODEs and the real logarithmic norm-square bridge; it does not provide a sign
estimate or an RH conclusion.
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

/-! ## CS32-A: the finite residual top path -/

noncomputable def pascalCenteredXiPrimeSideFiniteResidualTopPath
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X
    (pascalSymmetricRectangleTopEdge u W.rectangle.T)

theorem pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_hasDerivAt
    (X : ℕ) {s : ℂ} (hs1 : s ≠ 1) :
    HasDerivAt
      (fun z : ℂ => pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X z)
      (deriv riemannZeta s *
          pascalCenteredXiPrimeSideFiniteEulerCompensator X s +
        riemannZeta s *
          (pascalPrimePowerPHZFiniteUpTo X s *
            pascalCenteredXiPrimeSideFiniteEulerCompensator X s)) s := by
  have hz : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs1).hasDerivAt
  have hc := pascalCenteredXiPrimeSideFiniteEulerCompensator_hasDerivAt X s
  change HasDerivAt (fun z : ℂ =>
    riemannZeta z * pascalCenteredXiPrimeSideFiniteEulerCompensator X z) _ s
  exact hz.mul hc

theorem pascalCenteredXiPrimeSideFiniteResidualTopPath_ne_zero
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteResidualTopPath X W u ≠ 0 := by
  exact pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_ne_zero_on_safe_top
    hSafe hu

theorem pascalCenteredXiPrimeSideFiniteResidualTopPath_hasDerivAt
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    HasDerivAt
      (pascalCenteredXiPrimeSideFiniteResidualTopPath X W)
      (-pascalCenteredXiPrimeSideFiniteResidualLogRate X W u *
        pascalCenteredXiPrimeSideFiniteResidualTopPath X W u) u := by
  dsimp [pascalCenteredXiPrimeSideFiniteResidualTopPath,
    pascalCenteredXiPrimeSideFiniteResidualLogRate]
  dsimp [IsPascalCenteredXiTopLogDerivDecompositionSafe] at hSafe
  have hs := hSafe u hu
  have hR := pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_hasDerivAt
    X hs.2.1
  have hpath : HasDerivAt (fun v : ℝ =>
      pascalSymmetricRectangleTopEdge v W.rectangle.T) (1 : ℂ) u := by
    change HasDerivAt (fun v : ℝ =>
      (v : ℂ) + (W.rectangle.T : ℂ) * Complex.I) 1 u
    simpa using (((hasDerivAt_id (u : ℂ)).comp_ofReal).add_const
      ((W.rectangle.T : ℂ) * Complex.I))
  have hcomp := hR.comp u hpath
  have hrel :
      deriv (fun z : ℂ =>
        pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X z)
        (pascalSymmetricRectangleTopEdge u W.rectangle.T) =
        -pascalCenteredXiPrimeSideFiniteResidualLogRate X W u *
          pascalCenteredXiPrimeSideFiniteResidualTopPath X W u := by
    simp only [pascalCenteredXiPrimeSideFiniteResidualLogRate,
      pascalCenteredXiPrimeSideFiniteResidualTopPath]
    rw [logDeriv_apply]
    have hne := pascalCenteredXiPrimeSideFiniteResidualTopPath_ne_zero
      (X := X) hSafe hu
    have hneR : pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X
        (pascalSymmetricRectangleTopEdge u W.rectangle.T) ≠ 0 := by
      simpa [pascalCenteredXiPrimeSideFiniteResidualTopPath] using hne
    field_simp [hne]
  rw [← hR.deriv] at hcomp
  change HasDerivAt (fun v : ℝ =>
    pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X
      (pascalSymmetricRectangleTopEdge v W.rectangle.T)) _ u
  change HasDerivAt (fun v : ℝ =>
    pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X
      (pascalSymmetricRectangleTopEdge v W.rectangle.T)) _ u at hcomp
  convert hcomp using 1
  · rw [hrel]
    simp [pascalCenteredXiPrimeSideFiniteResidualLogRate,
      pascalCenteredXiPrimeSideFiniteResidualTopPath]

/-! ## CS32-B/C: norm-square amplitude carrier -/

noncomputable def pascalCenteredXiPrimeSideFiniteResidualNormSq
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℝ :=
  Complex.normSq (pascalCenteredXiPrimeSideFiniteResidualTopPath X W u)

theorem pascalCenteredXiPrimeSideFiniteResidualNormSq_pos
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    0 < pascalCenteredXiPrimeSideFiniteResidualNormSq X W u := by
  unfold pascalCenteredXiPrimeSideFiniteResidualNormSq
  exact Complex.normSq_pos.mpr
    (pascalCenteredXiPrimeSideFiniteResidualTopPath_ne_zero hSafe hu)

theorem pascalCenteredXiPrimeSideFiniteResidualNormSq_hasDerivAt
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    HasDerivAt
      (pascalCenteredXiPrimeSideFiniteResidualNormSq X W)
      (-2 * pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W u *
        pascalCenteredXiPrimeSideFiniteResidualNormSq X W u) u := by
  have hF := pascalCenteredXiPrimeSideFiniteResidualTopPath_hasDerivAt
    (X := X) hSafe hu
  have hn := hF.norm_sq
  unfold pascalCenteredXiPrimeSideFiniteResidualNormSq
  convert hn using 1
  · simp only [Complex.normSq_eq_norm_sq]
  · unfold pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate
    simp [Complex.inner, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring

theorem pascalCenteredXiPrimeSideFiniteResidualAmplitudeRate_eq_neg_half_normSq_deriv_div
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W u =
      -(1 / 2 : ℝ) *
        deriv (pascalCenteredXiPrimeSideFiniteResidualNormSq X W) u /
          pascalCenteredXiPrimeSideFiniteResidualNormSq X W u := by
  have hder := pascalCenteredXiPrimeSideFiniteResidualNormSq_hasDerivAt
    (X := X) hSafe hu
  have hpos := pascalCenteredXiPrimeSideFiniteResidualNormSq_pos
    (X := X) hSafe hu
  rw [hder.deriv]
  field_simp [ne_of_gt hpos]

theorem pascalCenteredXiPrimeSideFiniteResidualAmplitudeRate_eq_neg_half_log_normSq_deriv
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    deriv (fun v : ℝ =>
      Real.log (pascalCenteredXiPrimeSideFiniteResidualNormSq X W v)) u =
      -2 * pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W u := by
  have hpos := pascalCenteredXiPrimeSideFiniteResidualNormSq_pos
    (X := X) hSafe hu
  have hnorm := pascalCenteredXiPrimeSideFiniteResidualNormSq_hasDerivAt
    (X := X) hSafe hu
  have hlog := (Real.hasDerivAt_log hpos.ne').comp u hnorm
  change deriv (Real.log ∘ pascalCenteredXiPrimeSideFiniteResidualNormSq X W) u = _
  rw [hlog.deriv]
  field_simp [ne_of_gt hpos]

theorem pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement_eq_log_normSq_endpoint
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ}
    (hAmplitude : IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W)
      volume W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement X W
        (1 - W.rectangle.σ) =
      (Real.log (pascalCenteredXiPrimeSideFiniteResidualNormSq X W
          W.rectangle.σ) -
        Real.log (pascalCenteredXiPrimeSideFiniteResidualNormSq X W
          (1 - W.rectangle.σ))) / 2 := by
  have hlogderiv : ∀ v ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ),
      HasDerivAt
        (fun x : ℝ =>
          Real.log (pascalCenteredXiPrimeSideFiniteResidualNormSq X W x))
        (-2 * pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W v) v := by
    intro v hv
    have hpos := pascalCenteredXiPrimeSideFiniteResidualNormSq_pos
      (X := X) hSafe hv
    have hnorm := pascalCenteredXiPrimeSideFiniteResidualNormSq_hasDerivAt
      (X := X) hSafe hv
    have hlog := (Real.hasDerivAt_log hpos.ne').comp v hnorm
    change HasDerivAt
      (Real.log ∘ pascalCenteredXiPrimeSideFiniteResidualNormSq X W) _ v at hlog
    apply hlog.congr_deriv
    field_simp [ne_of_gt hpos]
  have hcont : ContinuousOn
      (fun v : ℝ =>
        Real.log (pascalCenteredXiPrimeSideFiniteResidualNormSq X W v))
      (Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) := by
    intro v hv
    exact (hlogderiv v hv).continuousAt.continuousWithinAt
  have hfund := intervalIntegral.integral_eq_sub_of_hasDeriv_right
    hcont
    (fun v hv => (hlogderiv v (mem_Icc_of_Ioo hv)).hasDerivWithinAt)
    (hAmplitude.const_mul (-2 : ℝ))
  have hfund' :
      (∫ v in W.rectangle.σ..(1 - W.rectangle.σ),
          (-2 : ℝ) * pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate
            X W v) =
        Real.log (pascalCenteredXiPrimeSideFiniteResidualNormSq X W
          (1 - W.rectangle.σ)) -
          Real.log (pascalCenteredXiPrimeSideFiniteResidualNormSq X W
            W.rectangle.σ) := by
    simpa using hfund
  unfold pascalCenteredXiPrimeSideFiniteResidualAmplitudeDisplacement
  calc
    (∫ v in W.rectangle.σ..(1 - W.rectangle.σ),
        pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W v) =
      (-1 / 2 : ℝ) *
        (∫ v in W.rectangle.σ..(1 - W.rectangle.σ),
          (-2 : ℝ) * pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate
            X W v) := by
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = (Real.log (pascalCenteredXiPrimeSideFiniteResidualNormSq X W
          W.rectangle.σ) -
        Real.log (pascalCenteredXiPrimeSideFiniteResidualNormSq X W
          (1 - W.rectangle.σ))) / 2 := by
      rw [hfund']
      ring

/-! ## CS32-D/F: the branch-free phase carrier -/

noncomputable def pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℂ :=
  (pascalCenteredXiPrimeSideFiniteResidualTopPath X W /
    (fun v => star (pascalCenteredXiPrimeSideFiniteResidualTopPath X W v))) u

theorem pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier_normSq
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    Complex.normSq (pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier X W u) = 1 := by
  unfold pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier
  change Complex.normSq
    (pascalCenteredXiPrimeSideFiniteResidualTopPath X W u /
      star (pascalCenteredXiPrimeSideFiniteResidualTopPath X W u)) = 1
  rw [Complex.normSq_div]
  simp [
    pascalCenteredXiPrimeSideFiniteResidualTopPath_ne_zero (X := X) hSafe hu]

theorem pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier_hasDerivAt
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    HasDerivAt
      (pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier X W)
      (-2 * Complex.I *
          (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W u) *
        pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier X W u) u := by
  have hF := pascalCenteredXiPrimeSideFiniteResidualTopPath_hasDerivAt
    (X := X) hSafe hu
  have hFne := pascalCenteredXiPrimeSideFiniteResidualTopPath_ne_zero
    (X := X) hSafe hu
  have hcarrier := hF.div hF.star (star_ne_zero.mpr hFne)
  change HasDerivAt
    (pascalCenteredXiPrimeSideFiniteResidualTopPath X W /
      (fun v => star (pascalCenteredXiPrimeSideFiniteResidualTopPath X W v))) _ u
  apply hcarrier.congr_deriv
  simp only [pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate,
    pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier,
    pascalCenteredXiPrimeSideFiniteResidualLogRate,
    pascalCenteredXiPrimeSideFiniteResidualTopPath]
  let q : ℂ := pascalCenteredXiPrimeSideFiniteResidualLogRate X W u
  let f : ℂ := pascalCenteredXiPrimeSideFiniteResidualTopPath X W u
  change ((-q * f) * star f - f * star (-q * f)) / (star f) ^ 2 =
    -2 * Complex.I * (q.im : ℂ) * (f / star f)
  have hf : f ≠ 0 := by
    simpa [f] using hFne
  have hqconj : star q = (q.re : ℂ) - (q.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [q, Complex.mul_re, Complex.mul_im]
  have hq : q = (q.re : ℂ) + (q.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [star_mul, star_neg, hqconj]
  field_simp [star_ne_zero.mpr hf]
  have hdiff : -q - -((q.re : ℂ) - (q.im : ℂ) * Complex.I) =
      -((q.im : ℂ) * Complex.I * 2) := by
    calc
      -q - -((q.re : ℂ) - (q.im : ℂ) * Complex.I) =
          -((q.re : ℂ) + (q.im : ℂ) * Complex.I) -
            -((q.re : ℂ) - (q.im : ℂ) * Complex.I) := by
        have hneg := congrArg Neg.neg hq
        rw [hneg]
      _ = -((q.im : ℂ) * Complex.I * 2) := by ring
  rw [hdiff]
  ring

/-! A small bonus consequence: the phase carrier is an exact unit-circle
    element in the algebraic sense, without choosing an argument. -/

theorem pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier_mul_star_eq_one
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier X W u *
        star (pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier X W u) = 1 := by
  have hF := pascalCenteredXiPrimeSideFiniteResidualTopPath_ne_zero
    (X := X) hSafe hu
  unfold pascalCenteredXiPrimeSideFiniteResidualPhaseCarrier
  change
    (pascalCenteredXiPrimeSideFiniteResidualTopPath X W u /
        star (pascalCenteredXiPrimeSideFiniteResidualTopPath X W u)) *
      star (pascalCenteredXiPrimeSideFiniteResidualTopPath X W u /
        star (pascalCenteredXiPrimeSideFiniteResidualTopPath X W u)) = 1
  rw [star_div₀]
  field_simp [hF, star_ne_zero.mpr hF]
  simp

/-! ## CS32-G: the remaining semantic frontier -/

inductive PascalCenteredXiPrimeSideFiniteResidualPolarTransportGap : Prop
  | no_independent_phase_endpoint_transport_or_reach_estimate

end DkMath.RH.CFBRCProjection
