/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideInteractionPhaseBoundaryAudit
import Mathlib.Tactic

/-!
# CS27: holomorphic phase potential / boundary companion audit

The finite oscillatory arithmetic source is lifted to a holomorphic
potential.  This module keeps the right-vertical endpoint identity separate
from the repository's fixed-Xi top-horizontal correction.  All sums and
path identities here are finite; no prime-series continuation, sign
provider, or RH conclusion is asserted.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open Filter
open MeasureTheory
open scoped Interval Topology

/-! ## CS27-A: the complex phase potential -/

noncomputable def pascalCenteredXiPrimeSideComplexPhasePotential
    (r : ℝ) (z : ℂ) : ℂ :=
  if r = 0 then z ^ 2 / 2 else
    Complex.exp ((r : ℂ) * z) * (((r : ℂ) * z) - 1) /
      ((r : ℂ) ^ 2)

private theorem cs27_phase_potential_nonzero_hasDerivAt
    {r : ℝ} (hr : r ≠ 0) (z : ℂ) :
    HasDerivAt
      (fun w : ℂ => Complex.exp ((r : ℂ) * w) *
        (((r : ℂ) * w) - 1) / ((r : ℂ) ^ 2))
      (z * Complex.exp ((r : ℂ) * z)) z := by
  have harg : HasDerivAt (fun w : ℂ => (r : ℂ) * w) (r : ℂ) z := by
    simpa [mul_comm] using (hasDerivAt_id' z).const_mul (r : ℂ)
  have hexp : HasDerivAt
      (fun w : ℂ => Complex.exp ((r : ℂ) * w))
      (Complex.exp ((r : ℂ) * z) * (r : ℂ)) z := by
    exact (Complex.hasDerivAt_exp ((r : ℂ) * z)).comp z harg
  have hlin : HasDerivAt
      (fun w : ℂ => (r : ℂ) * w - 1) (r : ℂ) z := by
    convert! harg.sub (hasDerivAt_const z (1 : ℂ)) using 1; simp
  have hprod := hexp.mul hlin
  have hdiv := hprod.div_const ((r : ℂ) ^ 2)
  have hrC : (r : ℂ) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (by exact_mod_cast hr)
  have hrC0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  convert! hdiv using 1; field_simp [hrC, hrC0]; simp

private theorem cs27_phase_potential_zero_hasDerivAt
    (z : ℂ) :
    HasDerivAt (fun w : ℂ => w ^ 2 / 2) z z := by
  have hpow := (hasDerivAt_id' z).pow 2
  have hdiv := hpow.div_const (2 : ℂ)
  simpa [pow_two] using hdiv

theorem pascalCenteredXiPrimeSideComplexPhasePotential_hasDerivAt
    (r : ℝ) (z : ℂ) :
    HasDerivAt
      (pascalCenteredXiPrimeSideComplexPhasePotential r)
      (z * Complex.exp ((r : ℂ) * z)) z := by
  by_cases hr : r = 0
  · subst r
    have hfun : pascalCenteredXiPrimeSideComplexPhasePotential 0 =
        (fun w : ℂ => w ^ 2 / 2) := by
      funext w
      simp [pascalCenteredXiPrimeSideComplexPhasePotential]
    rw [hfun]
    simpa using cs27_phase_potential_zero_hasDerivAt z
  · have hfun : pascalCenteredXiPrimeSideComplexPhasePotential r =
        (fun w : ℂ => Complex.exp ((r : ℂ) * w) *
          (((r : ℂ) * w) - 1) / ((r : ℂ) ^ 2)) := by
      funext w
      simp [pascalCenteredXiPrimeSideComplexPhasePotential, hr]
    rw [hfun]
    exact cs27_phase_potential_nonzero_hasDerivAt hr z

theorem pascalCenteredXiPrimeSideComplexPhasePotential_ofReal_im
    (r a : ℝ) :
    (pascalCenteredXiPrimeSideComplexPhasePotential r (a : ℂ)).im = 0 := by
  by_cases hr : r = 0
  · simp [pascalCenteredXiPrimeSideComplexPhasePotential, hr, Complex.mul_im, pow_two]
  · rw [pascalCenteredXiPrimeSideComplexPhasePotential, if_neg hr]
    rw [show ((r : ℂ) ^ 2) = (r ^ 2 : ℝ) by norm_num]
    rw [Complex.div_ofReal_im]
    simp [Complex.mul_im, Complex.exp_re, Complex.exp_im]

private theorem cs27_phase_potential_vertical_im_nonzero
    {a r T : ℝ} (hr : r ≠ 0) :
    (pascalCenteredXiPrimeSideComplexPhasePotential r
        ((a : ℂ) + (T : ℂ) * Complex.I)).im =
      Real.exp (a * r) *
        (T * Real.cos (r * T) / r +
          (a * r - 1) * Real.sin (r * T) / r ^ 2) := by
  unfold pascalCenteredXiPrimeSideComplexPhasePotential
  simp only [if_neg hr]
  rw [show ((r : ℂ) ^ 2) = (r ^ 2 : ℝ) by norm_num]
  rw [Complex.div_ofReal_im]
  simp [Complex.mul_im, Complex.exp_re, Complex.exp_im]
  field_simp [hr]

private theorem cs27_phase_potential_vertical_im_zero
    (a T : ℝ) :
    (pascalCenteredXiPrimeSideComplexPhasePotential 0
        ((a : ℂ) + (T : ℂ) * Complex.I)).im = a * T := by
  simp [pascalCenteredXiPrimeSideComplexPhasePotential, Complex.mul_re, Complex.mul_im, pow_two]
  ring

theorem pascalCenteredXiPrimeSidePhasePrimitive_eq_im_potential_jump
    (a r T : ℝ) :
    pascalCenteredXiPrimeSidePhasePrimitive a r T =
      (pascalCenteredXiPrimeSideComplexPhasePotential r
          ((a : ℂ) + (T : ℂ) * Complex.I) -
        pascalCenteredXiPrimeSideComplexPhasePotential r (a : ℂ)).im := by
  by_cases hr : r = 0
  · subst r
    simp only [pascalCenteredXiPrimeSidePhasePrimitive_zero_frequency,
      Complex.sub_im]
    rw [cs27_phase_potential_vertical_im_zero,
      pascalCenteredXiPrimeSideComplexPhasePotential_ofReal_im]
    ring
  · rw [pascalCenteredXiPrimeSidePhasePrimitive_nonzero_frequency hr,
      Complex.sub_im,
      pascalCenteredXiPrimeSideComplexPhasePotential_ofReal_im]
    simpa using (cs27_phase_potential_vertical_im_nonzero
      (a := a) (r := r) (T := T) hr).symm

theorem pascalCenteredXiPrimeSidePhasePrimitive_eq_im_potential_endpoint
    (a r T : ℝ) :
    pascalCenteredXiPrimeSidePhasePrimitive a r T =
      (pascalCenteredXiPrimeSideComplexPhasePotential r
        ((a : ℂ) + (T : ℂ) * Complex.I)).im := by
  rw [pascalCenteredXiPrimeSidePhasePrimitive_eq_im_potential_jump,
    Complex.sub_im,
    pascalCenteredXiPrimeSideComplexPhasePotential_ofReal_im]
  simp

/-! ## CS27-C: one-mode holomorphic Mellin potential -/

noncomputable def pascalCenteredXiPrimeSideComplexModePhasePotential
    (ε : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  if n = 0 then 0 else
    (pascalCenteredXiPrimeSidePhaseCarrier ε n : ℂ) *
      (pascalCenteredXiPrimeSideComplexPhasePotential
          (pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n) z -
        pascalCenteredXiPrimeSideComplexPhasePotential
          (pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n) z)

private theorem cs27_nat_cpow_neg_half
    {n : ℕ} (hn : 0 < n) :
    (n : ℂ) ^ (-(1 / 2 : ℂ)) =
      ((Real.exp (-(1 / 2 : ℝ) * Real.log (n : ℝ))) : ℂ) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne')]
  rw [← Complex.natCast_log]
  norm_num [Complex.ofReal_exp]
  congr 1
  ring

theorem pascalCenteredXiPrimeSideComplexModePhasePotential_hasDerivAt
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 0 < n) (z : ℂ) :
    HasDerivAt
      (pascalCenteredXiPrimeSideComplexModePhasePotential ε n)
      (mellinQuadraticBoxWeight ε z *
        ((n : ℂ) ^ (-(criticalLineCenter + z)))) z := by
  let rPlus := pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n
  let rMinus := pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n
  have hp := pascalCenteredXiPrimeSideComplexPhasePotential_hasDerivAt rPlus z
  have hm := pascalCenteredXiPrimeSideComplexPhasePotential_hasDerivAt rMinus z
  have hsum := hp.sub hm
  have hscaled := hsum.const_mul
    (pascalCenteredXiPrimeSidePhaseCarrier ε n : ℂ)
  have hderiv : HasDerivAt
      (pascalCenteredXiPrimeSideComplexModePhasePotential ε n)
      ((pascalCenteredXiPrimeSidePhaseCarrier ε n : ℂ) *
        (z * Complex.exp ((rPlus : ℂ) * z) -
          z * Complex.exp ((rMinus : ℂ) * z))) z := by
    have hfun : pascalCenteredXiPrimeSideComplexModePhasePotential ε n =
        (fun y : ℂ => (pascalCenteredXiPrimeSidePhaseCarrier ε n : ℂ) *
          (pascalCenteredXiPrimeSideComplexPhasePotential rPlus y -
            pascalCenteredXiPrimeSideComplexPhasePotential rMinus y)) := by
      funext y
      simp [pascalCenteredXiPrimeSideComplexModePhasePotential, hn.ne',
        rPlus, rMinus]
    rw [hfun]
    exact hscaled
  have htransport := pascalCenteredXiPrimeSideModePhaseTransport hε hn z
  have hcarrier :
      (pascalCenteredXiPrimeSidePhaseCarrier ε n : ℂ) =
        ((n : ℂ) ^ (-(1 / 2 : ℂ))) * ((2 * ε : ℝ)⁻¹ : ℂ) := by
    rw [cs27_nat_cpow_neg_half hn]
    simp [pascalCenteredXiPrimeSidePhaseCarrier]
    ring
  have hderiv_eq :
      (pascalCenteredXiPrimeSidePhaseCarrier ε n : ℂ) *
          (z * Complex.exp ((rPlus : ℂ) * z) -
            z * Complex.exp ((rMinus : ℂ) * z)) =
        mellinQuadraticBoxWeight ε z *
          ((n : ℂ) ^ (-(criticalLineCenter + z))) := by
    rw [hcarrier]
    have hplus : (rPlus : ℂ) = ((ε : ℝ) : ℂ) - (Real.log n : ℂ) := by
      change ((pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n : ℝ) : ℂ) = _
      simp [pascalCenteredXiPrimeSidePhaseFrequencyPlus]
    have hminus : (rMinus : ℂ) = ((-ε : ℝ) : ℂ) - (Real.log n : ℂ) := by
      change ((pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n : ℝ) : ℂ) = _
      simp [pascalCenteredXiPrimeSidePhaseFrequencyMinus]
    rw [hplus, hminus]
    have heplus : Complex.exp ((((ε : ℝ) : ℂ) - (Real.log n : ℂ)) * z) =
        Complex.exp (((ε : ℝ) : ℂ) * z - (Real.log n : ℂ) * z) := by
      congr 1
      ring
    have heminus : Complex.exp ((((-ε : ℝ) : ℂ) - (Real.log n : ℂ)) * z) =
        Complex.exp (((-ε : ℝ) : ℂ) * z - (Real.log n : ℂ) * z) := by
      congr 1
      ring
    calc
      ((n : ℂ) ^ (-(1 / 2 : ℂ))) * ((2 * ε : ℝ)⁻¹ : ℂ) *
          (z * Complex.exp ((((ε : ℝ) : ℂ) - (Real.log n : ℂ)) * z) -
            z * Complex.exp ((((-ε : ℝ) : ℂ) - (Real.log n : ℂ)) * z)) =
          ((n : ℂ) ^ (-(1 / 2 : ℂ))) *
            (((2 * ε : ℝ)⁻¹ : ℂ) * z) *
              (Complex.exp (((ε : ℝ) : ℂ) * z - (Real.log n : ℂ) * z) -
                Complex.exp (((-ε : ℝ) : ℂ) * z - (Real.log n : ℂ) * z)) := by
            rw [heplus, heminus]
            ring
      _ = mellinQuadraticBoxWeight ε z *
          ((n : ℂ) ^ (-(criticalLineCenter + z))) := htransport.symm
  rw [hderiv_eq] at hderiv
  exact hderiv

theorem pascalCenteredXiPrimeSideFiniteModeKernel_eq_im_complexModePhasePotential_jump
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) {n : ℕ} (hn : 0 < n) :
    pascalCenteredXiPrimeSideFiniteModeKernel ε W n =
      (pascalCenteredXiPrimeSideComplexModePhasePotential ε n
          ((((W.rectangle.σ - (1 / 2 : ℝ)) : ℝ) : ℂ) +
            (W.rectangle.T : ℂ) * Complex.I) -
        pascalCenteredXiPrimeSideComplexModePhasePotential ε n
          ((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ)).im := by
  rw [pascalCenteredXiPrimeSideFiniteModeKernel_eq_phasePrimitive_difference hε W hn]
  unfold pascalCenteredXiPrimeSideComplexModePhasePotential
  simp only [if_neg hn.ne']
  have hp := pascalCenteredXiPrimeSidePhasePrimitive_eq_im_potential_endpoint
    (W.rectangle.σ - (1 / 2 : ℝ))
    (pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n) W.rectangle.T
  have hm := pascalCenteredXiPrimeSidePhasePrimitive_eq_im_potential_endpoint
    (W.rectangle.σ - (1 / 2 : ℝ))
    (pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n) W.rectangle.T
  have hbasep := pascalCenteredXiPrimeSideComplexPhasePotential_ofReal_im
    (pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n)
    (W.rectangle.σ - (1 / 2 : ℝ))
  have hbasem := pascalCenteredXiPrimeSideComplexPhasePotential_ofReal_im
    (pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n)
    (W.rectangle.σ - (1 / 2 : ℝ))
  have hscalar : ∀ (c : ℝ) (z₁ z₂ w₁ w₂ : ℂ),
      (((c : ℂ) * (z₁ - z₂) - (c : ℂ) * (w₁ - w₂)).im) =
        c * (z₁.im - z₂.im - (w₁.im - w₂.im)) := by
    intro c z₁ z₂ w₁ w₂
    simp [Complex.sub_im, Complex.mul_im]
    ring
  have hIm :
      ((pascalCenteredXiPrimeSidePhaseCarrier ε n : ℂ) *
          (pascalCenteredXiPrimeSideComplexPhasePotential
              (pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n)
              ((((W.rectangle.σ - (1 / 2 : ℝ)) : ℝ) : ℂ) +
                (W.rectangle.T : ℂ) * Complex.I) -
            pascalCenteredXiPrimeSideComplexPhasePotential
              (pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n)
              ((((W.rectangle.σ - (1 / 2 : ℝ)) : ℝ) : ℂ) +
                (W.rectangle.T : ℂ) * Complex.I)) -
        (pascalCenteredXiPrimeSidePhaseCarrier ε n : ℂ) *
          (pascalCenteredXiPrimeSideComplexPhasePotential
              (pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n)
              ((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ) -
            pascalCenteredXiPrimeSideComplexPhasePotential
              (pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n)
              ((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ))).im =
        pascalCenteredXiPrimeSidePhaseCarrier ε n *
          (((pascalCenteredXiPrimeSideComplexPhasePotential
              (pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n)
              ((((W.rectangle.σ - (1 / 2 : ℝ)) : ℝ) : ℂ) +
                (W.rectangle.T : ℂ) * Complex.I)).im -
            (pascalCenteredXiPrimeSideComplexPhasePotential
              (pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n)
              ((((W.rectangle.σ - (1 / 2 : ℝ)) : ℝ) : ℂ) +
                (W.rectangle.T : ℂ) * Complex.I)).im) -
            ((pascalCenteredXiPrimeSideComplexPhasePotential
              (pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n)
              ((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ)).im -
            (pascalCenteredXiPrimeSideComplexPhasePotential
              (pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n)
              ((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ)).im)) := by
    exact hscalar _ _ _ _ _
  have hbasep' :
      (pascalCenteredXiPrimeSideComplexPhasePotential
        (pascalCenteredXiPrimeSidePhaseFrequencyPlus ε n)
        ((W.rectangle.σ : ℂ) - ((1 / 2 : ℝ) : ℂ))).im = 0 := by
    convert hbasep using 1; norm_num
  have hbasem' :
      (pascalCenteredXiPrimeSideComplexPhasePotential
        (pascalCenteredXiPrimeSidePhaseFrequencyMinus ε n)
        ((W.rectangle.σ : ℂ) - ((1 / 2 : ℝ) : ℂ))).im = 0 := by
    convert hbasem using 1; norm_num
  rw [hIm, ← hp, ← hm, hbasep', hbasem']
  ring

theorem pascalCenteredXiPrimeSideRealScalar_im_sub
    (c : ℝ) (z₁ z₂ w₁ w₂ : ℂ) :
    (((c : ℂ) * (z₁ - z₂) - (c : ℂ) * (w₁ - w₂)).im) =
      c * (z₁.im - z₂.im - (w₁.im - w₂.im)) := by
  simp [Complex.sub_im, Complex.mul_im]
  ring

/-! ## CS27-D: finite aggregate potential -/

noncomputable def pascalCenteredXiPrimeSideAggregateComplexPhasePotential
    (ε : ℝ) (_W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) (z : ℂ) : ℂ :=
  2 * (∑ n ∈ Finset.range (X + 1),
    (ArithmeticFunction.vonMangoldt n : ℂ) *
      pascalCenteredXiPrimeSideComplexModePhasePotential ε n z)

theorem pascalCenteredXiPrimeSideAggregateInteraction_eq_im_complexAggregatePhaseJump
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X =
      (pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
          ((((W.rectangle.σ - (1 / 2 : ℝ)) : ℝ) : ℂ) +
            (W.rectangle.T : ℂ) * Complex.I) -
        pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
          ((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ)).im := by
  classical
  rw [pascalCenteredXiPrimeSideAggregateRayInteractionEnergy_eq_two_modeSum hε W X]
  have hterm : ∀ {n : ℕ}, n ∈ Finset.range (X + 1) →
      ((ArithmeticFunction.vonMangoldt n : ℂ) *
          pascalCenteredXiPrimeSideComplexModePhasePotential ε n
            ((((W.rectangle.σ - (1 / 2 : ℝ)) : ℝ) : ℂ) +
              (W.rectangle.T : ℂ) * Complex.I)).im -
        ((ArithmeticFunction.vonMangoldt n : ℂ) *
          pascalCenteredXiPrimeSideComplexModePhasePotential ε n
            ((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ)).im =
      (ArithmeticFunction.vonMangoldt n : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W n := by
    intro n hnX
    by_cases hn0 : n = 0
    · subst n
      simp [pascalCenteredXiPrimeSideComplexModePhasePotential,
        pascalCenteredXiPrimeSideFiniteModeKernel]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hk := pascalCenteredXiPrimeSideFiniteModeKernel_eq_im_complexModePhasePotential_jump
        hε W hnpos
      rw [← Complex.sub_im, ← mul_sub, hk]
      simp [Complex.mul_im]
  unfold pascalCenteredXiPrimeSideAggregateComplexPhasePotential
  simp only [Complex.sub_im, Complex.mul_im, Complex.im_sum]
  norm_num
  rw [← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hnX
  simpa [Complex.mul_im] using (hterm hnX).symm

/-! ## CS27-E/F/G: finite companion and the genuine comparison frontier -/

noncomputable def pascalCenteredXiPrimeSideFiniteArithmeticTopEdgeCompanion
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℂ :=
  pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
      (-((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ) +
        (W.rectangle.T : ℂ) * Complex.I) -
    pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
      (((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ) +
        (W.rectangle.T : ℂ) * Complex.I)

theorem pascalCenteredXiPrimeSideFiniteArithmeticTopEdgeCompanion_eq_oriented_endpoint_jump
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiPrimeSideFiniteArithmeticTopEdgeCompanion ε W X =
      pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
        (-((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ) +
          (W.rectangle.T : ℂ) * Complex.I) -
        pascalCenteredXiPrimeSideAggregateComplexPhasePotential ε W X
          (((W.rectangle.σ - (1 / 2 : ℝ)) : ℂ) +
            (W.rectangle.T : ℂ) * Complex.I) := by
  rfl

inductive PascalCenteredXiPrimeSideHolomorphicPhaseTopMismatchGap : Prop
  | noIndependentTopMismatchEstimate

end DkMath.RH.CFBRCProjection
