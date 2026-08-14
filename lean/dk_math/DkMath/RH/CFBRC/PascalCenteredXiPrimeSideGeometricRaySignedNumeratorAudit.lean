/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteGeometricRayAudit
import Mathlib.Tactic

/-!
# CS16: geometric-ray signed numerator audit

The finite prime-power ray is rationalized pointwise over a strictly positive
complex norm-square denominator.  The remaining sign information is named as
a finite numerator.  This module contains no infinite ray, no infinite
sum/integral exchange, no synthetic sign provider, and no RH conclusion.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open MeasureTheory
open scoped ComplexConjugate Interval Topology

/-! ## CS16-A: canonical finite ray length -/

noncomputable def pascalCenteredXiPrimeSidePrimePowerRayLength
    (X p : ℕ) : ℕ :=
  (pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p).card

theorem pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo_eq_range_rayLength
    {X p : ℕ} (hp : Nat.Prime p) :
    pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p =
      Finset.range (pascalCenteredXiPrimeSidePrimePowerRayLength X p) := by
  let s := pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p
  have hdown : ∀ {k l : ℕ}, l ∈ s → k ≤ l → k ∈ s := by
    intro k l hl hkl
    exact pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo_downward
      hp hl hkl
  have hsub : s ⊆ Finset.range s.card := by
    intro k hk
    by_contra hnot
    have hsub' : Finset.range (k + 1) ⊆ s := by
      intro l hl
      have hl' := Finset.mem_range.mp hl
      exact hdown hk (by omega)
    have hle : k + 1 ≤ s.card := by
      simpa using (Finset.card_le_card hsub')
    have hnot' : ¬ k < s.card := by
      simpa [Finset.mem_range] using hnot
    omega
  have hsup : Finset.range s.card ⊆ s := by
    intro k hk
    have hklt : k < s.card := Finset.mem_range.mp hk
    by_contra hnot
    have hsub' : s ⊆ Finset.range k := by
      intro l hl
      apply Finset.mem_range.mpr
      by_contra hlt
      have hkl : k ≤ l := by omega
      exact False.elim (hnot (hdown hl hkl))
    have hle : s.card ≤ k := by
      simpa using (Finset.card_le_card hsub')
    omega
  have hs : s = Finset.range s.card := Finset.Subset.antisymm hsub hsup
  simpa [s, pascalCenteredXiPrimeSidePrimePowerRayLength] using hs

/-! ## CS16-B: strict right-edge contraction -/

noncomputable def pascalCenteredXiPrimeSidePrimeRatioAtRightEdge
    (W : PascalCenteredXiResidueTransportWindow) (p : ℕ) (t : ℝ) : ℂ :=
  pascalCenteredXiPrimeSidePrimeRatio p
    (pascalSymmetricRectangleRightEdge W.rectangle.σ t)

theorem pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_norm
    (W : PascalCenteredXiResidueTransportWindow) {p : ℕ}
    (hp : Nat.Prime p) (t : ℝ) :
    ‖pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t‖ =
      (p : ℝ) ^ (-W.rectangle.σ) := by
  unfold pascalCenteredXiPrimeSidePrimeRatioAtRightEdge
    pascalCenteredXiPrimeSidePrimeRatio
  rw [← Complex.ofReal_natCast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos]
  · simp [pascalSymmetricRectangleRightEdge]
  · exact_mod_cast hp.pos

theorem pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_norm_lt_one
    (W : PascalCenteredXiResidueTransportWindow) {p : ℕ}
    (hp : Nat.Prime p) (t : ℝ) :
    ‖pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t‖ < 1 := by
  rw [pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_norm W hp t]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt)
    (by linarith [W.rectangle.hσ])

theorem pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_ne_one
    (W : PascalCenteredXiResidueTransportWindow) {p : ℕ}
    (hp : Nat.Prime p) (t : ℝ) :
    pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t ≠ 1 := by
  intro hq
  have hnorm := pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_norm_lt_one W hp t
  rw [hq] at hnorm
  norm_num at hnorm

theorem pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_one_sub_ne_zero
    (W : PascalCenteredXiResidueTransportWindow) {p : ℕ}
    (hp : Nat.Prime p) (t : ℝ) :
    1 - pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t ≠ 0 := by
  exact sub_ne_zero.mpr (Ne.symm
    (pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_ne_one W hp t))

theorem pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_one_sub_normSq_pos
    (W : PascalCenteredXiResidueTransportWindow) {p : ℕ}
    (hp : Nat.Prime p) (t : ℝ) :
    0 < Complex.normSq
      (1 - pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t) :=
  Complex.normSq_pos.mpr
    (pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_one_sub_ne_zero W hp t)

/-! ## CS16-C: unconditional finite geometric amplitude -/

theorem pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_eq_weight_mul_canonicalGeometricCore
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t =
      pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideModePhaseNode W t) *
        pascalCenteredXiPrimeSideFiniteGeometricRayCore
          (pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t)
          (pascalCenteredXiPrimeSidePrimePowerRayLength X p) := by
  rw [pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_eq_weight_mul_ratio_core
      W hp t,
    pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo_eq_range_rayLength hp]
  unfold pascalCenteredXiPrimeSideFiniteGeometricRayCore
  rw [Finset.mul_sum]
  simp [pascalCenteredXiPrimeSidePrimeRatioAtRightEdge]

theorem pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_weighted_compression
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    (1 - pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t) *
        pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t =
      pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideModePhaseNode W t) *
        (pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t -
          pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t ^
            (pascalCenteredXiPrimeSidePrimePowerRayLength X p + 1)) := by
  rw [pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_eq_weight_mul_canonicalGeometricCore
      W hp t]
  calc
    (1 - pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t) *
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideModePhaseNode W t) *
          pascalCenteredXiPrimeSideFiniteGeometricRayCore
            (pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t)
            (pascalCenteredXiPrimeSidePrimePowerRayLength X p)) =
      pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideModePhaseNode W t) *
        ((1 - pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t) *
          pascalCenteredXiPrimeSideFiniteGeometricRayCore
            (pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t)
            (pascalCenteredXiPrimeSidePrimePowerRayLength X p)) := by ring
    _ = _ := by
      rw [pascalCenteredXiPrimeSideFiniteGeometricRayCore_compression]

/-! ## CS16-D: rationalized positive-denominator identity -/

noncomputable def pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) : ℝ :=
  Complex.re
    (pascalCenteredXiMellinSecondDifferenceWeight ε 0
        (pascalCenteredXiPrimeSideModePhaseNode W t) *
      (pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t -
        pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t ^
          (pascalCenteredXiPrimeSidePrimePowerRayLength X p + 1)) *
      conj
        (1 - pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t))

theorem complex_re_div_eq_re_mul_conj_div_normSq
    {z w : ℂ} (hw : w ≠ 0) :
    (z / w).re = (z * conj w).re / Complex.normSq w := by
  rw [Complex.div_re]
  have hnorm : Complex.normSq w ≠ 0 :=
    (Complex.normSq_eq_zero.not.mpr hw)
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  field_simp [hnorm]
  ring

theorem pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_re_eq_signedNumerator_div_normSq
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t).re =
      pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator ε W X p t /
        Complex.normSq (1 - pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t) := by
  let q := pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t
  let h := pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalCenteredXiPrimeSideModePhaseNode W t)
  let m := pascalCenteredXiPrimeSidePrimePowerRayLength X p
  have hq : 1 - q ≠ 0 := by
    exact pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_one_sub_ne_zero W hp t
  have hquot : pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t =
      (h * (q - q ^ (m + 1))) / (1 - q) := by
    apply (eq_div_iff hq).2
    calc
      pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t * (1 - q) =
          (1 - q) * pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t := by ring
      _ = h * (q - q ^ (m + 1)) := by
        exact pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_weighted_compression
          W hp t
  rw [hquot]
  exact complex_re_div_eq_re_mul_conj_div_normSq hq

/-! ## CS16-E: pointwise sign reduction -/

theorem pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_re_nonneg_iff_signedNumerator_nonneg
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    0 ≤ (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t).re ↔
      0 ≤ pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator ε W X p t := by
  rw [pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_re_eq_signedNumerator_div_normSq
    W hp t]
  have hd := pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_one_sub_normSq_pos W hp t
  constructor
  · intro h
    rw [← div_mul_cancel₀
      (pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator ε W X p t) hd.ne']
    exact mul_nonneg h hd.le
  · exact fun h => div_nonneg h hd.le

theorem pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_re_nonpos_iff_signedNumerator_nonpos
    {ε : ℝ} (W : PascalCenteredXiResidueTransportWindow)
    {X p : ℕ} (hp : Nat.Prime p) (t : ℝ) :
    (pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude ε W X p t).re ≤ 0 ↔
      pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator ε W X p t ≤ 0 := by
  rw [pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude_re_eq_signedNumerator_div_normSq
    W hp t]
  have hd := pascalCenteredXiPrimeSidePrimeRatioAtRightEdge_one_sub_normSq_pos W hp t
  constructor
  · intro h
    rw [← div_mul_cancel₀
      (pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator ε W X p t) hd.ne']
    exact mul_nonpos_of_nonpos_of_nonneg h hd.le
  · exact fun h => div_nonpos_of_nonpos_of_nonneg h hd.le

/-! ## CS16-F/G: endpoint ledger and denominator geometry -/

theorem pascalCenteredXiPrimeSideGeometricRayEndpointExpansion
    (q : ℂ) (m : ℕ) :
    (q - q ^ (m + 1)) * conj (1 - q) =
      q - (Complex.normSq q : ℂ) - q ^ (m + 1) +
        (Complex.normSq q : ℂ) * q ^ m := by
  simp only [map_sub, map_one]
  calc
    (q - q ^ (m + 1)) * (1 - conj q) =
        q - q * conj q - q ^ (m + 1) + q ^ (m + 1) * conj q := by ring
    _ = q - (Complex.normSq q : ℂ) - q ^ (m + 1) +
        (Complex.normSq q : ℂ) * q ^ m := by
      rw [Complex.mul_conj]
      have hlast : q ^ (m + 1) * conj q =
          (Complex.normSq q : ℂ) * q ^ m := by
        rw [pow_succ, mul_assoc, Complex.mul_conj]
        ring
      rw [hlast]

theorem pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator_eq_endpointLedger
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) :
    pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator ε W X p t =
      Complex.re
        (pascalCenteredXiMellinSecondDifferenceWeight ε 0
            (pascalCenteredXiPrimeSideModePhaseNode W t) *
          (pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t -
            (Complex.normSq (pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t) : ℂ) -
            pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t ^
              (pascalCenteredXiPrimeSidePrimePowerRayLength X p + 1) +
            (Complex.normSq (pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t) : ℂ) *
              pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t ^
      (pascalCenteredXiPrimeSidePrimePowerRayLength X p))) := by
  unfold pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator
  calc
    (pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideModePhaseNode W t) *
        (pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t -
          pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t ^
            (pascalCenteredXiPrimeSidePrimePowerRayLength X p + 1)) *
        conj (1 - pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t)).re =
      (pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalCenteredXiPrimeSideModePhaseNode W t) *
        ((pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t -
          pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t ^
            (pascalCenteredXiPrimeSidePrimePowerRayLength X p + 1)) *
          conj (1 - pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t))).re := by
            rw [mul_assoc]
    _ = _ := by rw [pascalCenteredXiPrimeSideGeometricRayEndpointExpansion]

theorem pascalCenteredXiPrimeSideOneSubRatio_normSq_expansion
    (q : ℂ) :
    Complex.normSq (1 - q) = 1 - 2 * q.re + Complex.normSq q := by
  simp [Complex.normSq_apply]
  ring

/-! ## CS16-H: signed numerator frontier -/

inductive PascalCenteredXiPrimeSideGeometricRaySignedNumeratorGap : Prop
  | noIndependentSignedNumeratorProvider

end DkMath.RH.CFBRCProjection
