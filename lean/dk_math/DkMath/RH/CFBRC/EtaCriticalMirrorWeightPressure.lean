/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorWeightedTransport
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorWeightPressure"

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-- Every informative eta index `m > 0` has transport base strictly above one. -/
theorem one_lt_etaCriticalMirrorTransportBase
    {m : ℕ} (hm : 0 < m) :
    (1 : ℝ) < (((m + 1 : ℕ) : ℝ)) := by
  exact_mod_cast Nat.succ_lt_succ hm

/-- Right of the critical line, every informative mirror transport expands magnitude. -/
theorem one_lt_norm_etaCriticalMirrorTermWeight_of_half_lt_re
    {s : ℂ} (hre : (1 : ℝ) / 2 < s.re)
    {m : ℕ} (hm : 0 < m) :
    1 < ‖etaCriticalMirrorTermWeight s m‖ := by
  rw [norm_etaCriticalMirrorTermWeight]
  apply Real.one_lt_rpow
  · exact one_lt_etaCriticalMirrorTransportBase hm
  · have hcenter : 0 < centeredSigma s.re := by
      unfold centeredSigma
      linarith
    positivity

/-- Left of the critical line, every informative mirror transport contracts magnitude. -/
theorem norm_etaCriticalMirrorTermWeight_lt_one_of_re_lt_half
    {s : ℂ} (hre : s.re < (1 : ℝ) / 2)
    {m : ℕ} (hm : 0 < m) :
    ‖etaCriticalMirrorTermWeight s m‖ < 1 := by
  rw [norm_etaCriticalMirrorTermWeight]
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact one_lt_etaCriticalMirrorTransportBase hm
  · have hcenter : centeredSigma s.re < 0 := by
      unfold centeredSigma
      linarith
    nlinarith

/-- At the critical line, every transport weight has unit magnitude. -/
theorem norm_etaCriticalMirrorTermWeight_eq_one_of_re_eq_half
    {s : ℂ} (hre : s.re = (1 : ℝ) / 2) (m : ℕ) :
    ‖etaCriticalMirrorTermWeight s m‖ = 1 := by
  rw [etaCriticalMirrorTermWeight_eq_one_of_re_eq_half hre]
  simp

/--
For every informative eta term, unit transport magnitude is equivalent to the
critical-line condition.
-/
theorem norm_etaCriticalMirrorTermWeight_eq_one_iff_re_eq_half
    (s : ℂ) {m : ℕ} (hm : 0 < m) :
    ‖etaCriticalMirrorTermWeight s m‖ = 1 ↔
      s.re = (1 : ℝ) / 2 := by
  constructor
  · intro hunit
    rcases lt_trichotomy s.re ((1 : ℝ) / 2) with hleft | hline | hright
    · have hlt :=
        norm_etaCriticalMirrorTermWeight_lt_one_of_re_lt_half hleft hm
      linarith
    · exact hline
    · have hgt :=
        one_lt_norm_etaCriticalMirrorTermWeight_of_half_lt_re hright hm
      linarith
  · intro hre
    exact norm_etaCriticalMirrorTermWeight_eq_one_of_re_eq_half hre m

/-- Right of the critical line, the norm defect is strictly positive. -/
theorem norm_etaCriticalMirrorTermWeight_sub_one_pos_of_half_lt_re
    {s : ℂ} (hre : (1 : ℝ) / 2 < s.re)
    {m : ℕ} (hm : 0 < m) :
    0 < ‖etaCriticalMirrorTermWeight s m‖ - 1 :=
  sub_pos.mpr
    (one_lt_norm_etaCriticalMirrorTermWeight_of_half_lt_re hre hm)

/-- Left of the critical line, the norm defect is strictly negative. -/
theorem norm_etaCriticalMirrorTermWeight_sub_one_neg_of_re_lt_half
    {s : ℂ} (hre : s.re < (1 : ℝ) / 2)
    {m : ℕ} (hm : 0 < m) :
    ‖etaCriticalMirrorTermWeight s m‖ - 1 < 0 :=
  sub_neg.mpr
    (norm_etaCriticalMirrorTermWeight_lt_one_of_re_lt_half hre hm)

/-- Complete left/center/right pressure classification for every informative term. -/
theorem etaCriticalMirrorTermWeight_pressure_trichotomy
    (s : ℂ) {m : ℕ} (hm : 0 < m) :
    (s.re < (1 : ℝ) / 2 ∧ ‖etaCriticalMirrorTermWeight s m‖ < 1) ∨
    (s.re = (1 : ℝ) / 2 ∧ ‖etaCriticalMirrorTermWeight s m‖ = 1) ∨
    ((1 : ℝ) / 2 < s.re ∧ 1 < ‖etaCriticalMirrorTermWeight s m‖) := by
  rcases lt_trichotomy s.re ((1 : ℝ) / 2) with hleft | hline | hright
  · exact Or.inl ⟨hleft,
      norm_etaCriticalMirrorTermWeight_lt_one_of_re_lt_half hleft hm⟩
  · exact Or.inr <| Or.inl ⟨hline,
      norm_etaCriticalMirrorTermWeight_eq_one_of_re_eq_half hline m⟩
  · exact Or.inr <| Or.inr ⟨hright,
      one_lt_norm_etaCriticalMirrorTermWeight_of_half_lt_re hright hm⟩

end DkMath.RH.CFBRCProjection
