/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CriticalMirrorGeometry
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CriticalMirrorZeroBridge"

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-- Reflection through the completed-zeta functional equation does not hit zero. -/
theorem one_sub_ne_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    1 - s ≠ 0 := by
  intro h
  apply hs.2.2
  exact (sub_eq_zero.mp h).symm

/-- A nontrivial zeta zero produces a standard zeta zero at `1 - s`. -/
theorem riemannZeta_one_sub_eq_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    riemannZeta (1 - s) = 0 := by
  rw [riemannZeta_def_of_ne_zero
    (one_sub_ne_zero_of_nontrivialRiemannZetaZero hs)]
  rw [completedRiemannZeta_one_sub_eq_zero_of_nontrivialRiemannZetaZero hs]
  simp

/-- Every standard nontrivial zeta zero lies strictly left of `re = 1`. -/
theorem nontrivialRiemannZetaZero_re_lt_one
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    s.re < 1 := by
  by_contra hlt
  have hle : 1 ≤ s.re := le_of_not_gt hlt
  exact (riemannZeta_ne_zero_of_one_le_re hle) hs.1

/-- Every standard nontrivial zeta zero lies strictly right of `re = 0`. -/
theorem nontrivialRiemannZetaZero_re_pos
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    0 < s.re := by
  by_contra hpos
  have hle : s.re ≤ 0 := le_of_not_gt hpos
  have hreflect : riemannZeta (1 - s) = 0 :=
    riemannZeta_one_sub_eq_zero_of_nontrivialRiemannZetaZero hs
  have hre : 1 ≤ (1 - s).re := by
    simp
    linarith
  exact (riemannZeta_ne_zero_of_one_le_re hre) hreflect

/-- Nontrivial zeros lie in the open critical strip. -/
theorem nontrivialRiemannZetaZero_mem_openCriticalStrip
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    0 < s.re ∧ s.re < 1 :=
  ⟨nontrivialRiemannZetaZero_re_pos hs,
    nontrivialRiemannZetaZero_re_lt_one hs⟩

/-- The critical mirror is the conjugate of the functional-equation reflection. -/
theorem criticalMirror_eq_star_one_sub (s : ℂ) :
    criticalMirror s = (starRingEnd ℂ) (1 - s) := by
  apply Complex.ext <;> simp [criticalMirror]

/-- The critical mirror of a nontrivial zero is again a zeta zero. -/
theorem riemannZeta_criticalMirror_eq_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    riemannZeta (criticalMirror s) = 0 := by
  calc
    riemannZeta (criticalMirror s) =
        riemannZeta ((starRingEnd ℂ) (1 - s)) := by
      rw [criticalMirror_eq_star_one_sub]
    _ = (starRingEnd ℂ) (riemannZeta (1 - s)) :=
      riemannZeta_conj (1 - s)
    _ = 0 := by
      rw [riemannZeta_one_sub_eq_zero_of_nontrivialRiemannZetaZero hs]
      simp

/-- The critical mirror also lies in the open right half-plane. -/
theorem criticalMirror_re_pos_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    0 < (criticalMirror s).re := by
  rw [criticalMirror_re]
  linarith [nontrivialRiemannZetaZero_re_lt_one hs]

/-- The critical mirror lies strictly left of `re = 1`. -/
theorem criticalMirror_re_lt_one_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    (criticalMirror s).re < 1 := by
  rw [criticalMirror_re]
  linarith [nontrivialRiemannZetaZero_re_pos hs]

/--
The nontrivial-zero predicate is closed under reflection across the critical
line.  This packages the functional equation, conjugation symmetry, and the
open-critical-strip bounds without assuming the Riemann hypothesis.

The local real-part normalization below deliberately keeps the broad `simp`
form that is stable under the current complex numeral coercions.
-/
theorem criticalMirror_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    NontrivialRiemannZetaZero (criticalMirror s) := by
  refine ⟨
    riemannZeta_criticalMirror_eq_zero_of_nontrivialRiemannZetaZero hs,
    ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    have hpos := criticalMirror_re_pos_of_nontrivialRiemannZetaZero hs
    have hpos' : 0 < 1 - s.re := by
      simpa [criticalMirror] using hpos
    simp [criticalMirror] at hre
    have hneg : -(2 * ((n : ℝ) + 1)) ≤ 0 := by
      exact neg_nonpos.mpr (by positivity)
    have hnonpos : 1 - s.re ≤ 0 := by
      rw [hre]
      exact hneg
    exact (not_lt_of_ge hnonpos) hpos'
  · intro hone
    have hre := congrArg Complex.re hone
    have hspos := nontrivialRiemannZetaZero_re_pos hs
    simp [criticalMirror] at hre
    linarith

end DkMath.RH.CFBRCProjection
