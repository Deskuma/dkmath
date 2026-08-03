/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorDefectCoefficientMargin
import Mathlib.Tactic
import DkMath.ABC.Basic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorContinuousWeightThreshold"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology

/-- Every positive real power of the eta-pair left endpoint eventually exceeds two. -/
private theorem eventually_two_le_etaPairFrameLeftEndpoint_rpow
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ k : ℕ in atTop,
      2 ≤ etaPairFrameLeftEndpoint k ^ a := by
  let M : ℝ := (2 : ℝ) ^ (1 / a)
  have hM : 0 < M := by
    dsimp [M]
    positivity
  let N : ℕ := Nat.ceil M
  apply eventually_atTop.2
  refine ⟨N, ?_⟩
  intro k hk
  have hMleN : M ≤ (N : ℝ) := by
    dsimp [N]
    have hspec := DkMath.ABC.Nat.ceil_spec M hM.le
    exact_mod_cast hspec.2
  have hNleLeft : (N : ℝ) ≤ etaPairFrameLeftEndpoint k := by
    unfold etaPairFrameLeftEndpoint
    exact_mod_cast (le_trans hk (by omega : k ≤ 2 * k + 1))
  have hMleLeft : M ≤ etaPairFrameLeftEndpoint k :=
    hMleN.trans hNleLeft
  have hpow :
      M ^ a ≤ etaPairFrameLeftEndpoint k ^ a :=
    Real.rpow_le_rpow hM.le hMleLeft ha.le
  have hMpow : M ^ a = 2 := by
    dsimp [M]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hmul : (1 / a) * a = 1 := by
      field_simp [ha.ne']
    rw [hmul]
    norm_num
  rwa [hMpow] at hpow

/-- Right of the critical line, the pair-left transport weight is eventually at least two. -/
theorem eventually_two_le_etaCriticalMirrorContinuousWeightR_leftEndpoint_of_half_lt_re
    {s : ℂ} (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ k : ℕ in atTop,
      2 ≤ etaCriticalMirrorContinuousWeightR s
        (etaPairFrameLeftEndpoint k) := by
  have ha : 0 < 2 * centeredSigma s.re := by
    unfold centeredSigma
    linarith
  simpa [etaCriticalMirrorContinuousWeightR] using
    (eventually_two_le_etaPairFrameLeftEndpoint_rpow ha)

/-- Left of the critical line, the pair-left transport weight is eventually at most one half. -/
theorem eventually_etaCriticalMirrorContinuousWeightR_leftEndpoint_le_half_of_re_lt_half
    {s : ℂ} (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ k : ℕ in atTop,
      etaCriticalMirrorContinuousWeightR s
        (etaPairFrameLeftEndpoint k) ≤ (1 : ℝ) / 2 := by
  let a : ℝ := -(2 * centeredSigma s.re)
  have ha : 0 < a := by
    dsimp [a, centeredSigma]
    linarith
  filter_upwards
    [eventually_two_le_etaPairFrameLeftEndpoint_rpow ha] with k hk
  have hleftPos : 0 < etaPairFrameLeftEndpoint k :=
    etaPairFrameLeftEndpoint_pos k
  have hinv :
      1 / (etaPairFrameLeftEndpoint k ^ a) ≤ (1 : ℝ) / 2 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hk
  unfold etaCriticalMirrorContinuousWeightR
  have hexp : 2 * centeredSigma s.re = -a :=
    Eq.symm (InvolutiveNeg.neg_neg (2 * centeredSigma s.re))
  rw [hexp, Real.rpow_neg hleftPos.le a]
  simpa [one_div] using hinv

/-- Right of the critical line,
    every point in every sufficiently late eta pair has weight at least two. -/
theorem eventually_two_le_etaCriticalMirrorContinuousWeightR_on_pair_of_half_lt_re
    {s : ℂ} (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ k : ℕ in atTop,
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        2 ≤ etaCriticalMirrorContinuousWeightR s x := by
  have ha : 0 ≤ 2 * centeredSigma s.re := by
    unfold centeredSigma
    linarith
  filter_upwards
    [eventually_two_le_etaCriticalMirrorContinuousWeightR_leftEndpoint_of_half_lt_re
      hre] with k hk
  intro x hleft _hright
  unfold etaCriticalMirrorContinuousWeightR at hk ⊢
  exact hk.trans
    (Real.rpow_le_rpow
      (etaPairFrameLeftEndpoint_pos k).le hleft ha)

/-- Left of the critical line,
    every point in every sufficiently late eta pair has weight at most one half. -/
theorem eventually_etaCriticalMirrorContinuousWeightR_on_pair_le_half_of_re_lt_half
    {s : ℂ} (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ k : ℕ in atTop,
      ∀ x : ℝ,
        etaPairFrameLeftEndpoint k ≤ x →
        x ≤ etaPairFrameRightEndpoint k →
        etaCriticalMirrorContinuousWeightR s x ≤ (1 : ℝ) / 2 := by
  have ha : 2 * centeredSigma s.re ≤ 0 := by
    unfold centeredSigma
    linarith
  filter_upwards
    [eventually_etaCriticalMirrorContinuousWeightR_leftEndpoint_le_half_of_re_lt_half
      hre] with k hk
  intro x hleft _hright
  unfold etaCriticalMirrorContinuousWeightR at hk ⊢
  exact
    (Real.rpow_le_rpow_of_nonpos
      (etaPairFrameLeftEndpoint_pos k) hleft ha).trans hk

end DkMath.RH.CFBRCProjection
