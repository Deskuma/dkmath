/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.Weave.Analytic.EtaContinuationDomains
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Tactic

#print "file: DkMath.RH.Weave.Analytic.EtaPairedContinuation"

noncomputable section

namespace DkMath.RH.Weave.Analytic

open Filter Set
open scoped Topology

/-- A safe anchor in the upper-right absolute-convergence region. -/
noncomputable def etaUpperAnchor : ℂ := 2 + Complex.I

/-- A safe anchor in the lower-right absolute-convergence region. -/
noncomputable def etaLowerAnchor : ℂ := 2 - Complex.I

@[simp] theorem etaUpperAnchor_re : etaUpperAnchor.re = 2 := by
  simp [etaUpperAnchor]

@[simp] theorem etaUpperAnchor_im : etaUpperAnchor.im = 1 := by
  simp [etaUpperAnchor]

@[simp] theorem etaLowerAnchor_re : etaLowerAnchor.re = 2 := by
  simp [etaLowerAnchor]

@[simp] theorem etaLowerAnchor_im : etaLowerAnchor.im = -1 := by
  simp [etaLowerAnchor]

/-- The upper anchor belongs to the upper-right continuation domain. -/
theorem etaUpperAnchor_mem :
    etaUpperAnchor ∈ etaUpperRightHalfPlane := by
  norm_num [etaUpperRightHalfPlane]

/-- The lower anchor belongs to the lower-right continuation domain. -/
theorem etaLowerAnchor_mem :
    etaLowerAnchor ∈ etaLowerRightHalfPlane := by
  norm_num [etaLowerRightHalfPlane]

/-- The paired and raw analytic eta values agree near the upper anchor. -/
theorem etaPairedValue_eventuallyEq_analyticEta_upperAnchor :
    etaPairedValue =ᶠ[𝓝 etaUpperAnchor] analyticEta := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hmem : etaUpperAnchor ∈ {s : ℂ | 1 < s.re} := by
    norm_num
  filter_upwards [hopen.mem_nhds hmem] with s hs
  simpa [etaPairedValue, EtaPairedTsumIdentifiesAnalyticAt] using
    etaPairedTsumIdentifiesAnalyticAt_of_one_lt_re hs

/-- The paired and raw analytic eta values agree near the lower anchor. -/
theorem etaPairedValue_eventuallyEq_analyticEta_lowerAnchor :
    etaPairedValue =ᶠ[𝓝 etaLowerAnchor] analyticEta := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hmem : etaLowerAnchor ∈ {s : ℂ | 1 < s.re} := by
    norm_num
  filter_upwards [hopen.mem_nhds hmem] with s hs
  simpa [etaPairedValue, EtaPairedTsumIdentifiesAnalyticAt] using
    etaPairedTsumIdentifiesAnalyticAt_of_one_lt_re hs

/--
Identity theorem on the upper-right half-plane: the genuine paired eta value
agrees with the raw zeta-product eta away from the real axis.
-/
theorem etaPairedValue_eqOn_upperRightHalfPlane :
    Set.EqOn etaPairedValue analyticEta etaUpperRightHalfPlane := by
  have hpaired : AnalyticOnNhd ℂ etaPairedValue etaUpperRightHalfPlane :=
    etaPairedValue_differentiableOn_upperRightHalfPlane.analyticOnNhd
      isOpen_etaUpperRightHalfPlane
  have hanalytic : AnalyticOnNhd ℂ analyticEta etaUpperRightHalfPlane :=
    analyticEta_differentiableOn_upperRightHalfPlane.analyticOnNhd
      isOpen_etaUpperRightHalfPlane
  exact
    hpaired.eqOn_of_preconnected_of_eventuallyEq
      hanalytic
      isPreconnected_etaUpperRightHalfPlane
      etaUpperAnchor_mem
      etaPairedValue_eventuallyEq_analyticEta_upperAnchor

/--
Identity theorem on the lower-right half-plane: the genuine paired eta value
agrees with the raw zeta-product eta away from the real axis.
-/
theorem etaPairedValue_eqOn_lowerRightHalfPlane :
    Set.EqOn etaPairedValue analyticEta etaLowerRightHalfPlane := by
  have hpaired : AnalyticOnNhd ℂ etaPairedValue etaLowerRightHalfPlane :=
    etaPairedValue_differentiableOn_lowerRightHalfPlane.analyticOnNhd
      isOpen_etaLowerRightHalfPlane
  have hanalytic : AnalyticOnNhd ℂ analyticEta etaLowerRightHalfPlane :=
    analyticEta_differentiableOn_lowerRightHalfPlane.analyticOnNhd
      isOpen_etaLowerRightHalfPlane
  exact
    hpaired.eqOn_of_preconnected_of_eventuallyEq
      hanalytic
      isPreconnected_etaLowerRightHalfPlane
      etaLowerAnchor_mem
      etaPairedValue_eventuallyEq_analyticEta_lowerAnchor

/--
The paired eta infinite sum equals analytic eta at every nonreal point of the
open right half-plane.
-/
theorem etaPairedValue_eq_analyticEta_of_pos_re_of_im_ne_zero
    {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0) :
    etaPairedValue s = analyticEta s := by
  rcases lt_or_gt_of_ne him with himneg | himpos
  · exact etaPairedValue_eqOn_lowerRightHalfPlane ⟨hre, himneg⟩
  · exact etaPairedValue_eqOn_upperRightHalfPlane ⟨hre, himpos⟩

/-- Value-identification obligation discharged at every nonreal right-half-plane point. -/
theorem etaPairedTsumIdentifiesAnalyticAt_of_pos_re_of_im_ne_zero
    {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0) :
    EtaPairedTsumIdentifiesAnalyticAt s := by
  change etaPairedValue s = analyticEta s
  exact etaPairedValue_eq_analyticEta_of_pos_re_of_im_ne_zero hre him

/-- Genuine finite eta endpoints converge to analytic eta off the real axis. -/
theorem etaPartialConvergesAt_of_pos_re_of_im_ne_zero
    {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0) :
    EtaPartialConvergesAt s := by
  exact etaPartialConvergesAt_of_pos_re hre
    (etaPairedTsumIdentifiesAnalyticAt_of_pos_re_of_im_ne_zero hre him)

/--
A standard zeta zero at a nonreal right-half-plane point forces the genuine
finite eta endpoints to converge to zero.
-/
theorem etaPartialEndpoint_tendsto_zero_of_riemannZeta_eq_zero_of_pos_re_of_im_ne_zero
    {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0)
    (hz : riemannZeta s = 0) :
    Tendsto (fun N : ℕ => DkMath.RH.CFBRCProjection.etaPartialEndpoint N s)
      atTop (nhds 0) := by
  exact etaPartialEndpoint_tendsto_zero_of_riemannZeta_eq_zero
    (etaPartialConvergesAt_of_pos_re_of_im_ne_zero hre him) hz

end DkMath.RH.Weave.Analytic
