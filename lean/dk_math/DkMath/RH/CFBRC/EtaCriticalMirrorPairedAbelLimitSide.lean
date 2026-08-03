/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelTailMonotonicity
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelLimitSide"

set_option linter.style.longLine false

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter Set
open scoped Topology

/-- The real Abel-limit coordinate seen by the signed vertical projection. -/
noncomputable def etaCriticalMirrorRotatedDefectProjectionLimit
    (s : ℂ) : ℝ :=
  etaCriticalMirrorSignedVerticalProjection s
    (-(∑' k : ℕ,
      etaCriticalMirrorPairedFrameCorrectionTerm s k))

/-- Distance from the projected moving-frame partial sum to its Abel limit. -/
noncomputable def etaCriticalMirrorRotatedDefectProjectionLimitGap
    (K : ℕ) (s : ℂ) : ℝ :=
  etaCriticalMirrorRotatedDefectProjectionLimit s -
    etaCriticalMirrorRotatedDefectProjectionPartial K s

/-- A strictly increasing convergent natural tail stays strictly below its limit. -/
private theorem lt_limit_of_strictMonoOn_Ici_nat_of_tendsto
    {u : ℕ → ℝ} {L : ℝ} {K0 K : ℕ}
    (hmono : StrictMonoOn u (Ici K0))
    (hK : K0 ≤ K)
    (hlim : Tendsto u atTop (nhds L)) :
    u K < L := by
  have hK1 : K0 ≤ K + 1 := by omega
  have hstep : u K < u (K + 1) :=
    hmono (mem_Ici.mpr hK) (mem_Ici.mpr hK1) (by omega)
  have hnext_le : u (K + 1) ≤ L := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (K + 1)] with n hn
    exact hmono.monotoneOn
      (mem_Ici.mpr hK1)
      (mem_Ici.mpr (hK1.trans hn))
      hn
  exact hstep.trans_le hnext_le

/-- A strictly decreasing convergent natural tail stays strictly above its limit. -/
private theorem limit_lt_of_strictAntiOn_Ici_nat_of_tendsto
    {u : ℕ → ℝ} {L : ℝ} {K0 K : ℕ}
    (hanti : StrictAntiOn u (Ici K0))
    (hK : K0 ≤ K)
    (hlim : Tendsto u atTop (nhds L)) :
    L < u K := by
  have hK1 : K0 ≤ K + 1 := by omega
  have hstep : u (K + 1) < u K :=
    hanti (mem_Ici.mpr hK) (mem_Ici.mpr hK1) (by omega)
  have hlimit_le_next : L ≤ u (K + 1) := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (K + 1)] with n hn
    exact hanti.antitoneOn
      (mem_Ici.mpr hK1)
      (mem_Ici.mpr (hK1.trans hn))
      hn
  exact hlimit_le_next.trans_lt hstep

/-- The projected moving-frame partial sums converge to the named Abel-limit coordinate. -/
theorem etaCriticalMirrorRotatedDefectProjectionPartial_tendsto_limit
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    Tendsto
      (fun K : ℕ =>
        etaCriticalMirrorRotatedDefectProjectionPartial K s)
      atTop
      (nhds (etaCriticalMirrorRotatedDefectProjectionLimit s)) := by
  simpa [etaCriticalMirrorRotatedDefectProjectionLimit] using
    etaCriticalMirrorRotatedDefectProjectionPartial_tendsto_neg_correction_projection
      hs him

/-- Right of the critical line, every sufficiently late partial sum lies below its Abel limit. -/
theorem eventually_etaCriticalMirrorRotatedDefectProjectionPartial_lt_limit_of_half_lt_re
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRotatedDefectProjectionPartial K s <
        etaCriticalMirrorRotatedDefectProjectionLimit s := by
  rcases
    exists_etaCriticalMirrorRotatedDefectProjectionPartial_strictMonoOn_tail_of_half_lt_re
      hs him hre with ⟨K0, hmono⟩
  have hlim :=
    etaCriticalMirrorRotatedDefectProjectionPartial_tendsto_limit hs him
  filter_upwards [eventually_ge_atTop K0] with K hK
  exact lt_limit_of_strictMonoOn_Ici_nat_of_tendsto hmono hK hlim

/-- Left of the critical line, every sufficiently late partial sum lies above its Abel limit. -/
theorem eventually_etaCriticalMirrorRotatedDefectProjectionLimit_lt_partial_of_re_lt_half
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRotatedDefectProjectionLimit s <
        etaCriticalMirrorRotatedDefectProjectionPartial K s := by
  rcases
    exists_etaCriticalMirrorRotatedDefectProjectionPartial_strictAntiOn_tail_of_re_lt_half
      hs him hre with ⟨K0, hanti⟩
  have hlim :=
    etaCriticalMirrorRotatedDefectProjectionPartial_tendsto_limit hs him
  filter_upwards [eventually_ge_atTop K0] with K hK
  exact limit_lt_of_strictAntiOn_Ici_nat_of_tendsto hanti hK hlim

/-- Right of the critical line, the remaining projected Abel gap is eventually positive. -/
theorem eventually_etaCriticalMirrorRotatedDefectProjectionLimitGap_pos_of_half_lt_re
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∀ᶠ K : ℕ in atTop,
      0 < etaCriticalMirrorRotatedDefectProjectionLimitGap K s := by
  filter_upwards
    [eventually_etaCriticalMirrorRotatedDefectProjectionPartial_lt_limit_of_half_lt_re
      hs him hre] with K hK
  exact sub_pos.mpr hK

/-- Left of the critical line, the remaining projected Abel gap is eventually negative. -/
theorem eventually_etaCriticalMirrorRotatedDefectProjectionLimitGap_neg_of_re_lt_half
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRotatedDefectProjectionLimitGap K s < 0 := by
  filter_upwards
    [eventually_etaCriticalMirrorRotatedDefectProjectionLimit_lt_partial_of_re_lt_half
      hs him hre] with K hK
  exact sub_neg.mpr hK

end DkMath.RH.CFBRCProjection
