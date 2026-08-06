/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelTailMonotonicity

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelTailMonotonicity"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelTailMonotonicity

open Filter Set
open scoped Topology
open DkMath.RH.CFBRCProjection

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re) :
    ∃ K0 : ℕ,
      StrictMonoOn
        (fun K : ℕ =>
          etaCriticalMirrorRotatedDefectProjectionPartial K s)
        (Ici K0) :=
  exists_etaCriticalMirrorRotatedDefectProjectionPartial_strictMonoOn_tail_of_half_lt_re
    hs him hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2) :
    ∃ K0 : ℕ,
      StrictAntiOn
        (fun K : ℕ =>
          etaCriticalMirrorRotatedDefectProjectionPartial K s)
        (Ici K0) :=
  exists_etaCriticalMirrorRotatedDefectProjectionPartial_strictAntiOn_tail_of_re_lt_half
    hs him hre

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    {N : ℕ} (hN : 0 < N) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRotatedDefectProjectionPartial K s <
        etaCriticalMirrorRotatedDefectProjectionPartial (K + N) s :=
  eventually_etaCriticalMirrorRotatedDefectProjectionPartial_lt_add_of_half_lt_re
    hs him hre hN

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    {N : ℕ} (hN : 0 < N) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorRotatedDefectProjectionPartial (K + N) s <
        etaCriticalMirrorRotatedDefectProjectionPartial K s :=
  eventually_etaCriticalMirrorRotatedDefectProjectionPartial_add_lt_of_re_lt_half
    hs him hre hN

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedAbelTailMonotonicity
