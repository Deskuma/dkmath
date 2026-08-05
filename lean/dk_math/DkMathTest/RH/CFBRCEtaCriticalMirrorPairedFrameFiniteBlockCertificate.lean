/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaCriticalMirrorPairedFrameFiniteBlockCertificate

#print "file: DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameFiniteBlockCertificate"

set_option linter.style.longLine false

noncomputable section

namespace DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameFiniteBlockCertificate

open Filter
open DkMath.RH.CFBRCProjection

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    (N : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j < N →
        0 < etaCriticalMirrorBlockStartDefectPairProjection s K j :=
  eventually_all_etaCriticalMirrorBlockStartDefectPairProjection_pos_on_range_of_half_lt_re
    hs him hre N

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    (N : ℕ) :
    ∀ᶠ K : ℕ in atTop,
      ∀ j : ℕ, j < N →
        etaCriticalMirrorBlockStartDefectPairProjection s K j < 0 :=
  eventually_all_etaCriticalMirrorBlockStartDefectPairProjection_neg_on_range_of_re_lt_half
    hs him hre N

example (s : ℂ) (K N : ℕ) :
    etaCriticalMirrorBlockStartDefectBlockProjection s K N =
      (Finset.range N).sum fun j : ℕ =>
        etaCriticalMirrorBlockStartDefectPairProjection s K j :=
  etaCriticalMirrorBlockStartDefectBlockProjection_eq_sum s K N

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : (1 : ℝ) / 2 < s.re)
    {N : ℕ} (hN : 0 < N) :
    ∀ᶠ K : ℕ in atTop,
      0 < etaCriticalMirrorBlockStartDefectBlockProjection s K N :=
  eventually_etaCriticalMirrorBlockStartDefectBlockProjection_pos_of_half_lt_re
    hs him hre hN

example
    {s : ℂ} (hs : NontrivialRiemannZetaZero s)
    (him : s.im ≠ 0) (hre : s.re < (1 : ℝ) / 2)
    {N : ℕ} (hN : 0 < N) :
    ∀ᶠ K : ℕ in atTop,
      etaCriticalMirrorBlockStartDefectBlockProjection s K N < 0 :=
  eventually_etaCriticalMirrorBlockStartDefectBlockProjection_neg_of_re_lt_half
    hs him hre hN

end DkMathTest.RH.CFBRCEtaCriticalMirrorPairedFrameFiniteBlockCertificate
