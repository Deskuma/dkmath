/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaMirrorEndpointOuterNormalization

#print "file: DkMathTest.RH.CFBRCEtaMirrorEndpointOuterNormalization"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaMirrorEndpointOuterNormalization

open DkMath.RH.CFBRCProjection

example (N : ℕ) (s : ℂ) :
    etaMirrorEndpointOuterBig N s =
      etaMirrorEndpointCore N s + etaMirrorEndpointGapCore N s := by
  exact etaMirrorEndpointOuterBig_eq_core_add_gapCore N s

example (N : ℕ) (s : ℂ) :
    etaMirrorEndpointOuterBig N s =
      2 * etaMirrorEndpointTotalEnergy N s := by
  exact etaMirrorEndpointOuterBig_eq_two_mul_totalEnergy N s

example (N : ℕ) (s : ℂ)
    (hOuter : etaMirrorEndpointOuterBig N s ≠ 0) :
    etaMirrorEndpointCoreShare N s + etaMirrorEndpointGapShare N s = 1 := by
  exact etaMirrorEndpointCoreShare_add_gapShare N s hOuter

example (N : ℕ) {s : ℂ} (hre : s.re = (1 : ℝ) / 2) :
    etaMirrorEndpointGapCore N s = 0 ∧
      etaMirrorEndpointGapShare N s = 0 := by
  exact
    ⟨etaMirrorEndpointGapCore_eq_zero_of_re_eq_half N hre,
      etaMirrorEndpointGapShare_eq_zero_of_re_eq_half N hre⟩

example (N : ℕ) {s : ℂ} (hre : s.re = (1 : ℝ) / 2)
    (hOuter : etaMirrorEndpointOuterBig N s ≠ 0) :
    etaMirrorEndpointCoreShare N s = 1 := by
  exact etaMirrorEndpointCoreShare_eq_one_of_re_eq_half N hre hOuter

end DkMathTest.RH.CFBRCEtaMirrorEndpointOuterNormalization
