/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaMirrorEndpointOuterNormalization

#print "file: DkMathTest.RH.CFBRCEtaMirrorEndpointStructuralRatio"

noncomputable section

namespace DkMathTest.RH.CFBRCEtaMirrorEndpointStructuralRatio

open DkMath.RH.CFBRCProjection

example (N : ℕ) (s : ℂ) :
    etaMirrorEndpointTotalStructuralShare N s = 1 := by
  exact etaMirrorEndpointTotalStructuralShare_eq_one N s

example (N : ℕ) (s : ℂ)
    (hOuter : etaMirrorEndpointOuterBig N s ≠ 0) :
    etaMirrorEndpointTotalStructuralShare N s =
      (etaMirrorEndpointCore N s + etaMirrorEndpointGapCore N s) /
        etaMirrorEndpointOuterBig N s := by
  exact etaMirrorEndpointTotalStructuralShare_eq_div_of_outer_ne N s hOuter

example (N : ℕ) (s : ℂ)
    (hOuter : etaMirrorEndpointOuterBig N s ≠ 0) :
    etaMirrorEndpointTotalStructuralShare N s =
      etaMirrorEndpointCoreShare N s + etaMirrorEndpointGapShare N s := by
  exact
    etaMirrorEndpointTotalStructuralShare_eq_coreShare_add_gapShare
      N s hOuter

end DkMathTest.RH.CFBRCEtaMirrorEndpointStructuralRatio
