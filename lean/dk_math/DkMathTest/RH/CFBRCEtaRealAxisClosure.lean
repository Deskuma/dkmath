/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.StandardZetaRealAxisClosure

namespace DkMathTest.RH.CFBRCEtaRealAxisClosure

open DkMath.RH.CFBRCProjection
open DkMath.RH.Weave.Analytic

example {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    etaPairedValue (σ : ℂ) = analyticEta (σ : ℂ) := by
  exact etaPairedValue_eq_analyticEta_of_real_mem_Ioo_zero_one hσ0 hσ1

example {σ : ℝ} (hσ0 : 0 < σ) :
    0 < (etaPairedValue (σ : ℂ)).re := by
  exact etaPairedValue_re_pos_of_pos_real hσ0

example {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  exact riemannZeta_ne_zero_of_real_mem_openCriticalInterval hσ0 hσ1

example {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    s.im ≠ 0 := by
  exact nontrivialRiemannZetaZero_im_ne_zero hs

example : StandardZetaRealAxisClosure := by
  exact standardZetaRealAxisClosure

end DkMathTest.RH.CFBRCEtaRealAxisClosure
