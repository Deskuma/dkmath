/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.Regularization.DualAudit
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

#print "file: DkMath.CFBRC.Regularization.RiemannZetaOracleAudit"

/-!
# Standard-zeta oracle comparison

This module is deliberately quarantined from the native CFBRC proof.  It uses
Mathlib's analytically continued `riemannZeta` only to compare the already
computed native value with the standard special value.
-/

namespace DkMath.CFBRC.Regularization

/-- The native Audit 001 value agrees with Mathlib's standard `ζ(-1)`. -/
theorem cfbrcNative_zetaNegOne_eq_riemannZeta :
    ((zetaNegNatFiniteDifference 1 : ℚ) : ℂ) =
      riemannZeta (-(1 : ℂ)) := by
  have hz := riemannZeta_neg_nat_eq_bernoulli 1
  norm_num [bernoulli] at hz ⊢
  exact hz.symm

end DkMath.CFBRC.Regularization
