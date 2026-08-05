/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.Regularization.ForwardDifference

#print "file: DkMath.CFBRC.Regularization.NegativeInteger"

/-!
# Native CFBRC values at non-positive integers

The definitions in this file are finite.  No divergent series is assigned a
usual sum, and no theorem about the analytically continued Riemann zeta
function is used.
-/

namespace DkMath.CFBRC.Regularization

open scoped BigOperators

/--
Finite Euler--forward-difference value corresponding to `η(-m)`.

The range stops at `m` because all higher forward differences of `x^m`
vanish.
-/
def etaNegNatFiniteDifference (m : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (m + 1),
    eulerForwardWeight j * powerMomentForwardDifference m j

/--
Parity-normalized finite value corresponding to `ζ(-m)`.

This is a CFBRC-native definition; it does not refer to `riemannZeta`.
-/
def zetaNegNatFiniteDifference (m : ℕ) : ℚ :=
  etaNegNatFiniteDifference m / (1 - (2 : ℚ) ^ (m + 1))

@[simp] theorem etaNegNatFiniteDifference_zero :
    etaNegNatFiniteDifference 0 = 1 / 2 := by
  norm_num [etaNegNatFiniteDifference, eulerForwardWeight,
    powerMomentForwardDifference, Finset.sum_range_succ, fwdDiff,
    Function.iterate_succ_apply, Function.comp_apply]

@[simp] theorem etaNegNatFiniteDifference_one :
    etaNegNatFiniteDifference 1 = 1 / 4 := by
  norm_num [etaNegNatFiniteDifference, eulerForwardWeight,
    powerMomentForwardDifference, Finset.sum_range_succ, fwdDiff]

@[simp] theorem etaNegNatFiniteDifference_two :
    etaNegNatFiniteDifference 2 = 0 := by
  norm_num [etaNegNatFiniteDifference, eulerForwardWeight,
    powerMomentForwardDifference, Finset.sum_range_succ, fwdDiff]

@[simp] theorem etaNegNatFiniteDifference_three :
    etaNegNatFiniteDifference 3 = -1 / 8 := by
  norm_num [etaNegNatFiniteDifference, eulerForwardWeight,
    powerMomentForwardDifference, Finset.sum_range_succ, fwdDiff,
    Function.iterate_succ_apply, Function.comp_apply]

@[simp] theorem zetaNegNatFiniteDifference_zero :
    zetaNegNatFiniteDifference 0 = -1 / 2 := by
  norm_num [zetaNegNatFiniteDifference, etaNegNatFiniteDifference,
    eulerForwardWeight, powerMomentForwardDifference, Finset.sum_range_succ,
    fwdDiff]

@[simp] theorem zetaNegNatFiniteDifference_one :
    zetaNegNatFiniteDifference 1 = -1 / 12 := by
  norm_num [zetaNegNatFiniteDifference, etaNegNatFiniteDifference,
    eulerForwardWeight, powerMomentForwardDifference, Finset.sum_range_succ,
    fwdDiff]

@[simp] theorem zetaNegNatFiniteDifference_two :
    zetaNegNatFiniteDifference 2 = 0 := by
  norm_num [zetaNegNatFiniteDifference, etaNegNatFiniteDifference,
    eulerForwardWeight, powerMomentForwardDifference, Finset.sum_range_succ,
    fwdDiff]

@[simp] theorem zetaNegNatFiniteDifference_three :
    zetaNegNatFiniteDifference 3 = 1 / 120 := by
  norm_num [zetaNegNatFiniteDifference, etaNegNatFiniteDifference,
    eulerForwardWeight, powerMomentForwardDifference, Finset.sum_range_succ,
    fwdDiff]

/-- Audit 001 headline: the native finite kernel recovers `-1/12`. -/
theorem cfbrcNative_zeta_neg_one_eq_neg_one_div_twelve :
    zetaNegNatFiniteDifference 1 = -1 / 12 :=
  zetaNegNatFiniteDifference_one

end DkMath.CFBRC.Regularization
