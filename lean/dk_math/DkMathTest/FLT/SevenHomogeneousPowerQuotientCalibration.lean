/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.HomogeneousPowerQuotient
import DkMath.FLT.Seven.SevenRealCubicAxisDrop

#print "file: DkMathTest.FLT.SevenHomogeneousPowerQuotientCalibration"

namespace DkMathTest.FLT.SevenHomogeneousPowerQuotientCalibration

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubicInt
open DkMath.Lib.NumberTheory

/-! The generic seven-step congruence reproduces the FLT7 core input on its
existing homogeneous quotient type. The FLT module is imported only by this
calibration test; the reusable library remains FLT-free. -/

example (x y : SevenRealCubicInt) :
    homogeneousPowerQuotient x y 7 = seventhQuotient x y := by
  simp [homogeneousPowerQuotient, DkMath.Algebra.DiffPow.diffPowSum,
    seventhQuotient, Finset.sum_range_succ]

example (x y : SevenRealCubicInt) :
    x - y ∣ homogeneousPowerQuotient x y 7 - (7 : SevenRealCubicInt) * y ^ 6 := by
  simpa using gap_dvd_homogeneous_sub_natCast_mul x y 7

example (x y : SevenRealCubicInt) :
    x ^ 7 - y ^ 7 =
      (x - y) * homogeneousPowerQuotient x y 7 := by
  exact pow_sub_pow_eq_gap_mul_homogeneous x y 7

end DkMathTest.FLT.SevenHomogeneousPowerQuotientCalibration
