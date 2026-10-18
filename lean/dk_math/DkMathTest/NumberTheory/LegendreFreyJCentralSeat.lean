/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.FreyJCentralSeat

#print "file: DkMathTest.NumberTheory.LegendreFreyJCentralSeat"

/-! # NOTE-007 中央席 j の回帰例: 有理数の値と、例外素数3・旧支持内の7。 -/
namespace LegendreFreyJCentralSeatTest
open DkMath.NumberTheory.Legendre FreyC4CentralSeat

example : rationalJ 1 (by decide) = 1728 := by rw [rationalJ_eq]; norm_num [centralSeat]
example : rationalJ 2 (by decide) = 21952 / 9 := by rw [rationalJ_eq]; norm_num [centralSeat]
example : reductionJ 1 3 (by decide) (by decide) = 0 := reductionJ_eq_zero _ _
example : reductionJ 18 7 (by decide) (by decide) = 0 := reductionJ_eq_zero _ _
example (hs : 7 ∈ squareOffsetPrimeSupport 18 (18 + 1)) :
    ∃ (hq : Nat.Prime 7) (hd : 7 ∣ centralSeat 18),
      7 ≤ 18 ∧ reductionJ 18 7 hq hd = 0 ∧ (7 = 3 ∨ 7 % 3 = 1) :=
  j_bridge_of_mem_support hs
end LegendreFreyJCentralSeatTest
