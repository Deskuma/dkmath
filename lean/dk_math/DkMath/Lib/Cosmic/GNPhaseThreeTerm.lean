/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GNSourceTransport

#print "file: DkMath.Lib.Cosmic.GNPhaseThreeTerm"

/-! # 同じ二端点の三位相関係

係数を固定した三つの線形 source の加法関係を扱う。
位相ごとの冪表示は明示的な入力であり、一因子の表示からは仮定しない。
-/

namespace DkMath.Lib.Cosmic

/-- 同じ gap と parameter を持つ三因子の有限恒等式。
位相の相異性や原始性は、この加法恒等式自体には不要。 -/
theorem phaseSource_three_term_relation {R : Type*} [CommRing R]
    (ξ η χ x u : R) :
    (η - χ) * phaseSource ξ x u + (χ - ξ) * phaseSource η x u +
      (ξ - η) * phaseSource χ x u = 0 := by
  unfold phaseSource
  ring

/-- 三つの冪表示を同時に代入する。同じ x,u と同じ三つの根を式全体で保持する。 -/
theorem phaseSource_pow_three_term_relation {R : Type*} [CommRing R]
    (ξ η χ x u a b c : R) (n : ℕ)
    (ha : phaseSource ξ x u = (ξ - 1) * a ^ n)
    (hb : phaseSource η x u = (η - 1) * b ^ n)
    (hc : phaseSource χ x u = (χ - 1) * c ^ n) :
    (η - χ) * (ξ - 1) * a ^ n + (χ - ξ) * (η - 1) * b ^ n +
      (ξ - η) * (χ - 1) * c ^ n = 0 := by
  simpa only [ha, hb, hc, mul_assoc] using phaseSource_three_term_relation ξ η χ x u

/-- 位相 ξ,ξ²,ξ³ の場合、共通因子 ξ*(ξ−1)² を除くと重み付き冪方程式になる。
係数 1+ξ+ξ² と (1+ξ)² が冪であるとは結論しない。 -/
theorem phaseSource_three_consecutive_power_relation {R : Type*} [CommRing R] [IsDomain R]
    (ξ x u a b c : R) (n : ℕ) (hξ : ξ ≠ 0) (hξ1 : ξ ≠ 1)
    (ha : phaseSource ξ x u = (ξ - 1) * a ^ n)
    (hb : phaseSource (ξ ^ 2) x u = (ξ ^ 2 - 1) * b ^ n)
    (hc : phaseSource (ξ ^ 3) x u = (ξ ^ 3 - 1) * c ^ n) :
    ξ * a ^ n + (1 + ξ + ξ ^ 2) * c ^ n = (1 + ξ) ^ 2 * b ^ n := by
  have ht := phaseSource_pow_three_term_relation ξ (ξ ^ 2) (ξ ^ 3) x u a b c n ha hb hc
  have hp : ξ * (ξ - 1) ^ 2 *
      (ξ * a ^ n + (1 + ξ + ξ ^ 2) * c ^ n - (1 + ξ) ^ 2 * b ^ n) = 0 := by
    linear_combination -ht
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left
    (mul_ne_zero hξ (pow_ne_zero _ (sub_ne_zero.mpr hξ1))))

end DkMath.Lib.Cosmic
