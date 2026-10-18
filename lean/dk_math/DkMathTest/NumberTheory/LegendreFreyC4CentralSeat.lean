/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.FreyC4CentralSeat

#print "file: DkMathTest.NumberTheory.LegendreFreyC4CentralSeat"

/-!
# NOTE-006 §3 の境界を含む回帰

素数の中央席 Q₃=13 だけでなく、合成数 Q₄=21、素数冪 Q₁₈=7³ でも検査する。
q=3 の例外、n=0 の端点、16∣n の分母条件を別々に保つ。
非特異な剰余曲線の c₄ が0になる例を、本当の Weierstrass モデルで確認する。
-/

namespace LegendreFreyC4CentralSeatTest

open DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.Legendre.FreyC4CentralSeat
open DkMath.Lib.NumberTheory

-- 正規化の前後で16倍を落とす場所が異なる。
example : (curve 3).c₄ = 16 * 13 ∧ (rationalCurve 3).c₄ = 13 := by
  constructor
  · norm_num [curve_c4, centralSeat]
  · norm_num [rationalCurve_c4, centralSeat]

example (n : ℕ) : rationalCurve n = FreyGapCubic.normalizeChange •
    (curve n).map (Int.castRingHom ℚ) := rationalCurve_eq_change n

example : SquareCell 3 (centralSeat 3) := centralSeat_mem_squareCell (by decide)
example : (rationalCurve 3).IsElliptic := rationalCurve_isElliptic (by decide)

-- n=0 の中央席は平方区間の内部には入らず、曲線も零 Gap を持つ。
example : centralSeat 0 = 1 ∧ ¬ SquareCell 0 (centralSeat 0) ∧ (curve 0).Δ = 0 := by
  norm_num [centralSeat, SquareCell, curve_discriminant]

-- 合成数の場合も全ての条件付き接続が成立する。
example : centralSeat 4 = 21 ∧ ¬ (centralSeat 4).Prime ∧ 7 ∣ centralSeat 4 := by decide
example : (7 : ℤ) ∣ (curve 4).c₄ ∧ ¬ (7 : ℤ) ∣ (curve 4).Δ ∧ 7 % 3 = 1 := by
  have h := prime_bridge (q := 7) (n := 4) (by decide) (by decide)
  exact ⟨h.1, h.2.1, h.2.2.resolve_left (by decide)⟩

-- Q₄=21 の素因子7は上界4を越えるので旧支持に含まれない。3は含まれる。
example : 3 ∈ squareOffsetPrimeSupport 4 5 ∧ 7 ∉ squareOffsetPrimeSupport 4 5 := by
  norm_num [mem_squareOffsetPrimeSupport]

-- 同じ素因子が中央席を3回割っても判別式は割らない。平方自由性は仮定しない。
example : centralSeat 18 = 7 ^ 3 ∧ ¬ (7 : ℤ) ∣ (curve 18).Δ :=
  ⟨by decide, prime_not_dvd_discriminant (by decide) (by decide)⟩

-- 実際の剰余曲線では Δ≠0 と c₄=0 が両立する。
example : ((curve 4).map (Int.castRingHom (ZMod 7))).IsElliptic ∧
    ((curve 4).map (Int.castRingHom (ZMod 7))).c₄ = 0 :=
  ⟨reduction_isElliptic (by decide) (by decide), reduction_c4_eq_zero (by decide)⟩

-- 非例外の素因子では位数3。q=3 では同じ位数結論を使えない。
example : orderOf (4 : ZMod 7) = 3 := orderOf_eq_three (by decide) (by decide) (by decide)
example : 3 ∣ centralSeat 1 ∧ orderOf (1 : ZMod 3) = 1 ∧ 3 % 3 ≠ 1 := by
  norm_num [centralSeat]
example : ¬ (3 : ℤ) ∣ (curve 1).Δ := prime_not_dvd_discriminant (by decide) (by decide)
example : 13 ≡ 1 [MOD 3] := prime_modEq_one (n := 3) (by decide) (by decide) (by decide)

-- n=1 の有理数モデルの c₄=3 から、整係数性を推論できない。
example : ¬ FreyGapCubic.IntegralNormalization (1 : ℤ) 1 := by
  have h := integralNormalization_iff 1
  norm_num at h
  exact h

-- 16∣n の場合には、本当に整数モデルへ降ろした c₄=Qₙ を得る。
example : (FreyGapCubic.integral (16 : ℤ) 1).c₄ = 273 := by
  have h := integral_c4 16 (by norm_num)
  norm_num [centralSeat] at h
  exact h

end LegendreFreyC4CentralSeatTest
