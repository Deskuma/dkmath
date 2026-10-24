/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

#print "file: DkMath.Lib.Algebra.SquareCompletion"

/-!
# 平方完成と有限個の単位層

[DkMath.Lib] GN-LIB-003b: `Gnomon.Algebra` の平方帯と
`Primitive.SquareBody` の端点恒等式から、carrierに依存しない一般核を抽出する。
旧定義をこのモジュールへ持ち込まず、式そのものを任意の可換半環で扱う。

平方の辺xへ厚さuを足すと、面積の増分は `u*(2*x+u)` となる。
二つの厚さu,vを順に足すと、後半の基点はx+uへ移る。
この平行移動を残した加法則が、有限帯を単位層へ分ける帰納法の核である。

有限和の層数は自然数nである。係数環の任意の元uを層数として列挙しない。
半環内ではnと添字iを自然数からcastする。減算・約分・正性・整域性は不要であり、
零因子や正標数を持つ環も含む。順序、素数性、平方の間の素数存在は結論しない。
-/

namespace DkMath.Lib.Algebra

open scoped BigOperators

/--
[DkMath.Lib] 昇格元: `Gnomon.square_add_squareGnomonBand`（A20）。
Natの旧carrierを除き、任意の可換半環へ一般化した平方完成。
旧APIはこの式のNat特殊化を呼び出す互換wrapperである。
-/
theorem square_add_band {R : Type*} [CommSemiring R] (x u : R) :
    x ^ 2 + u * (2 * x + u) = (x + u) ^ 2 := by
  ring

/--
[DkMath.Lib] 単位層の面積は2x+1。
旧 `Gnomon.square_add_oddGnomon` を一般半環の式として供給する。
自然数上の「奇数」という性質とは分け、ここでは多項式恒等式だけを述べる。
-/
theorem square_add_unit_layer {R : Type*} [CommSemiring R] (x : R) :
    x ^ 2 + (2 * x + 1) = (x + 1) ^ 2 := by
  simpa only [one_mul] using square_add_band x 1

/--
[DkMath.Lib] 昇格元: `Gnomon.squareGnomonBand_add`。
二つ目の帯は移動後の基点x+uから測る。同じ基点に固定した加法性ではない。
-/
theorem band_add_thickness {R : Type*} [CommSemiring R] (x u v : R) :
    (u + v) * (2 * x + (u + v)) =
      u * (2 * x + u) + v * (2 * (x + u) + v) := by
  ring

/--
[DkMath.Lib] 昇格元: `Gnomon.squareGnomonBand_eq_sum_shifted_oddGnomon`（A21）。
係数型を任意の可換半環へ一般化するが、層数nは自然数のまま保持する。
厚さ0は空和。後続では移動した単位層を一つ追加する。
-/
theorem band_eq_sum_unit_layers {R : Type*} [CommSemiring R] (x : R) (n : ℕ) :
    (n : R) * (2 * x + (n : R)) =
      ∑ i ∈ Finset.range n, (2 * (x + (i : R)) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, band_add_thickness, ih, Finset.sum_range_succ]
      simp only [one_mul]

/--
[DkMath.Lib] 有限帯を単位層へ分けたまま平方を完成する。
自然数差で面積増分を定義せず、全て加法恒等式として保持する。
-/
theorem square_add_sum_unit_layers {R : Type*} [CommSemiring R] (x : R) (n : ℕ) :
    x ^ 2 + (∑ i ∈ Finset.range n, (2 * (x + (i : R)) + 1)) =
      (x + (n : R)) ^ 2 := by
  rw [← band_eq_sum_unit_layers]
  exact square_add_band x (n : R)

/--
[DkMath.Lib] 昇格元: `Gnomon.sum_odd_eq_square`。
最初のn個の単位層を足す恒等式を一般半環へ運ぶ。正標数でも成立する。
-/
theorem sum_unit_layers_eq_square {R : Type*} [CommSemiring R] (n : ℕ) :
    (∑ i ∈ Finset.range n, (2 * (i : R) + 1)) = (n : R) ^ 2 := by
  simpa only [zero_add, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
    square_add_sum_unit_layers (0 : R) n

/--
[DkMath.Lib] 昇格元: `Primitive.squareBody_add_one_eq`（A23）。
旧squareBodyの内部式x²+2xへ1を補う一般恒等式。旧carrierはNat側に残す。
-/
theorem square_body_add_one {R : Type*} [CommSemiring R] (x : R) :
    (x ^ 2 + 2 * x) + 1 = (x + 1) ^ 2 := by
  simpa only [add_assoc] using square_add_unit_layer x

/-! 小さな教科書例。零厚さ、零基点、有限帯、負の座標を含む。 -/

example (x : ℕ) : x ^ 2 + 0 * (2 * x + 0) = (x + 0) ^ 2 :=
  square_add_band x 0

example : (0 : ℕ) ^ 2 + 4 * (2 * 0 + 4) = 4 ^ 2 :=
  square_add_band 0 4

example : (30 : ℕ) ^ 2 + 2 * (2 * 30 + 2) = 32 ^ 2 :=
  square_add_band 30 2

example : (2 : ℕ) * (2 * 30 + 2) = 61 + 63 := by decide

example : (-3 : ℤ) ^ 2 + 2 * (2 * (-3) + 2) = (-3 + 2) ^ 2 :=
  square_add_band (-3) 2

example : (∑ i ∈ Finset.range 0, (2 * (i : ℕ) + 1)) = 0 ^ 2 :=
  sum_unit_layers_eq_square 0

example : (∑ i ∈ Finset.range 4, (2 * (i : ℕ) + 1)) = 4 ^ 2 :=
  sum_unit_layers_eq_square 4

example : ((30 : ℕ) ^ 2 + 2 * 30) + 1 = 31 ^ 2 :=
  square_body_add_one 30

end DkMath.Lib.Algebra
