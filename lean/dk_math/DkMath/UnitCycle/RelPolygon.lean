/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- import Mathlib
import DkMath.UnitCycle.Core

#print "file: DkMath.UnitCycle.RelPolygon"

namespace DkMath.UnitCycle.RelPolygon

open DkMath.UnitCycle -- allow access to core names if needed

/-!
# 相対多角数（周回）最小モデル

## ねらい
- State に周回位置 `pos` とギャップ量 `val` を持たせる。
- 遷移 `T` を `pos := pos + 1; val := val + g(pos)` として定義する。
- 不変量 `I := val` を取り、総和版（Sum-of-increments）

  `I ((T^[k]) s) ≥ I s + ∑ i ∈ range k, g ((T^[i]) s)`

  が効くことを示す。
- 具体例：`pos = 9, k = 2` で `∑g = 6`（= 1 + 5）となり、
  `k = 2` に対して **余分に +4** が乗ることを確認する。

このモデルは「相対多角数そのもの」ではないが、
- 周回（pos の進行）
- 局所スパイク（特定位置で解像度/増分が跳ねる）

という構造だけを抽出した“最小実戦ユニット”である。
-/

/-
DkMath/UnitCycle/RelPolygon.lean

相対多角数（Relative Polygon）の「最小モデル」：
- State := (pos, val)
- g(pos) := if pos % 10 = 0 then 5 else 1   （局所スパイク）
- T := pos を 1 進め、val を g(pos) だけ増やす
- I := val

狙い：
- I(T s) ≥ I s + g(s) を示し、
- 既存の総和版（Sum-of-increments）
    I_iterate_ge_sum_g
  を適用して、
    I(T^[k] s) ≥ I s + Σ_{i < k} g(T^[i] s)
  を得る。

さらに具体例：
- pos = 9, k = 2 で Σg = 6（= 1 + 5）となり、
  k=2 に対して余分に +4 が乗ることを見せる。
-/

/-! ## 1) 最小 State -/

/-- 周回位置 `pos` と蓄積値 `val` を持つ最小状態 -/
structure RPState where
  pos : ℕ
  val : ℕ
deriving Repr

/-! ## 2) 局所スパイク増分 g(pos) -/

/-- 局所スパイク：pos が 10 の倍数なら 5、それ以外は 1 -/
def g (s : RPState) : ℕ :=
  if s.pos % 10 = 0 then 5 else 1

/-- 反復ステップ：pos を 1 進め、val を g(pos) だけ増やす -/
def T (s : RPState) : RPState :=
  { pos := s.pos + 1
    val := s.val + g s }

/-- ポテンシャル：今回は val をそのまま使う -/
def I (s : RPState) : ℕ := s.val

/-! ## 3) 基本補題：g ≥ 1 と I(T s) ≥ I s + g s -/

lemma hg : ∀ s : RPState, 1 ≤ g s := by
  intro s
  dsimp [g]
  split_ifs <;> decide

lemma hT : ∀ s : RPState, I (T s) ≥ I s + g s := by
  intro s
  -- I(T s) = s.val + g s
  simp [T, I]

/-!
## 4) 総和版の適用（コア定理に委譲）

Core 側に以下の形の定理がある前提：

theorem I_iterate_ge_sum_g
    (hT : ∀ s, I (T s) ≥ I s + g s) :
    ∀ k s, I (iterate T k s) ≥ I s + ∑ i ∈ Finset.range k, g (iterate T i s)

あるいは `Function.iterate` 記法で

∀ k s, I ((T^[k]) s) ≥ I s + ∑ i ∈ Finset.range k, g ((T^[i]) s)

実際の Core 実装に合わせて、下のどちらかを使う。
-/

/-- (A) iterate 版：Core が `iterate` を公開している場合 -/
theorem I_iterate_ge_sum
    (k : ℕ) (s : RPState) :
    I (iterate T k s) ≥ I s + ∑ i ∈ Finset.range k, g (iterate T i s) := by
  -- Core の総和版にそのまま委譲
  simpa [I, g] using (I_iterate_ge_sum_g (State := RPState) (T := T) (I := I) (g := g) hT k s)

/-- (B) Function.iterate 版：`T^[k] s` で書きたい場合の薄いラッパ -/
theorem I_iterate_ge_sum_fn
    (k : ℕ) (s : RPState) :
    I ((T^[k]) s) ≥ I s + ∑ i ∈ Finset.range k, g ((T^[i]) s) := by
  -- `Function.iterate` を iterate に橋渡しできるなら委譲。
  -- もし Core が `iterate` = `Function.iterate` の定義ならこのまま通る。
  -- そうでない場合、Core 側の iterate 記法に統一して使ってよい。
  simpa using (I_iterate_ge_sum (k := k) (s := s))

/-! ## 5) 具体例：pos=9, k=2 で Σg=6（余分に +4） -/

/-- 初期状態：pos=9, val=0 -/
def s0 : RPState := { pos := 9, val := 0 }

/-- 1ステップ目の g は 1（pos=9 は 10 の倍数でない） -/
lemma g_s0 : g s0 = 1 := by
  -- 9 % 10 = 9 なので if は false
  simp [s0, g]

/-- 2ステップ目の状態（T s0）は pos=10 になり、次の g は 5 -/
lemma g_Ts0 : g (T s0) = 5 := by
  -- T s0 の pos は 10, 10 % 10 = 0
  simp [T, s0, g]

/-- k=2 のとき、総和 Σ_{i<2} g(T^[i] s0) = g(s0)+g(T s0) = 1+5 = 6 -/
theorem sum_g_pos9_k2 :
    (∑ i ∈ Finset.range 2, g ((T^[i]) s0)) = 6 := by
  -- range 2 = {0,1}
  -- T^[0] s0 = s0, T^[1] s0 = T s0
  -- NOTE: This proof relies on `simp` expanding `Finset.sum` over `range 2`,
  -- unfolding the iterates `T^[i]` and evaluating the concrete arithmetic
  -- needed to conclude that the sum is `6`.
  simp [Finset.sum_range_succ, s0, T, g, Nat.add_comm]

/-- k=2 に対して Σg=6 なので、単純な +k (=2) より 4 大きい -/
theorem sum_g_pos9_k2_extra : (∑ i ∈ Finset.range 2, g ((T^[i]) s0)) = 2 + 4 := by
  -- 6 = 2 + 4
  simp [sum_g_pos9_k2]

/-- 総和版から、I(T^[2] s0) ≥ 6 を得る（I s0 = 0 のため） -/
theorem I_pos9_k2_ge_6 : I ((T^[2]) s0) ≥ 6 := by
  have h := I_iterate_ge_sum_fn (k := 2) (s := s0)
  -- I s0 = 0, Σg = 6 を代入
  simpa [I, s0, sum_g_pos9_k2] using h

end DkMath.UnitCycle.RelPolygon
