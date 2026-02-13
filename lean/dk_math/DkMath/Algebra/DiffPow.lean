/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

namespace DkMath.Algebra.DiffPow

open scoped BigOperators
open Finset

section CommRing

/-!
## 差の冪の因数分解（Difference of Powers Factorization）

本モジュールは、以下の重要な等式を扱う：

```
a^d - b^d = (a - b) * ∑_{i=0}^{d-1} a^(d-1-i) * b^i
```

この因数分解は多項式代数や宇宙式（Universe formula）の Body 項として使われることがある。

### 背景
- 可換環 `CommRing` で定義することで、減法が存在する最小限の構造で作業できる
- 必要に応じて整数環 `ℤ` などより具体的な環に特殊化することも可能
- この分解はニュートン差分公式や高次の多項式展開と関連がある
-/

/-- 差の冪の因数分解に出る和（Difference Power Sum）

定義：
```
diffPowSum a b d = ∑_{i=0}^{d-1} a^(d-1-i) * b^i
```

例：d=3 のとき
```
diffPowSum a b 3 = a^2 + a*b + b^2
```

この和は a^d - b^d を (a - b) で割った商として現れる。
つまり a^d - b^d = (a - b) * diffPowSum a b d が成り立つ。
-/
def diffPowSum {α : Type*} [CommRing α] (a b : α) (d : ℕ) : α :=
  ∑ i ∈ range d, a^(d - 1 - i) * b^i

/-- 差の冪和から定数項を引いた形（Difference Power Sum minus Constant Multiple）

等式：
```
diffPowSum a b d - d * b^(d-1) = ∑_{i=0}^{d-1} (a^(d-1-i) * b^i - b^(d-1))
```

解説：
- 左辺は diffPowSum からその最後の項 (i=d-1 のとき b^(d-1)) を定数倍したものを引く
- 右辺は各項から b^(d-1) を引いたものを和にしている
- この等式は線形性により自動的に成立する
-/
lemma diffPowSum_sub_const_mul {α : Type*} [CommRing α] (a b : α) (d : ℕ) :
    diffPowSum a b d - (d : α) * b ^ (d - 1) =
    ∑ i ∈ range d, (a ^ (d - 1 - i) * b ^ i - b ^ (d - 1)) := by
  -- expand the definition of diffPowSum and rewrite the constant sum
  unfold diffPowSum
  have : (d : α) * b ^ (d - 1) = ∑ i ∈ range d, b ^ (d - 1) := by
    simp [Finset.sum_const, Finset.card_range]
  rw [this]
  simp only [Finset.sum_sub_distrib]

/--
差の冪の因数分解（Main Theorem）

定理（Factorization of Difference of Powers）：
```
a^d - b^d = (a - b) * diffPowSum a b d
```

証明戦略：
1. 帰納法を使用する（d に関する強い帰納法）
2. ベースケース: d = 0 のとき自明
3. 帰納ステップ: d から d+1 への推移
   - (a-b) * a^d と b * (a^d - b^d) に分解
   - a^d の係数と b ^ i との積を再グループ化
   - 和の添え字シフト（sum_range_succ'）を利用

※ Mathlib の `Finset.sum_range_choose` や幾何級数関連の lemma との接点あり
-/
theorem pow_sub_pow_factor {α : Type*} [CommRing α] (a b : α) (d : ℕ) :
    a^d - b^d = (a - b) * diffPowSum a b d := by
  induction d with
  | zero =>
    simp [diffPowSum, range_zero, Finset.sum_empty]
  | succ d ih =>
    have eq1 : a^(d + 1) - b^(d + 1) = a * a^d - b * b^d := by ring
    rw [eq1]
    have eq2 : a * a^d - b * b^d = (a - b) * a^d + b * (a^d - b^d) := by ring
    rw [eq2, ih]
    have : diffPowSum a b (d + 1) = a^d + b * diffPowSum a b d := by
      unfold diffPowSum
      -- split the 0-th term and shift the rest (use sum_range_succ' to get f 0 + ∑ f (i+1))
      rw [Finset.sum_range_succ']
      -- show the tail sum equals b * the shifted sum
      have tail_eq : ∑ k ∈ range d, a ^ (d + 1 - 1 - (k + 1)) * b ^ (k + 1) =
                     b * ∑ i ∈ range d, a ^ (d - 1 - i) * b ^ i := by
        -- move the `b` inside the sum so `sum_congr` can match summands
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [add_tsub_cancel_right, pow_succ, Nat.sub_sub, Nat.add_comm]; ring
      rw [tail_eq]
      grind
    rw [this]
    grind

/-- 宇宙式の Body 項（Body Term of Universe Formula）

定義：
```
BodyPow x u d = (x + u)^d - u^d
```

意味：
- x と u の 2 つ変数と幾何のパラメータ d を持つ
- x+u を基数とし、u だけシフトした冪の差
- 宇宙論の局所モデル計算やテイラー展開に関連

この形は a^d - b^d で a = x+u, b = u と置いた特殊例である。
-/
def BodyPow {α : Type*} [CommRing α] (x u : α) (d : ℕ) : α :=
  (x + u)^d - u^d

/-- `BodyPow x u d` は差の冪として因数分解できる（Factorization of BodyPow）

定理（BodyPow Factor Theorem）:
```
BodyPow x u d = x * diffPowSum (x + u) u d
```

詳細な解説：
1. BodyPow x u d = (x + u)^d - u^d は a^d - b^d の形である
   （ここで a = x + u, b = u）

2. pow_sub_pow_factor により
   a^d - b^d = (a - b) * diffPowSum a b d

3. a - b = (x + u) - u = x に置換すると
   (x + u)^d - u^d = x * diffPowSum (x + u) u d

4. これは binomial expansion (x + u)^d の u によるシフトと見なせる

証明は d に関する帰納法で、各ステップで sum_range_succ' により
和の添え字を整理する。
-/
theorem BodyPow_factor {α : Type*} [CommRing α] (x u : α) (d : ℕ) :
    BodyPow x u d = x * diffPowSum (x + u) u d := by
  induction d with
  | zero =>
    simp [BodyPow, diffPowSum, range_zero, Finset.sum_empty]
  | succ d ih =>
    show BodyPow x u (d + 1) = x * diffPowSum (x + u) u (d + 1)
    simp only [BodyPow]
    have key : (x + u)^d - u^d = x * diffPowSum (x + u) u d := by
      have h := ih
      simp only [BodyPow] at h
      exact h
    have h : (x + u)^(d + 1) - u^(d + 1) =
        x * ((x + u) * diffPowSum (x + u) u d + u^d) := by
      have h1 : (x + u)^(d + 1) - u^(d + 1) =
          (x + u) * (x + u)^d - u * u^d := by ring
      have h2 : (x + u) * (x + u)^d - u * u^d =
          (x + u) * ((x + u)^d - u^d) + (x + u) * u^d - u * u^d := by ring
      have h3 : (x + u) * ((x + u)^d - u^d) + (x + u) * u^d - u * u^d =
          (x + u) * (x * diffPowSum (x + u) u d) + x * u^d := by
        rw [key]; ring
      have h4 : (x + u) * (x * diffPowSum (x + u) u d) + x * u^d =
          x * ((x + u) * diffPowSum (x + u) u d + u^d) := by ring
      rw [h1, h2, h3, h4]
    rw [h]
    unfold diffPowSum
    -- convert the RHS sum form and show the remaining tail equals u * diffPowSum ...
    -- use the `sum_range_succ'` variant to get f 0 + ∑ f (i+1), matching the index-shifted form
    rw [Finset.sum_range_succ']
    have tail_eq : ∑ i ∈ range d, (x + u) ^ (d + 1 - 1 - (i + 1)) * u ^ (i + 1) =
                   u * ∑ i ∈ range d, (x + u) ^ (d - 1 - i) * u ^ i := by
      -- move the `u` inside the sum so `sum_congr` can match summands
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [add_tsub_cancel_right, pow_succ, Nat.sub_sub, Nat.add_comm]; ring
    rw [tail_eq]
    simp only [add_tsub_cancel_right, tsub_zero, pow_zero, mul_one]
    rw [eq_add_of_sub_eq key]
    rw [diffPowSum]
    ring

end CommRing

section CommSemiring

-- CommRing ではなく CommSemiring 上で定義したい場合のバージョン
/-- 差の冪の因数分解に出る和 (Difference Power Sum) -/
def diffPowSum' {α : Type*} [CommSemiring α] (a b : α) (d : ℕ) : α :=
  ∑ i ∈ range d, a^(d - 1 - i) * b^i

/--
この定理は `CommSemiring` 上では "引き算 ( - )" が定義されないため直接表現できん。
したがって semiring レベルの和 `diffPowSum'` は保持しつつ、因数分解の主張は `CommRing` 上で成り立つ
という形にしておく。
-/
theorem pow_sub_pow_factor' {α : Type*} [CommRing α] (a b : α) (d : ℕ) :
    a^d - b^d = (a - b) * diffPowSum' a b d := by
  -- `diffPowSum'` は `diffPowSum` と同じ定義なので、既に証明済みの `pow_sub_pow_factor` を流用する
  simpa [diffPowSum, diffPowSum'] using pow_sub_pow_factor (a := a) (b := b) (d := d)

end CommSemiring

end DkMath.Algebra.DiffPow
