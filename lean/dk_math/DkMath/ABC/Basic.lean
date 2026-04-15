/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.ABC.Basic"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.ABC.Basic

-- None

end DkMath.ABC.Basic



#check Real.rpow_nonneg

namespace Real

-- 非負数の累乗は非負であることを示すフック補題(AIが間違えて定義名を多用するので)
lemma rpow_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) (r : ℝ) : 0 ≤ x ^ r :=
  Real.rpow_nonneg hx r

end Real


-- ==========================================
-- ABC Basic Tool Lemmas
-- ==========================================

namespace ABC


-- ABC.Int
namespace Int

@[simp]
lemma cast_add_one (n : ℤ) : (n : ℝ) + 1 = (n + 1 : ℝ) := by rfl


@[simp]
lemma frac_nonneg_and_lt_one (x : ℝ) : 0 ≤ x - Int.floor x ∧ x - Int.floor x < 1 := by
  constructor
  · exact sub_nonneg_of_le (Int.floor_le x)
  · exact sub_lt_iff_lt_add'.mpr (Int.lt_floor_add_one x)


@[simp]
lemma le_floor_add_one (x : ℝ) : x ≤ Int.floor x + 1 := by
  -- 元の形を素朴に示す: x = (x - ⌊x⌋) + ⌊x⌋, かつ 0 ≤ x - ⌊x⌋ < 1
  have h := frac_nonneg_and_lt_one x
  have hx : x = (x - Int.floor x) + Int.floor x := by ring
  have : x < Int.floor x + 1 := by
    calc
      x = (x - Int.floor x) + Int.floor x := hx
      _ < 1 + Int.floor x := by
        have : x - Int.floor x < 1 := h.2; exact (add_lt_add_iff_right ↑⌊x⌋).mpr this
      _ = Int.floor x + 1 := by ring
  exact (le_of_lt this)


@[simp]
theorem ceil_eq_floor_add_one_of_not_int (x : ℝ) (h : x ≠ Int.floor x) : Int.ceil x = Int.floor x + 1 := by
  rw [Int.ceil_eq_iff]
  constructor
  · -- ↑(Int.floor x + 1) - 1 < x を示す
    have h_floor : Int.floor x ≤ x := Int.floor_le x
    -- ↑(Int.floor x + 1) - 1 = ↑(Int.floor x)
    have : ↑(⌊x⌋ + 1) - 1 = (Int.floor x : ℝ) := by
      simp only [Int.cast_add, Int.cast_one, add_sub_cancel_right]
    rw [this]
    -- Int.floor x < x は floor_le と x ≠ ↑⌊x⌋ から得る
    exact lt_of_le_of_ne h_floor (Ne.symm h)
  · -- x ≤ Int.floor x + 1 を示す
    -- Int.le_floor_add_one はすでに x ≤ ⌊x⌋ + 1（実数への自動キャストあり）を与えるのでそれを使う
    -- 目標の右辺は ↑(⌊x⌋ + 1) なので Int.cast_add_one を逆向きに rw して形を合わせる
    simp only [Int.cast_add, Int.cast_one, le_floor_add_one]


@[simp]
lemma ceil_eq_floor_add_one (x : ℝ) : Int.ceil x = if x = Int.floor x then Int.floor x else Int.floor x + 1 := by
  by_cases h : x = Int.floor x
  · rw [h]; simp
  · simp [h, ceil_eq_floor_add_one_of_not_int x h]


@[simp]
lemma floor_le_add_one (x : ℝ) : Int.floor x ≤ Int.ceil x := by
  rw [ceil_eq_floor_add_one x]
  split_ifs with h
  · -- x が整数のとき: ⌈x⌉ = ⌊x⌋
    -- 目標 ⌊x⌋ ≤ ⌊x⌋ は自明
    exact le_rfl
  · -- それ以外: ⌈x⌉ = ⌊x⌋ + 1 なので ⌊x⌋ ≤ ⌊x⌋ + 1 は加法の単調性
    exact le_add_of_nonneg_right (by decide : (0:ℤ) ≤ 1)


@[simp]
lemma ceil_le_add_one (x : ℝ) : (Int.ceil x : ℝ) ≤ x + 1 := by
  -- Int.lt_floor_add_one (x + 1) は x + 1 < ↑⌊x + 1⌋ + 1 なので、x < ↑⌊x + 1⌋ を得るには 1 を引いて使うのじゃ
  have h : x < ↑⌊x + 1⌋ := by
    -- x + 1 < ↑⌊x + 1⌋ + 1 より x < ↑⌊x + 1⌋
    linarith [Int.lt_floor_add_one (x + 1)]
  have h' : Int.ceil x ≤ ⌊x + 1⌋ := Int.ceil_le.mpr (le_of_lt h)
  -- ⌊x + 1⌋ ≤ x + 1 なので (Int.ceil x : ℝ) ≤ x + 1 となる
  exact le_trans (Int.cast_le.mpr h') (Int.floor_le (x + 1))

-- #check cast_add_one
-- #check frac_nonneg_and_lt_one
-- #check le_floor_add_one
-- #check ceil_eq_floor_add_one_of_not_int
-- #check ceil_eq_floor_add_one
-- #check floor_le_add_one
-- #check ceil_le_add_one

end Int



-- ABC.Nat
namespace Nat

/--
y が非負の実数のときの Nat.ceil に関する基本的な性質を示す補題。

主張：
  (Nat.ceil y - 1 : ℝ) < y ∧ y ≤ Nat.ceil y

意味：
  - Nat.ceil y は y 以上の最小の自然数であり（上界性）、
  - そのひとつ下の整数を実数にキャストしたものは y より小さい（厳密不等式）、
  ということを表す。

用途：
  切り上げ（ceil）に関する不等式を扱うときに用いる。特に、実数から自然数への切り上げに伴う上下界の扱いや、離散化・整数近似に関する証明で有用。

備考：
  - 記法 (Nat.ceil y - 1 : ℝ) は Nat.ceil y から 1 を引いた自然数を実数にキャストしたものを指す。
  - 仮定 `hy : 0 ≤ y` はキャストや関連する比較での取り扱いを簡単にするために置かれている。
-/
@[simp]
lemma ceil_spec (y : ℝ) (hy : 0 ≤ y) : (Nat.ceil y - 1 : ℝ) < y ∧ y ≤ Nat.ceil y := by
  constructor
  · -- show (↑⌈y⌉ - 1) < y
    set n := Nat.ceil y
    by_cases hn0 : n = 0
    · -- n = 0: then y ≤ 0, but hy : 0 ≤ y so y = 0, and -1 < 0 = y holds
      have hle : y ≤ (n : ℝ) := Nat.le_ceil y
      have : y ≤ 0 := by simpa [hn0] using hle
      have hy0 : y = 0 := le_antisymm this hy
      have : (n : ℝ) - 1 = (-1 : ℝ) := by simp [hn0]
      rw [hy0, this]; linarith
    · -- n ≥ 1: rewrite ↑n - 1 = ↑(n - 1) and use minimality of ceil
      have hnne : n ≠ 0 := hn0
      have hnpos : 0 < n := Nat.pos_of_ne_zero hnne
      have hn1 : 1 ≤ n := Nat.one_le_of_lt hnpos
      have : (n : ℝ) - 1 = (n - 1 : ℝ) := by norm_cast;
      rw [this]
      by_contra hneg  -- assume ¬(↑(n - 1) < y)
      have hle : y ≤ (n - 1 : ℝ) := (not_lt).mp hneg
      have hceil_le : Nat.ceil y ≤ n - 1 := (Nat.ceil_le).mpr (by exact_mod_cast hle)
      -- but Nat.ceil y = n by definition of n, so n ≤ n - 1, contradiction
      have hn_eq : Nat.ceil y = n := rfl
      have hle : n ≤ n - 1 := by rwa [←hn_eq] at hceil_le
      -- n = (n - 1).succ なので型を合わせて矛盾を導くのじゃ
      have hn_succ : n = (n - 1).succ := Eq.symm (Nat.succ_pred_eq_of_pos hnpos)
      rw [hn_succ] at hle
      exact absurd hle (Nat.not_succ_le_self (n - 1))
  · -- right inequality: y ≤ ⌈y⌉
    exact Nat.le_ceil y

/--
0 より大きい自然数は 0 ではないことを表す補題。

引数:
- `n : ℕ` — 自然数
- `hn : 0 < n` — `n` が正であるという仮定

説明:
`0 < n` という仮定から `n ≠ 0` を導く簡単な事実を記述する補題です。補題は証明や簡約（`simp`）に便利な形で利用されます。
-/
@[simp]
lemma ne_zero_of_gt {n : ℕ} (hn : 0 < n) : n ≠ 0 := by
  intro h; rw [h] at hn; exact Nat.not_lt_zero 0 hn

/--
自然数 n に対して、0 ≤ n かつ n ≠ 0 ならば 0 < n であることを示す補助補題。

説明:
- ℕ においては 0 ≤ n はしばしば自明だが、本補題は仮定 hn : 0 ≤ n と hne : n ≠ 0 から
  厳密な不等式 0 < n を得るために使える。
- 直感的には、n が 0 でなくかつ非負であれば n ≥ 1 となり、それは 0 < n を意味する。

用途:
- 他の定理や補題の証明中に、n がゼロでないことと非負であることから正であることを結論付けたい場面で使用する。

備考:
- 名前 zero_lt_of_le は「0 からの下界(≤)と非零性から 0 < n を導く」ことを表している。
-/
@[simp]
lemma zero_lt_of_le {n : ℕ} (hn : 0 ≤ n) (hne : n ≠ 0) : 0 < n := by
  match n with
  | 0 =>
    exfalso; exact hne rfl
  | Nat.succ n' =>
    exact Nat.succ_pos n'

/--
n ≠ 0 ならば n + 1 は正であることを示す補題。

自然数の後者 (successor) は常に 0 より大きいことを表し、`simp` タグが付与されているため
不等式 `0 < n + 1` を自動簡約するときに利用されることを意図している。

例:
  -- `hn : n ≠ 0` があるとき
  have h : 0 < n + 1 := succ_pos_of_ne_zero hn
-/
@[simp]
lemma succ_pos_of_ne_zero {n : ℕ} (_ : n ≠ 0) : 0 < n + 1 := by
  exact zero_lt_of_le (Nat.zero_le (n + 1)) (Nat.succ_ne_zero n)

-- #check ceil_spec
-- #check ne_zero_of_gt
-- #check zero_lt_of_le
-- #check succ_pos_of_ne_zero

/--
`log2_spec` は、自然数 `n`（`1 ≤ n`）に対して `Nat.log 2 n` が
n の二進対数の床（floor(log₂ n)）として振る舞うことを述べる補題です。

具体的には次の不等式を与えます：
  2^(Nat.log 2 n) ≤ n < 2^(Nat.log 2 n + 1)

引数:
  - `n` : 対象の自然数
  - `hn` : `1 ≤ n`（`n = 0` の場合を除外するための仮定）

用途:
  - `n` のビット長や指数に関する下界・上界の推定
  - 二分探索や対数に基づく複雑さ解析での不等式の根拠づけ

関連:
  - `Nat.log` の基本性質や `pow` に関する補題と併せて使うと便利です。
-/
@[simp]
theorem log2_spec {n : ℕ} (hn : 1 ≤ n) : (2:ℕ)^(Nat.log 2 n) ≤ n ∧ n < (2:ℕ)^(Nat.log 2 n + 1) := by
  -- 2^(log 2 n) ≤ n は pow_log_le_self から
  have hleft : (2:ℕ)^(Nat.log 2 n) ≤ n := by
    have hne : n ≠ 0 := Nat.ne_of_gt hn
    simpa using (Nat.pow_log_le_self (2) hne)
  -- n < 2^(log 2 n + 1) は lt_pow_succ_log_self (b=2) から (succ 形と +1 の同一視)
  have hright : n < (2:ℕ)^(Nat.log 2 n + 1) := by
    -- Nat.lt_pow_succ_log_self は指数に .succ 形で出るので書き換え
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (b := 2) (by decide : 1 < (2:ℕ)) n
  exact ⟨hleft, hright⟩


/--
n ≥ 1 のとき、2 を底とする対数の床 Nat.log 2 n に対して
2^(Nat.log 2 n) ≤ n < 2^(Nat.log 2 n + 1) が成り立ちます。
本定理はそのうち右側の不等号 n < 2^(Nat.log 2 n + 1) を主張します。

引数:
- n : ℕ — 自然数
- 仮定: 1 ≤ n

説明:
Nat.log 2 n は n の二進対数の床に相当するため、
2^k ≤ n < 2^(k+1) を満たす最大の k が Nat.log 2 n です。
この補題はその性質から直接得られる不等式を述べています。

利用例:
- n の桁数や指数に関する評価を行う際に使えます。
- 証明では Nat.log の定義と冪の単純な性質を用います。
-/
@[simp]
theorem lt_pow_succ_log2_of_one_le' {n : ℕ} (_ : 1 ≤ n) : n < (2:ℕ)^(Nat.log 2 n + 1) := by
  -- Nat.lt_pow_succ_log_self を基に b = 2 を指定して直接適用する。 -/
  exact Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n

@[simp]
lemma lt_pow_succ_log2_of_one_le {n : ℕ} (hn : 1 ≤ n) : n < (2:ℕ)^(Nat.log 2 n + 1) := (log2_spec hn).2


/--
n ≥ 1 のとき 2^(Nat.log 2 n) ≤ n を主張する補題。

Nat.log 2 n は 2 を底とする対数の床（すなわち最大の k で 2^k ≤ n を満たす）として定義されるため、
この不等式は本質的に自明である。証明では `Nat.log_eq_iff` を用い、仮定 `hn : 1 ≤ n` から `n ≠ 0` を導出している。
-/
@[simp]
lemma pow_log2_le_self' {n : ℕ} (hn : 1 ≤ n) : (2:ℕ)^(Nat.log 2 n) ≤ n :=
  -- Nat.log_eq_iff の仮定 n ≠ 0 を hn から導くのじゃ -/
  (Nat.log_eq_iff (Or.inr ⟨by norm_num, Nat.ne_of_gt hn⟩)).mp rfl |>.left

@[simp]
lemma pow_log2_le_self {n : ℕ} (hn : 1 ≤ n) : (2:ℕ)^(Nat.log 2 n) ≤ n := (log2_spec hn).1



/--
n ≥ 1 のときに 2^(Nat.log 2 n) ≤ n が成り立つことを示す補助補題。

`Nat.log` は基底 2 の対数の床を返すため、この主張は
「⌊log₂ n⌋ に対して 2^⌊log₂ n⌋ ≤ n」が成り立つことを表します。
引数 `hn : 1 ≤ n` は特に n ≠ 0 を含意するため、`Nat.log_eq_iff` の仮定を満たします。

パラメータ:
- `n` : 自然数
- `hn` : 1 ≤ n（n が 0 でないことを保証）

証明の概要:
`Nat.log_eq_iff` を用いて log の定義に基づく不等式を導出します。

関連:
- 底が 0 または 1 の場合は単調性が異なるので注意。
- 一般の順序体や半環でのべき乗の単調性に関する補題とも対応する結果である。
-/
@[simp]
lemma pow_lt_pow_of_lt_right {a m n : ℕ} (ha : 2 ≤ a) (hmn : m < n) : a ^ m < a ^ n := by
  -- a ≥ 2 なら pow は単調増加なので、m < n なら a^m < a^n となるのじゃ -/
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hmn
  -- まず a^m < a^(m+1) を示す
  have h1 : 1 < a := Nat.lt_of_succ_le ha
  -- 0 < a は 0 < 1 と 1 < a から得る -/
  have hpow_pos : 0 < a ^ m := Nat.pow_pos (lt_trans (by norm_num : 0 < 1) h1)
  have hstep : a ^ m < a ^ (m + 1) := by
    calc
      a ^ m = a ^ m * 1 := by rw [Nat.mul_one]
      _ < a ^ m * a := Nat.mul_lt_mul_of_pos_left h1 hpow_pos
      _ = a ^ (m + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  -- n = m + (k + 1) なので a^n = a^(m+1+k) であり a^(m+1) ≤ a^n を得る
  have hpow_le : a ^ (m + 1) ≤ a ^ (m + k + 1) :=
    Nat.pow_le_pow_of_le ha (by rw [add_right_comm]; exact Nat.le_add_right (m + 1) k)
  exact lt_of_lt_of_le hstep hpow_le

/--
a ≥ 2 のとき、自然数における冪乗は指数に関して単調増加することを表す補題。

具体的には、基数 a が 2 以上であれば
a^m ≤ a^n が成り立つことと m ≤ n であることは同値である。

直感的には a ≥ 2 により a^k は k の増加に伴って増加するためであり、
証明は差 n - m による帰納法や、a の各乗間の比が 1 より大きいことを利用して示せる。

引数:
- a : ℕ — 基数（仮定 ha : 2 ≤ a）
- m, n : ℕ — 指数

用途: 冪乗に関する単調性を必要とする不等式の変形や比較に用いる。
-/
@[simp]
lemma pow_le_pow_left_iff {a m n : ℕ} (ha : 2 ≤ a) : a ^ m ≤ a ^ n ↔ m ≤ n := by
  constructor
  · -- 左から右: a^m ≤ a^n → m ≤ n
    intro h
    -- pow の単調性（a ≥ 2 なら a^m ≤ a^n ↔ m ≤ n）は Mathlib には直接ないので、contrapositive で証明するのじゃ -/
    contrapose! h
    -- m > n なら a^m > a^n となる（a ≥ 2 なら pow は単調増加）
    have hmn : n < m := h
    have hpow : a ^ n < a ^ m := Nat.pow_lt_pow_of_lt_right ha hmn
    exact hpow
  · -- 右から左: m ≤ n → a^m ≤ a^n
    intro h
    exact Nat.pow_le_pow_of_le ha h

/--
底 a が 2 以上の自然数のとき、べき乗 a^m は指数 m に関して厳密に単調増加することを表す補題。

命題: 任意の自然数 a, m, n に対して 2 ≤ a のとき
  a ^ m < a ^ n ↔ m < n

意味と証明方針:
- 直感的には、底が 2 以上であれば a を何回か掛け合わせる回数が増えれば値は単調に増加する。
- 左から右 (a^m < a^n → m < n) は対偶を取ることで扱いやすくなる。対偶は「m ≥ n なら a^m ≥ a^n」であり、これは補題 Nat.pow_le_pow_of_le（底が 2 以上のとき指数に関してべき乗は単調増加）を使って示せる。
- 右から左 (m < n → a^m < a^n) は直接的に Nat.pow_lt_pow_of_lt_right（底が 2 以上のとき指数増加に対してべき乗は厳密増加）を適用して示す。

注意:
- a = 0 や a = 1 の場合は挙動が異なる（特に a = 1 では全てのべきが等しい）ため、仮定 2 ≤ a が必要である。
- 証明で利用する補題: Nat.pow_le_pow_of_le, Nat.pow_lt_pow_of_lt_right。
- 記号と仮定は全て自然数 ℕ に属するものである。
- この補題は指数比較をべき乗比較に還元／逆にべき乗比較から指数比較を導く際に便利である。
- 例: a = 2 のときは 2^m < 2^n ⇔ m < n が成り立つ。
-/
lemma pow_lt_pow_left_iff {a m n : ℕ} (ha : 2 ≤ a) : a ^ m < a ^ n ↔ m < n := by
  constructor
  · -- 左から右: a^m < a^n → m < n
    intro h
    contrapose! h
    -- m ≥ n なら a^m ≥ a^n となる（a ≥ 2 なら pow は単調増加）
    have hmn : n ≤ m := h
    have hpow : a ^ n ≤ a ^ m := Nat.pow_le_pow_of_le ha hmn
    exact hpow
  · -- 右から左: m < n → a^m < a^n
    intro h
    exact Nat.pow_lt_pow_of_lt_right ha h

/--
a ≥ 2 かつ m ≤ n のとき、自然数におけるべき乗は指数に関して単調増加であり、a ^ m ≤ a ^ n が成り立つことを示す補題。

引数:
- `ha` : 2 ≤ a （底が少なくとも 2）
- `hmn`: m ≤ n （指数の大小関係）

証明は `pow_le_pow_left_iff` を用いて行われる。
-/
@[simp]
lemma pow_le_pow {a m n : ℕ} (ha : 2 ≤ a) (hmn : m ≤ n) : a ^ m ≤ a ^ n :=
  (pow_le_pow_left_iff ha).mpr hmn

/--
b ≥ 2 かつ 1 ≤ n のもとで、m ≤ n ならば Nat.log b m ≤ Nat.log b n が成り立つことを主張します。
Nat.log は底 b に関する自然数の対数（切り下げ）を返すので、この補題は「対数は第二引数について単調増加（非減少）である」ことを述べています。
条件 b ≥ 2 は対数の底として意味を持たせるため、1 ≤ n は 0 の扱い（対数が 0 になる特殊ケースなど）を避けるために必要です。

証明の方針: ある k に対して b^k ≤ m が成り立てば同じ k について b^k ≤ n も成り立つため、m に対する最大の k（すなわち Nat.log b m）は n に対する最大の k を超え得ない、という単純な指数に関する単調性に基づきます。

用途: 基数 b における桁数の比較や、自然数のサイズ推定に利用されます。
-/
@[simp]
lemma log_le_log_of_le {b m n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) (h : m ≤ n) : Nat.log b m ≤ Nat.log b n := by
  -- handle the trivial case m = 0 separately
  by_cases hm0 : m = 0
  · -- m = 0: Nat.log b 0 = 0 so 0 ≤ Nat.log b n holds -/
    rw [hm0, Nat.log_zero_right b]
    exact Nat.zero_le (Nat.log b n)
  · -- m ≠ 0 so 1 ≤ m -/
    have hm1 : 1 ≤ m := Nat.one_le_of_lt (Nat.pos_of_ne_zero hm0)
    have hn1 : 1 ≤ n := hn
    have hpow_m : b^(Nat.log b m) ≤ m := (Nat.log_eq_iff (Or.inr ⟨by linarith [hb], Nat.ne_of_gt hm1⟩)).mp rfl |>.left
    have hpow_n' : n < b^(Nat.log b n + 1) := (Nat.log_eq_iff (Or.inr ⟨hb, Nat.ne_of_gt hn1⟩)).mp rfl |>.right
    -- assume the contrary and derive a contradiction
    by_contra hneg
    -- hneg : ¬ (Nat.log b m ≤ Nat.log b n) なので Nat.log b n < Nat.log b m となるのじゃ -/
    have hlt : Nat.log b n < Nat.log b m := lt_of_not_ge hneg
    have : Nat.log b n + 1 ≤ Nat.log b m := Nat.succ_le_of_lt hlt
    -- raise both sides to a power and use hpow_m and m ≤ n to contradict n < b^(Nat.log b n + 1)
    have : b^(Nat.log b n + 1) ≤ b^(Nat.log b m) := Nat.pow_le_pow_of_le hb this
    have : b^(Nat.log b n + 1) ≤ m := le_trans this hpow_m
    have : b^(Nat.log b n + 1) ≤ n := le_trans this h
    linarith [hpow_n']
  -- TODO: replace the above linarith with a direct contradiction using inequalities

-- log2 ⇔ log 2 の変換を行う補題を定義する -/
-- #check log2_eq_log_two -- 存在する
-- ⊢ ∀ {n : ℕ}, n.log2 = log 2 n
-- Nat.log2_eq_log_two {n : ℕ} : n.log2 = log 2 n

/--
m, n : ℕ に対して、Nat.log 2 m ≤ Nat.log 2 n という仮定から同じ不等式を得る補助補題。

この補題は仮定をそのまま返すだけの恒等的なものなので、主に
rewrite や明示的な仮定の名前付け・伝搬のために用います。

引数:
- m, n : 自然数
- h : Nat.log 2 m ≤ Nat.log 2 n

結果: Nat.log 2 m ≤ Nat.log 2 n

備考: Nat.log b n は底 b に対する整数対数（切り捨て）を返します。本補題は底 2 の場合に限定しています。
-/
@[simp]
lemma log2_le_log2_of_log_le_log {m n : ℕ} (h : Nat.log 2 m ≤ Nat.log 2 n) : Nat.log 2 m ≤ Nat.log 2 n := by
  -- 2^log2 m ≤ 2^log2 n なら pow の単調性から log2 m ≤ log2 n を得るのじゃ -/
  have ha : 2 ≤ 2 := by norm_num
  have hpow : (2 : ℕ) ^ Nat.log 2 m ≤ (2 : ℕ) ^ Nat.log 2 n := Nat.pow_le_pow_of_le ha h
  exact (Nat.pow_le_pow_left_iff ha).mp hpow

/--
自然数 `n` に対して、二進対数の特殊化 `Nat.log2 n` が
一般の対数関数 `Nat.log 2 n` と一致することを主張する補題です。

説明:
- `Nat.log2` は底 2 に固定された二進対数（整数部、つまり床）を表す便利な定義です。
- `Nat.log b n` は任意の底 `b` に対する対数を定義します。
- 本補題はこれら二つの定義が底 `2` の場合に同じ値を返すことを保証します。

証明の方針:
- 定義を展開し、`n = 0` と `n > 0` の場合に分けて議論することで示せます。
- 実際には `Nat.log2` の定義は `Nat.log 2` のエイリアスになっているか、同値な再帰的定義から導けます。

用途:
- 二進対数と一般対数を相互に置き換える際に使えます。
- 二進法に基づくアルゴリズムの解析で `Nat.log` の性質を流用したいときに便利です。
- 証明の簡略化のために、底が 2 の場合は `Nat.log2` と `Nat.log 2` を自由に交換できます。
-/
@[simp]
lemma log2_eq_log (n : ℕ) : Nat.log2 n = Nat.log 2 n := by
  -- handle the trivial n = 0 case separately
  by_cases hn0 : n = 0
  · rw [hn0]; simp
  -- now n ≠ 0, so 1 ≤ n -/
  have hn1 : 1 ≤ n := Nat.one_le_of_lt (Nat.pos_of_ne_zero hn0)
  -- use log2_spec to get the characterization of Nat.log 2 n, then apply Nat.log_eq_iff -/
  have hspec := log2_spec hn1
  -- hspec : 2^(Nat.log 2 n) ≤ n ∧ n < 2^(Nat.log 2 n + 1)
  -- 型変換: Nat.log2 n = Nat.log 2 n なので、hspec の両辺を congrArg で log2 に変換するのじゃ -/
  have hlog2_eq : Nat.log2 n = Nat.log 2 n := Nat.log2_eq_log_two
  have hspec_log2 : 2 ^ Nat.log2 n ≤ n ∧ n < 2 ^ (Nat.log2 n + 1) :=
    by rw [hlog2_eq]; exact hspec
  -- Nat.log_eq_iff で Nat.log 2 n = Nat.log2 n を導く
  have hlog : Nat.log 2 n = Nat.log2 n :=
    ((Nat.log_eq_iff (Or.inr ⟨by norm_num, Nat.ne_of_gt hn1⟩)).mpr hspec_log2)
  exact hlog.symm

/--
Nat.log2 の単調性。

任意の自然数 m, n に対して m ≤ n ならば Nat.log2 m ≤ Nat.log2 n が成り立つ。
直感的には Nat.log2 n は n を超えない最大の 2 の冪の指数（2^k ≤ n となる最大の k）のように振る舞うため、
m ≤ n のとき m に対して成立する指数の不等式は n に対しても成立し、その結果として対応する log2 の値は増加しない。
形式的には「2^k ≤ m ならば 2^k ≤ n」であることを使うか、べき乗に関する単調性補題（例えば Nat.pow_le_pow_of_le_right 等）を利用して証明する。
0 を含む境界条件も定義に従って扱える。
-/
@[simp]
lemma monotone_log2 : Monotone Nat.log2 := by
  intro a b h
  -- handle the trivial a = 0 case -/
  by_cases ha0 : a = 0
  · rw [ha0]; simp
  -- now a ≠ 0, so 1 ≤ a -/
  have ha_pos : 0 < a := zero_lt_of_le (Nat.zero_le a) ha0
  have ha1 : 1 ≤ a := Nat.one_le_of_lt ha_pos
  -- from a ≤ b we get 1 ≤ b -/
  have hb1 : 1 ≤ b := Nat.le_trans ha1 h
  -- use the global log2_spec for a and b -/
  have ha_spec := log2_spec (n := a) ha1
  have hb_spec := log2_spec (n := b) hb1
  -- 2^(log2 a) ≤ a ≤ b < 2^(log2 b + 1) so 2^(log2 a) ≤ 2^(log2 b + 1) -/
  have hpow_le : (2 : ℕ) ^ (Nat.log 2 a) ≤ (2 : ℕ) ^ (Nat.log 2 b + 1) := by
    -- まず 2^(log2 a) ≤ a ≤ b から 2^(log2 a) ≤ b を得る
    have h_le_b : (2 : ℕ) ^ (Nat.log 2 a) ≤ b := le_trans ha_spec.1 h
    -- 次に b < 2^(log2 b + 1) を用いて b ≤ 2^(log2 b + 1) とし、連鎖して目的の不等式を得る
    exact le_trans h_le_b (le_of_lt hb_spec.2)
    -- pow の単調性から log2 a ≤ log2 b + 1 を導くのじゃ -/
  have hnm1 : Nat.log 2 a ≤ Nat.log 2 b + 1 :=
    (Nat.pow_le_pow_left_iff (by norm_num)).mp hpow_le
  -- 2 ≤ 2 なので pow の単調性が使える
  -- hpow_le : (2 : ℕ) ^ (Nat.log 2 a) ≤ (2 : ℕ) ^ (Nat.log 2 b + 1)
  -- よって Nat.log 2 a ≤ Nat.log 2 b + 1
  match Nat.le_or_eq_of_le_succ hnm1 with
  | .inl hnm =>
    -- Nat.log2 n = Nat.log 2 n なので型を合わせるために congrArg で変換するのじゃ -/
    have hlog2_eq : Nat.log2 a = Nat.log 2 a := Nat.log2_eq_log a
    have hlog2_eq' : Nat.log2 b = Nat.log 2 b := Nat.log2_eq_log b
    rw [hlog2_eq, hlog2_eq']
    exact log2_le_log2_of_log_le_log hnm
  | .inr hnm_eq =>
    exfalso
    -- rewrite 2^(log2 a) into 2^(log2 b + 1) using the equality of exponents
    have hpow_eq := congrArg (fun k => (2 : ℕ) ^ k) hnm_eq
    let ha_pow := ha_spec.1
    rw [hnm_eq] at ha_pow
    -- from 2^(log2 b + 1) ≤ a and a ≤ b we get 2^(log2 b + 1) ≤ b, contradicting b < 2^(log2 b + 1)
    have hpow_le' : (2 : ℕ) ^ (Nat.log 2 b + 1) ≤ b := le_trans ha_pow h
    linarith [hpow_le', hb_spec.2]
  -- TODO: simplify to direct lt/le chain without linarith

/--
n ≥ 1 かつ n ≤ X のとき、2 を底とする対数のフロア関数 Nat.log2 は単調であるため
Nat.log2 n ≤ Nat.log2 (X + 1) が成立することを主張する補題。

引数:
- n, X : ℕ — 自然数
- h1 : 1 ≤ n — n は正
- hX : n ≤ X — n は X 以下
- hX1 : X ≤ X + 1 — 自明な不等式（右辺を X + 1 の形に揃えるために与えられている）

証明の方針: Nat.log2 は正の引数に対して単調増加する性質を用いる。
-/
@[simp]
lemma log2_le_log2_of_le
  {n X : ℕ} (_ : 1 ≤ n) (hX : n ≤ X) (hX1 : X ≤ X + 1) :
  Nat.log2 n ≤ Nat.log2 (X + 1) := by
  -- n ≤ X ≤ X + 1 なので n ≤ X + 1 が成り立つのじゃ -/
  have h_le : n ≤ X + 1 := Nat.le_trans hX hX1
  -- Nat.log2 は単調なので h_le から不等号を導くのじゃ -/
  have hmono : Monotone Nat.log2 := Nat.monotone_log2
  exact hmono h_le


/-- log2 of a power of two is the exponent: log2 (2^k) = k. -/
@[simp]
theorem log2_pow_two (k : ℕ) : Nat.log2 ((2:ℕ) ^ k) = k := by
  induction k with
  | zero =>
    -- Nat.log2 1 = 0 を示す -/
    rw [pow_zero]
    -- Nat.log2 1 = Nat.log 2 1 なので log2_eq_log で変換する -/
    rw [Nat.log2_eq_log]
    -- Nat.log 2 1 = 0 は log_eq_iff で示せる -/
    have hlog : Nat.log 2 1 = 0 :=
      ((Nat.log_eq_iff (Or.inr ⟨by norm_num, by norm_num⟩)).mpr ⟨by norm_num, by norm_num⟩)
    rw [hlog]
  | succ k ih =>
    -- show both inequalities and conclude equality
    have h1 : Nat.log2 ((2:ℕ) ^ (k + 1)) ≤ k + 1 := by
      have : 1 ≤ (2:ℕ) ^ (k + 1) := by
        have hpos : 0 < (2:ℕ) := by norm_num
        have hpow : 0 < (2:ℕ) ^ (k + 1) := Nat.pow_pos hpos
        exact Nat.succ_le_of_lt hpow
      -- pow_log2_le_self は Nat.log を用いた不等式を返すので Nat.log2_eq_log で書き換え、
      -- pow_le_pow_left_iff を使って指数の不等号を得るのじゃ -/
      have hpow := pow_log2_le_self this
      have hpow' : (2 : ℕ) ^ (Nat.log2 ((2 : ℕ) ^ (k + 1))) ≤ (2 : ℕ) ^ (k + 1) := by
        rw [← Nat.log2_eq_log] at hpow; exact hpow
      exact (pow_le_pow_left_iff (by norm_num)).mp hpow'
    have h2 : k + 1 ≤ Nat.log2 ((2:ℕ) ^ (k + 1)) := by
      -- provide an explicit proof 1 ≤ 2^(k+1) instead of using `simp` -/
      have hpos : 0 < (2:ℕ) := by norm_num
      have hpow_pos : 0 < (2:ℕ) ^ (k + 1) := Nat.pow_pos hpos
      have h1_le : 1 ≤ (2:ℕ) ^ (k + 1) := Nat.succ_le_of_lt hpow_pos
      have hlt := lt_pow_succ_log2_of_one_le (by exact h1_le)
      -- apply to n = 2^(k+1)
      have : (2:ℕ) ^ (k + 1) < (2:ℕ) ^ (Nat.log 2 ((2:ℕ) ^ (k + 1)) + 1) := hlt
      -- convert using log2_eq_log
      have hlog := Nat.log2_eq_log ((2:ℕ) ^ (k + 1))
      rw [← hlog] at this
      exact Nat.le_of_lt_succ (lt_of_lt_of_le (by simp only [Nat.log2_two_pow, Nat.succ_eq_add_one,
        lt_add_iff_pos_right, Nat.zero_lt_one]) (le_refl _))
    linarith
  -- TODO: simple nat linear arithmetic can replace this linarith

/-
n ≥ 1 のときに 2 ^ (Nat.log2 n) ≤ n であることを主張する補題の文書化コメント。

説明:
- `Nat.log2 n` は自然対数の底 2 に関する floor(log2 n) を表す（n ≥ 1 を仮定）。
- したがって、ある整数 k = Nat.log2 n に対して 2^k ≤ n < 2^(k+1) が成り立ち、その左不等号が本補題の主張である。

利用例・用途:
- 自然数 n の二進表現の桁数に関する評価や、2 のべき乗による上界・下界の導出に用いる。
- 証明において、`Nat.log2` の定義から直接導ける基本的不等式として頻繁に参照される。

証明方針（スケッチ）:
- `Nat.log2` の定義（ある k が存在して 2^k ≤ n < 2^(k+1) となること）を用いるか、
- `Nat.log2` に関する既存の補題（例えば log2 の性質や単調性）を利用して示す。

引数:
- `n : ℕ` : 自然数、仮定として `1 ≤ n` が必要。

タグ: log2, pow, 二進法, 不等式, 自然数
-/
@[simp]
lemma pow_log2_le {n : ℕ} (hn : 1 ≤ n) : (2:ℕ)^(Nat.log2 n) ≤ n := by
  -- Nat.log2 n = Nat.log 2 n なので pow_log2_le_self を使う
  simpa [Nat.log2_eq_log n] using pow_log2_le_self hn


-- 自然数の商と余りによる分解
/--
自然数 n, m に対して、n を m で割った商と余りによる分解を与える標準的な恒等式。

具体的には、n を m で割った商 n / m と余り n % m を用いて
n = m * (n / m) + n % m
が成り立つことを主張する。

また m > 0 のときは余りについて n % m < m が成り立ち、商と余りは一意である（剰余の標準的性質）。
m = 0 の場合には規約により n / 0 = 0, n % 0 = n となり、上の式は自明に成り立つ。
-/
lemma eq_div_mul_add_mod (n m : ℕ) : n = m * (n / m) + n % m := by
  rw [Nat.div_add_mod]


/--
n に 1 を加えた形での除算と剰余の分解に関する補題。

説明:
与えられた自然数 n, m に対して、除算と剰余の標準的な等式
  n = m * (n / m) + n % m
に両辺で 1 を加えることで得られる等式
  n + 1 = m * (n / m) + n % m + 1
を主張する。証明は Nat.div_add_mod_eq を使って右辺を n に書き直し、両辺に 1 を足すだけである。

備考:
m = 0 の場合も Lean の自然数除算・剰余の定義により等式は成り立つ（0 による除算は 0、剰余は n）。
参照: Nat.div_add_mod_eq（除算と剰余の分解の基本事実）
-/
lemma one_eq_div_mul_add_mod_one (n m : ℕ) : n + 1 = m * (n / m) + n % m + 1 := by
  rw [Nat.div_add_mod]


/- This theorem states that for any natural number n, the greatest common divisor (gcd) of n and n + 1 is 1. -/
/--
任意の自然数 n に対して n と n + 1 は互いに素であり、
Nat.gcd n (n + 1) = 1 が成り立つことを主張する定理。

証明の要旨：もし d が n と n + 1 の公約数ならば
d は (n + 1) - n = 1 を割ることになるため d = 1 であり、
したがって最大公約数は 1 である。
-/
theorem coprime_gcd_self_succ (n : ℕ) : Nat.gcd n (n + 1) = 1 := by simp
theorem coprime_gcd_self_succ' (n : ℕ) : Nat.gcd n (n + 1) = 1 := by
  -- gcd(n, n+1) = gcd(n+1, n) = gcd(n, (n+1) % n)
  rw [Nat.gcd_comm]
  rw [Nat.gcd_rec]
  rw [Nat.mod_eq_of_lt (Nat.lt_succ_self n)]
  -- simp
  simp only [Nat.gcd_self_add_right, Nat.gcd_one_right]


/--
任意の自然数 `n` に対して `n` と `n + 1` は互いに素であることを主張する補題。

証明の要点：もしある正整数 `p` が `n` と `n + 1` の両方を割り切るなら、
`p` はそれらの差 `(n + 1) - n = 1` も割り切ることになる。したがって `p = 1` であり、
公約数は 1 のみである。ゆえに `Nat.Coprime n (n + 1)` が成り立つ。

標準的かつ基本的な性質であり、隣接する自然数は常に互いに素である。
-/
lemma coprime_self_succ (n : ℕ) : Nat.Coprime n (n + 1) := by
  rw [Nat.Coprime]
  have : ∀ d, d ∣ n → d ∣ n+1 → d = 1 := by
    intro d hdn hdn1
    have : d ∣ (n+1) - n := Nat.dvd_sub hdn1 hdn
    simp at this
    omega
  have h1 : n.gcd (n+1) ∣ n := Nat.gcd_dvd_left n (n+1)
  have h2 : n.gcd (n+1) ∣ n+1 := Nat.gcd_dvd_right n (n+1)
  exact this _ h1 h2


-- 補題: 正であれば 0 ではない
lemma ne_zero_of_pos {n : ℕ} (h : 0 < n) : n ≠ 0 :=
  Nat.pos_iff_ne_zero.mp h

-- 補題: 正な二つの自然数の積は 0 ではない
lemma mul_ne_zero_of_pos {x y : ℕ} (hx : 0 < x) (hy : 0 < y) : x * y ≠ 0 := by
  apply Nat.mul_ne_zero
  · exact Nat.pos_iff_ne_zero.mp hx
  · exact Nat.pos_iff_ne_zero.mp hy


-- a * b * c ≠ 0
lemma abc_mul_ne_zero {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
  a * b * c ≠ 0 := by
  apply Nat.mul_ne_zero
  · apply Nat.mul_ne_zero
    · exact ha
    · exact hb
  · exact hc

lemma abc_mul_ne_zero' {a b c : ℕ} (ha : a > 0) (hb : b > 0) (hc : c > 0) :
  a * b * c ≠ 0 := by
  apply Nat.mul_ne_zero
  · apply Nat.mul_ne_zero
    · exact Nat.pos_iff_ne_zero.mp ha
    · exact Nat.pos_iff_ne_zero.mp hb
  · exact Nat.pos_iff_ne_zero.mp hc



end Nat



namespace Finset


/-- Finset.prod_rpow (*AI use) -/
lemma prod_rpow {α : Type*} (s : Finset α) (f : α → ℝ) (r : ℝ) (_hr : 0 ≤ r) (hf : ∀ a, 0 ≤ f a) :
  (Finset.prod s f) ^ r = Finset.prod s (fun a => (f a) ^ r) := by
  -- Proof by induction on the finite set `s`
  classical
  induction s using Finset.induction_on with
  | empty =>
    -- Base case: s is empty, both sides equal 1
    simp only [Finset.prod_empty, Real.one_rpow]
  | insert a s ha ih =>
    -- Inductive case: s = insert a s' with s' nonempty
    rw [Finset.prod_insert ha]
    -- (f a * ∏ x ∈ s, f x) ^ r = (f a) ^ r * (∏ x ∈ s, f x) ^ r
    have ha_nonneg : 0 ≤ f a := hf a
    have hs_nonneg : 0 ≤ Finset.prod s f := Finset.prod_nonneg (fun x _ => hf x)
    rw [Real.mul_rpow ha_nonneg hs_nonneg]
    -- ここで ih : (∏ x ∈ s, f x) ^ r = ∏ a ∈ s, f a ^ r を使う
    rw [ih]
    -- (f a) ^ r * ∏ a ∈ s, f a ^ r = ∏ a ∈ insert a s, f a ^ r
    rw [Finset.prod_insert ha]


end Finset

end ABC



namespace ABC

-- General lemmas used in multiple places in mgf_twoTail_log

section general_lemmas



/-- Division inequality lemma (*AI use) -/
lemma div_le_div_of_le_of_nonneg {a b c d : ℝ} (h : a ≤ b) (_hcd : 0 ≤ c) (hd : 0 < d) :
  a / d ≤ b / d := by
  -- 両辺に 1/d (> 0) を掛けて不等式を保つ
  rw [div_eq_mul_inv a d, div_eq_mul_inv b d]
  exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr (le_of_lt hd))


/-- Absolute value equality for nonnegative reals (*AI use) -/
lemma abs_eq_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : |x| = x := by
  rw [abs_of_nonneg hx]


/-- Inverse rpow lemma for positive a (*AI use) -/
lemma inv_rpow {a : ℝ} (ha : 0 < a) (r : ℝ) :
  a ^ (-r) = 1 / (a ^ r) := by
  rw [Real.rpow_neg (le_of_lt ha) r, inv_eq_one_div]


/-- Division rpow lemma for nonnegative a and positive b (*AI use) -/
lemma div_rpow {a : ℝ} {b : ℝ} (ha : 0 < a) (hb : 0 < b) (r : ℝ) :
  (a / b) ^ r = a ^ r / b ^ r := by
  -- a, b > 0 なので rpow の分配公式が使える
  rw [div_eq_mul_inv]
  have hb_inv_pos : 0 < b⁻¹ := inv_pos.mpr hb
  -- (a * b⁻¹) ^ r = a ^ r * (b⁻¹) ^ r
  rw [Real.mul_rpow (le_of_lt ha) (le_of_lt hb_inv_pos)]
  -- (b⁻¹) ^ r = (b ^ r)⁻¹ は inv_rpow で証明できる
  rw [Real.inv_rpow (le_of_lt hb) r]
  -- a ^ r * (b ^ r)⁻¹ = a ^ r / b ^ r
  rw [←div_eq_mul_inv]


/-- Division rpow lemma for nonnegative a and positive b (*AI use) -/
lemma rpow_div_of_nonneg {a : ℝ} {b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (r : ℝ) :
  (a / b) ^ r = a ^ r / b ^ r := by
  -- a ≥ 0, b > 0 なので rpow の分配公式が使える
  rw [div_eq_mul_inv]
  have hb_inv_pos : 0 < b⁻¹ := inv_pos.mpr hb
  -- (a * b⁻¹) ^ r = a ^ r * (b⁻¹) ^ r
  rw [Real.mul_rpow ha (le_of_lt hb_inv_pos)]
  -- (b⁻¹) ^ r = (b ^ r)⁻¹ は inv_rpow で証明できる
  rw [Real.inv_rpow (le_of_lt hb) r]
  -- a ^ r * (b ^ r)⁻¹ = a ^ r / b ^ r
  rw [←div_eq_mul_inv]


-- If a and b are coprime and a + b = c then c > 0 (i.e., c is nonzero).
lemma abc_pos_from_coprime {a b c : ℕ} (hrel : a + b = c) (hcoprime : IsCoprime a b) : 0 < c := by
  by_contra H
  have hc0 : c = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt H)
  -- then a = b = 0, contradicting coprimality
  have hab0 : a = 0 ∧ b = 0 := by
    rw [hc0] at hrel
    exact Nat.add_eq_zero_iff.mp hrel
  rcases hab0 with ⟨ha0, hb0⟩
  -- rewrite coprime to IsCoprime 0 0 and use lemma not_isCoprime_zero_zero
  rw [ha0, hb0] at hcoprime
  exact not_isCoprime_zero_zero hcoprime


-- 補題: a + b = c 且つ IsCoprime a b なら c ≠ 0（既存の abc_pos_from_coprime を再利用）
lemma c_ne_zero_of_coprime_sum {a b c : ℕ} (hrel : a + b = c) (hcoprime : IsCoprime a b) : c ≠ 0 := by
  have hc_pos : 0 < c := abc_pos_from_coprime hrel hcoprime
  exact Nat.pos_iff_ne_zero.mp hc_pos


-- 補題: a,b > 0 かつ a + b = c なら a,b,c は正かつ非零
lemma abc_pos_and_ne_zero_of_pos {a b c : ℕ} (hrel : a + b = c) (ha : 0 < a) (hb : 0 < b) :
  0 < c ∧ a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 := by
  have hc : 0 < c := by linarith [ha, hb, hrel]
  have ha_ne : a ≠ 0 := Nat.pos_iff_ne_zero.mp ha
  have hb_ne : b ≠ 0 := Nat.pos_iff_ne_zero.mp hb
  have hc_ne : c ≠ 0 := Nat.pos_iff_ne_zero.mp hc
  exact ⟨hc, ha_ne, hb_ne, hc_ne⟩


-- a > 0, b > 0, c > 0 を取り出す補題
lemma abc_pos_of_pos {a b c : ℕ} (hrel : a + b = c) (ha : 0 < a) (hb : 0 < b) :
  0 < a ∧ 0 < b ∧ 0 < c := by
  have hc : 0 < c := by linarith [ha, hb, hrel]
  exact ⟨ha, hb, hc⟩


-- c > 0 なら a > 0, b > 0 を取り出す補題
lemma ab_pos_of_c_pos {a b c : ℕ} (hrel : a + b = c) (hc : 0 < c) :
  0 < a ∨ 0 < b := by
  by_contra H
  -- H : ¬(0 < a ∨ 0 < b) なので 0 < a → False, 0 < b → False
  have ha : a ≤ 0 := le_of_not_gt (by_contra fun hnn => H (Or.inl (not_not.mp hnn)))
  have hb : b ≤ 0 := le_of_not_gt (by_contra fun hb_pos => H (Or.inr (not_not.mp hb_pos)))
  -- a, b は自然数なので a = 0, b = 0
  have ha0 : a = 0 := Nat.eq_zero_of_le_zero ha
  have hb0 : b = 0 := Nat.eq_zero_of_le_zero hb
  -- a + b = c より c = 0
  rw [ha0, hb0] at hrel
  have hc0 : c = 0 := by simpa [eq_comm] using hrel
  -- しかし hc : 0 < c なので矛盾
  linarith


/-- lemma about the positivity of prime numbers -/
@[simp]
lemma prime_pos {p : ℕ} (pp : Nat.Prime p) : 0 < p := by
  exact Nat.Prime.pos pp


@[simp]
lemma prime_rpos {p : ℕ} (pp : Nat.Prime p) : 0 < (p : ℝ) := by
  exact Nat.cast_pos.mpr (prime_pos pp)


@[simp]
lemma prime_ge1 {p : ℕ} (pp : Nat.Prime p) : 1 ≤ p := by
  linarith [prime_pos pp]


@[simp]
lemma prime_rge1 {p : ℕ} (pp : Nat.Prime p) : 1 ≤ (p : ℝ) := by
  -- ℕ の 1 ≤ p から ℝ の 1 ≤ ↑p へ型を持ち上げる
  exact_mod_cast (prime_ge1 pp)


@[simp]
lemma div_lt_div_of_lt_of_pos
  {a b c : ℝ} (_ : 0 < a) (_ : a < b) (hc : 0 < c) (hcb : c < b) :
  (1 : ℝ) / b < (1 : ℝ) / c :=
  one_div_lt_one_div_of_lt hc hcb

-- (1 : ℝ) / (X : ℝ) ^ a < (1 : ℝ) / (M ^ a) := by
            -- 1 < (X : ℝ) ^ a / M ^ a かつ 0 < M ^ a より、分数の大小比較で
@[simp]
lemma div_lt_div_of_pos_of_lt
  {a : ℝ} (ha : 0 < a) {X M : ℝ} (_ : 1 < X) (hM : 1 < M) (hMX : M < X) (hdenoms : 0 < M ^ a) :
  (1 : ℝ) / (X : ℝ) ^ a < (1 : ℝ) / (M ^ a) := by
  have hpow_gt : M ^ a < X ^ a := Real.rpow_lt_rpow (by linarith [hM]) hMX ha
  exact one_div_lt_one_div_of_lt hdenoms hpow_gt

@[simp]
lemma mul_one_div_cancel_left {α : Type*} [DivisionRing α] (a b : α) (ha : a ≠ 0) :
  a * (1 / a * b) = b := by
  calc
    a * (1 / a * b) = a * (a⁻¹ * b) := by
      rw [div_eq_mul_inv, one_mul]
    _ = (a * a⁻¹) * b := by
      rw [← mul_assoc]
    _ = 1 * b := by
      rw [DivisionRing.mul_inv_cancel (a := a) ha]
    _ = b := by
      rw [one_mul]

@[simp]
theorem div_lt_iff {a b c : ℝ} (hc : 0 < c) :
  a / c < b ↔ a < b * c := by
  -- c > 0 なので両辺に c や 1/c を掛けて不等号を変形する
  have hc_ne : c ≠ 0 := by linarith
  refine Iff.intro ?h1 ?h2
  · -- 右辺へ: a / c < b から a < b * c を示す
    intro h
    have hmul := mul_lt_mul_of_pos_right h hc
    have eq1 : (a / c) * c = a := by
      field_simp [hc_ne]
    rw [eq1] at hmul
    exact hmul
  · -- 左辺へ: a < b * c から a / c < b を示す
    intro h
    -- 1/c > 0 を得て両辺に掛ける
    have h1c : 0 < (1 : ℝ) / c := div_pos (by norm_num) hc
    have hmul := mul_lt_mul_of_pos_right h h1c
    have eq2 : a * (1 / c) = a / c := by field_simp [hc_ne]
    have eq3 : (b * c) * (1 / c) = b := by field_simp [hc_ne]
    rw [eq2, eq3] at hmul
    exact hmul

-- #check div_lt_div_of_lt_of_pos
-- #check div_lt_div_of_pos_of_lt
-- #check mul_one_div_cancel_left
-- #check div_lt_iff

end general_lemmas

end ABC





namespace Real

/--
実数 a, b, c に対して、c が正 (c > 0) の場合に成り立つ不等式の同値変形を示す補題。

直感的には「a を c で割った値が b 以下である」ことは
「a が b に c を掛けた値以下である」ことと同値である、という主張です。
（除算は正の数に関して単調増加なので、この変換が可能になります。）

用途:
- 不等号の形を除算 ⇄ 乗算のどちらかに変形したいときに使います。
- `@[simp]` 属性が付いているため、簡約規則として自動化にも利用されます。

前提:
- c : ℝ, c > 0
- a, b : ℝ
-/
@[simp]
lemma div_le_iff {a b c : ℝ} (hc : 0 < c) :
  a / c ≤ b ↔ a ≤ b * c := by
  -- c > 0 なので両辺に c や 1/c を掛けて不等号を変形する
  have hc_ne : c ≠ 0 := by linarith
  refine Iff.intro ?h1 ?h2
  · -- 右辺へ: a / c ≤ b から a ≤ b * c を示す
    intro h
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hc)
    have eq1 : (a / c) * c = a := by
      field_simp [hc_ne]
    rw [eq1] at hmul
    exact hmul
  · -- 左辺へ: a ≤ b * c から a / c ≤ b を示す
    intro h
    -- 1/c > 0 を得て両辺に掛ける
    have h1c : 0 < (1 : ℝ) / c := div_pos (by norm_num) hc
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt h1c)
    have eq2 : a * (1 / c) = a / c := by field_simp [hc_ne]
    have eq3 : (b * c) * (1 / c) = b := by field_simp [hc_ne]
    rw [eq2, eq3] at hmul
    exact hmul


/--
正の実数 `x` に対して実数冪の零乗は 1 になることを示す補題。

具体的には、`0 < x` を仮定すると `x ^ (0 : ℝ) = 1` が成り立つ。
これは実数冪の定義（`x ^ y = exp (y * log x)`）と `exp 0 = 1` の事実から従う。
`simp` 属性が付与されており、簡約時に自動的に用いられることを意図している。

引数:
- `x` : 実数
- `hx` : `0 < x` （対数 `log x` をとるために必要）
-/
lemma rpow_zero_of_pos {x : ℝ} (hx : 0 < x) :
  x ^ (0 : ℝ) = 1 := by
  -- x^0 = exp (0 * log x) = exp 0 = 1 -/
  rw [Real.rpow_def_of_pos hx, mul_zero, Real.exp_zero]


/--
(n + m : ℝ) * Real.log x = (n : ℝ) * Real.log x + (m : ℝ) * Real.log x を表す補題。
x は Real.log の定義域（通常は x > 0）を満たす実数であると仮定する。
自然数 n, m を実数へキャストしたものに対して、実数倍の分配法則により対数に関する等式を与える。
log や累乗（rpow）に関する式の簡約・変形に便利である。
-/
lemma add_rpow {x : ℝ} (n m : ℕ) :
  (n + m : ℝ) * Real.log x = (n : ℝ) * Real.log x + (m : ℝ) * Real.log x := by
  -- (n + m : ℝ) * Real.log x = n * Real.log x + m * Real.log x
  rw [add_mul]


/-- 正の実数 x と自然数 n, m に対して、自然数を実数にキャストした冪は加法に関して積に分解される。
  つまり
    x ^ (n + m : ℝ) = x ^ (n : ℝ) * x ^ (m : ℝ)
  が成り立つ。ここで仮定 hx : 0 < x は底 x が正であることを示しており、
  実数指数の定義（対数と指数の組）に必要である点に注意。 -/
lemma dk_rpow_nadd {x : ℝ} (hx : 0 < x) (n m : ℕ) :
  x ^ (n + m : ℝ) = x ^ (n : ℝ) * x ^ (m : ℝ) := by
  -- x^(n+m) = exp((n+m) * log x) = exp(n * log x + m * log x) = exp(n * log x) * exp(m * log x) = x^n * x^m
  -- 展開してから中間等式を作ることで安全に変形する
  -- LHS を指数表現に展開
  have hL : x ^ (n + m : ℝ) = Real.exp ((n + m : ℝ) * Real.log x) := by
    rw [Real.rpow_def_of_pos hx]
    rw [mul_comm]
    -- 0 < x の仮定 hx を明示的に使う
  -- RHS を指数表現に展開
  have hR : x ^ (n : ℝ) * x ^ (m : ℝ) = Real.exp ((n : ℝ) * Real.log x) * Real.exp ((m : ℝ) * Real.log x) := by
    rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx]
    -- 乗算の順序を揃えるため mul_comm を使う
    rw [mul_comm (Real.log x) (n : ℝ), mul_comm (Real.log x) (m : ℝ)]
  -- 中間の等式を示して結論を得る
  calc
    x ^ (n + m : ℝ) = Real.exp ((n + m : ℝ) * Real.log x) := by rw [hL]
    _ = Real.exp ((n : ℝ) * Real.log x + (m : ℝ) * Real.log x) := by
      have : (n + m : ℝ) * Real.log x = (n : ℝ) * Real.log x + (m : ℝ) * Real.log x := by
        simp [add_mul]
      rw [this]
    _ = Real.exp ((n : ℝ) * Real.log x) * Real.exp ((m : ℝ) * Real.log x) := by rw [Real.exp_add]
    _ = x ^ (n : ℝ) * x ^ (m : ℝ) := by rw [hR]


/--
正の実数 `x` と自然数 `n` に対して、自然数べき乗 `x ^ n` と自然数を実数へコーアースした後の実数べき乗 `x ^ (n : ℝ)` が一致することを表す補題。
仮定 `0 < x` は実数に対する `rpow`（実数べき乗）が定義されるために必要であり、`n` は自然数であることに注意してください。
-/
lemma rpow_nat_cast {x : ℝ} (hx : 0 < x) (n : ℕ) :
  x ^ n = x ^ (n : ℝ) := by
  induction n
  case zero =>
    -- x^0 = x^0 を示す -/
    rw [Nat.cast_zero, Real.rpow_zero_of_pos hx, pow_zero]
  case succ n ih =>
    calc
      x ^ (n + 1) = x ^ n * x := by
        -- `pow_succ` は x^(n+1) = x^n * x
        simp [pow_succ]
      _ = (x ^ (n : ℝ)) * x := by
        -- 帰納法の仮定を使用
        rw [ih]
      _ = (x ^ (n : ℝ)) * x ^ (1 : ℝ) := by
        -- x = x^1
        simp [Real.rpow_one]
      _ = x ^ ((n : ℝ) + 1) := by
        -- rpow の加法則（底 > 0 が必要）を逆向きに適用して積をべきに戻す
        rw [← Real.rpow_add hx (n : ℝ) 1]
      _ = x ^ (n + 1 : ℝ) := by
        -- キャストの整形で同じにする
        simp
    -- キャスト (↑n + 1) と ↑(n + 1) は simp で解消できるので rfl の代わりに simp を使う
    simp [Nat.cast_add]


lemma rpow_nat_cast' {x : ℝ} (hx : 0 < x) (n : ℕ) :
  x ^ n = x ^ (n : ℝ) := by
  induction n with
  | zero =>
      simp [Real.rpow_zero_of_pos hx]  -- x^0 = x^0
  | succ n ih =>
      calc
        x ^ (n + 1) = x ^ n * x := by
          simp [pow_succ]
        _ = (x ^ (n : ℝ)) * x := by
          rw [ih]
        _ = (x ^ (n : ℝ)) * x ^ (1 : ℝ) := by
          simp [Real.rpow_one]
        _ = x ^ ((n : ℝ) + 1) := by
          -- rpow の加法則（底 > 0）
          simpa using (Eq.symm (Real.rpow_add hx (n : ℝ) 1))
        _ = x ^ (n + 1 : ℝ) := by
          -- キャスト整形
          simp
      simp

/--
x : ℝ が正 (0 < x) で n : ℕ のとき，
実数べきで自然数を実数にキャストした x^(n : ℝ) は自然数べき x^n と等しいことを示す。
これは `rpow_nat_cast` の対称形である。
-/
lemma rpow_nat_cast_symm {x : ℝ} (hx : 0 < x) (n : ℕ) :
  x ^ (n : ℝ) = x ^ n :=
  (rpow_nat_cast hx n).symm

-- #check Real.rpow_pow -- 存在しない
-- (x^y)^z = x^(y*z) for x > 0
lemma rpow_pow {x : ℝ} (hx : 0 < x) (n : ℕ) (m : ℝ) :
  (x ^ n) ^ m = x ^ ((n : ℝ) * m) := by
  -- (x^n)^m = exp(m * log(x^n)) = exp(m * n * log x) = exp((n : ℝ) * m * log x) = x^((n : ℝ) * m)
  have h1 : (x ^ n) ^ m = Real.exp (m * Real.log (x ^ n)) := by
    rw [Real.rpow_def_of_pos (pow_pos hx n)]
    rw [mul_comm]
  have h2 : Real.log (x ^ n) = (n : ℝ) * Real.log x := by
    -- n を実数にキャストしてから log_rpow を適用する
    rw [← rpow_nat_cast_symm hx n, Real.log_rpow hx (n : ℝ)]
  calc
    (x ^ n) ^ m = Real.exp (m * Real.log (x ^ n)) := by rw [h1]
    _ = Real.exp (m * ((n : ℝ) * Real.log x)) := by rw [h2]
    _ = Real.exp ((n : ℝ) * m * Real.log x) := by
      ring_nf
    _ = x ^ ((n : ℝ) * m) := by
      rw [Real.rpow_def_of_pos hx]
      rw [mul_comm]





/-! ### Phase 2: 補題の整備 - log 2 / log 3 関連 -/

-- log 2 / log 3 性質定理
lemma log2_div_log3_pos : 0 < log 2 / log 3 := by
  -- log 2 > 0 ∧ log 3 > 0
  have h1 : 0 < log 2 := by
    apply log_pos
    norm_num
  have h2 : 0 < log 3 := by
    apply log_pos
    norm_num
  -- a > 0 ∧ b > 0 ⇒ a/b > 0
  exact div_pos h1 h2


-- log 2 / log 3 > 1/2 （実際の数値評価: log 2 ≈ 0.693, log 3 ≈ 1.098, 0.693/1.098 ≈ 0.631 > 0.5）
lemma log2_div_log3_gt_half : log 2 / log 3 > 1 / 2 := by
  -- log 4 > log 3 (since 4 > 3) and log 4 = 2 * log 2, so 2*log2 > log3
  have h1 : (2 : ℝ) * log 2 = log 4 := by
    rw [two_mul]
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h2 : log 4 > log 3 := by
    apply log_lt_log
    · norm_num
    · norm_num
  have h2' : 2 * log 2 > log 3 := by
    rwa [← h1] at h2
  -- from 2*log2 > log3 we get (1/2)*log3 < log2
  have h_half_lt : (1 / 2) * log 3 < log 2 := by linarith [h2']
  -- conclude using the field-version lemma lt_div_iff₀ which requires positivity of denom
  have h_log3_pos : 0 < log 3 := by apply log_pos; norm_num
  exact (lt_div_iff₀ h_log3_pos).2 h_half_lt


-- log 2 / log 3 < 1 (明らかに、log 2 < log 3 なので)
lemma log2_div_log3_lt_one : log 2 / log 3 < 1 := by
  have h1 : 0 < log 3 := by apply log_pos; norm_num
  have h2 : log 2 < log 3 := by
    apply log_lt_log
    · norm_num
    · norm_num
  exact (div_lt_one h1).mpr h2


-- log 2 / log 3 ≈ 0.631 の数値評価補題
lemma log2_div_log3_le_two_thirds : log 2 / log 3 ≤ 2 / 3 := by
  -- 数値的には 0.631 < 0.667 だが、形式的証明は複雑
  -- Transform the inequality using `div_le_iff₀` (log 3 > 0)
  have hlog3_pos : 0 < log 3 := by apply log_pos; norm_num
  -- rewrite to an equivalent inequality without division
  rw [div_le_iff₀ hlog3_pos]
  -- it suffices to show `log 2 ≤ (2 / 3) * log 3`; multiply both sides by 3 and use
  -- `log (2 ^ 3) = 3 * log 2`, `log (3 ^ 2) = 2 * log 3` and monotonicity of `log`.
  have h_pow : 3 * log 2 ≤ 2 * log 3 := by
    -- show first log (2^3) ≤ log (3^2)
    have hlog_pow : log (2 ^ 3) ≤ log (3 ^ 2) :=
      (Real.log_le_log_iff (by norm_num) (by norm_num)).2 (by norm_num)
    -- convert `log (x ^ n)` to `n * log x`
    rw [Real.log_pow, Real.log_pow] at hlog_pow
    exact hlog_pow
  -- finish by linear arithmetic
  linarith [h_pow]


/-! ### Phase 2: 補題の整備 - rpow と指数の性質 -/


-- p ≥ 3 ⇒ p > 1
lemma nat_ge_3_cast_gt_one {p : ℕ} (hp3 : p ≥ 3) : (1 : ℝ) < p := by
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  linarith


-- p ≥ 3 ⇒ p > 0
lemma nat_ge_3_cast_pos {p : ℕ} (hp3 : p ≥ 3) : (0 : ℝ) < p := by
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  linarith


-- p ≥ 3 ⇒ p ≠ 0
lemma nat_ge_3_cast_ne_zero {p : ℕ} (hp3 : p ≥ 3) : (p : ℝ) ≠ 0 := by
  have : (0 : ℝ) < p := nat_ge_3_cast_pos hp3
  linarith


-- 0 < t ≤ log 2 / log 3 ⇒ t < 1
lemma t_le_log2_div_log3_lt_one {t : ℝ} (_ht : 0 < t) (ht_le : t ≤ log 2 / log 3) : t < 1 := by
  calc t ≤ log 2 / log 3 := ht_le
    _ < 1 := log2_div_log3_lt_one


-- 0 < t ≤ log 2 / log 3 ⇒ t - 1 < 0
lemma t_sub_one_neg {t : ℝ} (ht : 0 < t) (ht_le : t ≤ log 2 / log 3) : t - 1 < 0 := by
  have : t < 1 := t_le_log2_div_log3_lt_one ht ht_le
  linarith


-- 0 < t ≤ 1/2 ⇒ t - 1 ≤ -1/2
lemma t_sub_one_le_neg_half {t : ℝ} (ht_half : t ≤ 1 / 2) : t - 1 ≤ -1 / 2 := by
  linarith


-- 0 < t ≤ log 2 / log 3 ⇒ t - 1 ≤ log 2 / log 3 - 1
lemma t_sub_one_le_log2_div_log3_sub_one {t : ℝ} (ht_le : t ≤ log 2 / log 3) :
    t - 1 ≤ log 2 / log 3 - 1 := by
  linarith


-- 3^(-log 2 / log 3) = 1/2
lemma rpow_neg_log2_div_log3_eq_inv_two : (3 : ℝ) ^ (-log 2 / log 3) = 1 / 2 := by
  -- 3 > 0 を使って定義展開: x^y = exp (y * log x)
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [Real.rpow_def_of_pos h3]
  -- 指数を簡約: (-log 2 / log 3) * log 3 = -log 2
  have log3_ne_zero : log 3 ≠ 0 := (log_pos (by norm_num)).ne'
  have : log 3 * (-log 2 / log 3) = -log 2 := by
    field_simp [log3_ne_zero]
  rw [this]
  -- exp(-log 2) = (exp (log 2))⁻¹ = 2⁻¹
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  simp only [one_div]

-- 3^(log 2 / log 3) = 2 (逆向き)
lemma three_pow_alpha_eq_two : (3 : ℝ) ^ (log 2 / log 3) = 2 := by
  have h_inv : (3 : ℝ) ^ (-log 2 / log 3) = 1 / 2 := rpow_neg_log2_div_log3_eq_inv_two
  have h3 : (0 : ℝ) < 3 := by norm_num
  have h_neg_eq : (3 : ℝ) ^ (-log 2 / log 3) = ((3 : ℝ) ^ (log 2 / log 3))⁻¹ := by
    rw [← Real.rpow_neg h3.le]
    ring_nf
  rw [h_neg_eq] at h_inv
  have : (3 : ℝ) ^ (log 2 / log 3) = (1 / 2)⁻¹ := by
    field_simp at h_inv ⊢
    exact h_inv.symm
  simp only [inv_div, div_one] at this
  exact this

-- α := log 2 / log 3 の基本性質
namespace Alpha

-- 0 < α
lemma pos : 0 < log 2 / log 3 := by
  have h2 : 1 < (2:ℝ) := by norm_num
  have h3 : 1 < (3:ℝ) := by norm_num
  have hlog2 : 0 < log 2 := Real.log_pos h2
  have hlog3 : 0 < log 3 := Real.log_pos h3
  exact div_pos hlog2 hlog3

-- α < 1
lemma lt_one : log 2 / log 3 < 1 := by
  have h : log 2 < log 3 := by
    have : (2:ℝ) < 3 := by norm_num
    exact Real.log_lt_log (by norm_num) this
  have h3pos : 0 < log 3 := Real.log_pos (by norm_num : 1 < (3:ℝ))
  exact (div_lt_one h3pos).mpr h

-- α ≤ 2/3
lemma le_two_thirds : log 2 / log 3 ≤ (2:ℝ) / 3 := by
  -- 2 ≤ 3^(2/3) から log 2 ≤ (2/3) * log 3
  have h2_le : (2:ℝ) ≤ (3:ℝ) ^ ((2:ℝ) / 3) := by
    -- 2^3 = 8 ≤ 9 = 3^2 なので 2 ≤ 3^(2/3)
    have h8_9 : (8:ℝ) ≤ 9 := by norm_num
    have h2_cubed : (2:ℝ) ^ (3:ℝ) = 8 := by norm_num
    have h3_squared : (3:ℝ) ^ (2:ℝ) = 9 := by norm_num
    -- 2 = 8^(1/3), 3^(2/3) = 9^(1/3)
    have : (8:ℝ) ^ ((1:ℝ) / 3) ≤ (9:ℝ) ^ ((1:ℝ) / 3) :=
      Real.rpow_le_rpow (by norm_num) h8_9 (by norm_num)
    simp only [← h2_cubed, ← h3_squared] at this
    have : ((2:ℝ) ^ (3:ℝ)) ^ ((1:ℝ) / 3) ≤ ((3:ℝ) ^ (2:ℝ)) ^ ((1:ℝ) / 3) := this
    simp only [← Real.rpow_mul (by norm_num : 0 ≤ (2:ℝ)),
               ← Real.rpow_mul (by norm_num : 0 ≤ (3:ℝ))] at this
    norm_num at this
    exact this
  have h3_pos : 0 < (3:ℝ) := by norm_num
  have hlog_le : log 2 ≤ (2 / 3) * log 3 := by
    have := Real.log_le_log (by norm_num : 0 < (2:ℝ)) h2_le
    rw [Real.log_rpow h3_pos] at this
    exact this
  have hlog3_pos : 0 < log 3 := Real.log_pos (by norm_num : 1 < (3:ℝ))
  exact (div_le_iff hlog3_pos).mpr hlog_le

-- 3^(α-1) = 2/3
lemma three_pow_sub_one_eq_two_thirds : (3 : ℝ) ^ (log 2 / log 3 - 1) = (2:ℝ) / 3 := by
  have h3_pos : (0 : ℝ) < 3 := by norm_num
  rw [sub_eq_add_neg, Real.rpow_add h3_pos]
  rw [three_pow_alpha_eq_two]
  rw [Real.rpow_neg_one]
  norm_num

end Alpha

-- 2 ≤ 4^(2/3)
lemma two_le_four_rpow_two_thirds : (2:ℝ) ≤ (4:ℝ) ^ ((2:ℝ)/3) := by
  -- Strategy: 2 ≤ 3^(2/3) ≤ 4^(2/3)
  -- First: 2 ≤ 3^(2/3) from 8 ≤ 9 (cube root)
  have h1 : (2:ℝ) ≤ (3:ℝ) ^ ((2:ℝ)/3) := by
    have h8_9 : (8:ℝ) ≤ 9 := by norm_num
    -- 8^(1/3) ≤ 9^(1/3)
    have h_rpow : (8:ℝ) ^ ((1:ℝ)/3) ≤ (9:ℝ) ^ ((1:ℝ)/3) :=
      Real.rpow_le_rpow (by norm_num) h8_9 (by norm_num)
    -- 8 = 2^3, so 8^(1/3) = 2
    have h8_eq : (8:ℝ) ^ ((1:ℝ)/3) = 2 := by
      have : (8:ℝ) = (2:ℝ) ^ (3:ℝ) := by norm_num
      rw [this]
      rw [← Real.rpow_mul (by norm_num : 0 ≤ (2:ℝ))]
      norm_num
    -- 9 = 3^2, so 9^(1/3) = 3^(2/3)
    have h9_eq : (9:ℝ) ^ ((1:ℝ)/3) = (3:ℝ) ^ ((2:ℝ)/3) := by
      have : (9:ℝ) = (3:ℝ) ^ (2:ℝ) := by norm_num
      rw [this]
      rw [← Real.rpow_mul (by norm_num : 0 ≤ (3:ℝ))]
      norm_num
    rw [h8_eq, h9_eq] at h_rpow
    exact h_rpow
  -- Second: 3^(2/3) ≤ 4^(2/3) (base monotonicity)
  have h2 : (3:ℝ) ^ ((2:ℝ)/3) ≤ (4:ℝ) ^ ((2:ℝ)/3) :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
  exact le_trans h1 h2

-- X ≥ 3 ⇒ X+1 ≥ 4
lemma four_le_xplus1_of_X_ge3 {X : ℕ} (hX : 3 ≤ X) : (4:ℝ) ≤ (X:ℝ) + 1 := by
  have : 4 ≤ X + 1 := by omega
  norm_cast

-- X ≥ 3 なら 2^α ≤ (X+1)^(1-α)
lemma two_pow_alpha_le_xplus1_pow_one_sub_alpha {X : ℕ} (hX : 3 ≤ X) :
  (2:ℝ) ^ (log 2 / log 3) ≤ ((X:ℝ) + 1) ^ (1 - log 2 / log 3) := by
  have hα23 : log 2 / log 3 ≤ (2:ℝ)/3 := Alpha.le_two_thirds
  have hα1 : 0 ≤ 1 - log 2 / log 3 := by
    have := Alpha.lt_one
    linarith
  have hX4 : (4:ℝ) ≤ (X:ℝ) + 1 := four_le_xplus1_of_X_ge3 hX
  -- Chain: 2^α ≤ 2^(2/3) = 4^(1/3) ≤ 4^(1-α) ≤ (X+1)^(1-α)
  -- Step 1: 2^α ≤ 2^(2/3)
  have h1 : (2:ℝ) ^ (log 2 / log 3) ≤ (2:ℝ) ^ ((2:ℝ)/3) := by
    have : 1 ≤ (2:ℝ) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_le this hα23
  -- Step 2: 2^(2/3) = 4^(1/3)
  have h_eq : (2:ℝ) ^ ((2:ℝ)/3) = (4:ℝ) ^ ((1:ℝ)/3) := by
    have : (2:ℝ) ^ ((2:ℝ)/3) = ((2:ℝ) ^ (2:ℝ)) ^ ((1:ℝ)/3) := by
      rw [← Real.rpow_mul (by norm_num : 0 ≤ (2:ℝ))]
      norm_num
    simp only [Real.rpow_two] at this
    norm_num at this
    exact this
  -- Step 3: 4^(1/3) ≤ 4^(1-α)
  have h2 : (4:ℝ) ^ ((1:ℝ)/3) ≤ (4:ℝ) ^ (1 - log 2 / log 3) := by
    have : (1:ℝ)/3 ≤ 1 - log 2 / log 3 := by linarith [hα23]
    have : 1 ≤ (4:ℝ) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_le this ‹_›
  -- Step 4: 4^(1-α) ≤ (X+1)^(1-α)
  have h3 : (4:ℝ) ^ (1 - log 2 / log 3) ≤ ((X:ℝ) + 1) ^ (1 - log 2 / log 3) :=
    Real.rpow_le_rpow (by norm_num) hX4 hα1
  -- Combine
  calc (2:ℝ) ^ (log 2 / log 3)
      ≤ (2:ℝ) ^ ((2:ℝ)/3) := h1
    _ = (4:ℝ) ^ ((1:ℝ)/3) := h_eq
    _ ≤ (4:ℝ) ^ (1 - log 2 / log 3) := h2
    _ ≤ ((X:ℝ) + 1) ^ (1 - log 2 / log 3) := h3


-- 底が > 1 の場合、べきは指数に関して単調増加（指数が負でも同様）
-- p ≥ 3, t ≤ s ⇒ p^(t-1) ≤ p^(s-1)
lemma rpow_le_rpow_of_exp_le_of_neg {p : ℕ} (hp3 : p ≥ 3) {t s : ℝ}
  (hts : t ≤ s) : (p : ℝ) ^ (t - 1) ≤ (p : ℝ) ^ (s - 1) := by
  have hp_one_le : 1 ≤ (p : ℝ) := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    linarith
  have h_sub_le : t - 1 ≤ s - 1 := by linarith
  exact Real.rpow_le_rpow_of_exponent_le hp_one_le h_sub_le


-- p ≥ 3, t ≤ log 2 / log 3 ⇒ p^(t-1) ≤ 3^(t-1) ≤ 3^(log_3 2 - 1) = 2/3
lemma rpow_t_sub_one_le_two_thirds {p : ℕ} (hp3 : p ≥ 3) {t : ℝ}
    (_ht : 0 < t) (ht_le : t ≤ log 2 / log 3) : (p : ℝ) ^ (t - 1) ≤ 2 / 3 := by
  -- First show the exponent t - 1 is ≤ 0 (since log 2 / log 3 < 1)
  have h_log2_lt_log3 : log 2 < log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have h_log3_pos : 0 < log 3 := by apply log_pos; norm_num
  have h_ratio_lt_one : log 2 / log 3 < 1 := by
    have h := div_lt_div_of_pos_right h_log2_lt_log3 h_log3_pos
    simpa [div_self (ne_of_gt h_log3_pos)] using h
  have h_ratio_minus1_lt0 : (log 2 / log 3) - 1 < 0 := by linarith [h_ratio_lt_one]
  have h_t_minus1_lt0 : t - 1 < 0 := lt_of_le_of_lt (by linarith) h_ratio_minus1_lt0
  have h_z_le_zero : t - 1 ≤ 0 := le_of_lt h_t_minus1_lt0

  -- Since t-1 ≤ 0 and p ≥ 3, for base comparison 3 ≤ p we have p^(t-1) ≤ 3^(t-1)
  have h3pos : 0 < (3 : ℝ) := by norm_num
  have h3_le_p : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have h1 := Real.rpow_le_rpow_of_nonpos h3pos h3_le_p h_z_le_zero
  -- h1 : p ^ (t - 1) ≤ 3 ^ (t - 1)

  -- Next, since 1 ≤ 3 and t-1 ≤ (log 2 / log 3) - 1, monotonicity in exponent gives
  -- 3^(t-1) ≤ 3^(log2/log3 - 1)
  have h_exp_le : t - 1 ≤ (log 2 / log 3) - 1 := by linarith
  have h2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (3 : ℝ)) h_exp_le
  -- h2 : 3 ^ (t - 1) ≤ 3 ^ ((log 2 / log 3) - 1)

  -- Finally evaluate 3 ^ ((log 2 / log 3) - 1) = 2 / 3
  let h_pos3 : 0 < (3 : ℝ) := by norm_num
  have h_rpow_def : (3 : ℝ) ^ ((log 2 / log 3) - 1) = exp (log 3 * ((log 2 / log 3) - 1)) := by
    rw [Real.rpow_def_of_pos h_pos3]
  have h3_nonzero : log 3 ≠ 0 := (log_pos (by norm_num)).ne'
  have h_mul : log 3 * ((log 2 / log 3) - 1) = log 2 - log 3 := by
    field_simp [h3_nonzero]
  have h_log_div : log 2 - log 3 = log (2 / 3) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
  have h_exp_log : exp (log (2 / 3)) = 2 / 3 := by apply exp_log; norm_num
  have h3val : (3 : ℝ) ^ ((log 2 / log 3) - 1) = 2 / 3 := by
    calc
      (3 : ℝ) ^ ((log 2 / log 3) - 1) = exp (log 3 * ((log 2 / log 3) - 1)) := h_rpow_def
      _ = exp (log 2 - log 3) := by rw [h_mul]
      _ = exp (log (2 / 3)) := by rw [h_log_div]
      _ = 2 / 3 := h_exp_log

  -- combine inequalities
  calc
    (p : ℝ) ^ (t - 1) ≤ 3 ^ (t - 1) := h1
    _ ≤ 3 ^ ((log 2 / log 3) - 1) := h2
    _ = 2 / 3 := h3val


-- r ≤ 2/3, 0 ≤ r < 1 ⇒ 1/(1-r) ≤ 3
lemma one_div_one_sub_le_3_of_le_two_thirds {r : ℝ}
    (hr : r ≤ 2 / 3) (hr_lt_1 : r < 1) :
    1 / (1 - r) ≤ 3 := by
  have h_denom : 1 - r ≥ 1 - 2/3 := by linarith
  have h_denom_eq : 1 - (2:ℝ)/3 = 1/3 := by norm_num
  have h_denom_pos : 0 < 1 - r := by linarith
  calc 1 / (1 - r)
      ≤ 1 / (1 / 3) := by
        apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/3)
        linarith
    _ = 3 := by norm_num


-- p ≥ 3, t ≤ α ⇒ p^(t-1) ≤ 2/3 （主項の決定版）
lemma ratio_le_two_thirds {p : ℕ} (hp3 : 3 ≤ p) {t : ℝ} (ht : t ≤ log 2 / log 3) :
  (p : ℝ) ^ (t - 1) ≤ (2:ℝ) / 3 := by
  -- (1) 底の単調：指数 ≤ 0 なら逆向き (y^z ≤ x^z for 0 < x ≤ y, z ≤ 0)
  have hexp_nonpos : t - 1 ≤ 0 := by
    have := Alpha.lt_one
    linarith
  have hbase : (p:ℝ) ^ (t - 1) ≤ (3:ℝ) ^ (t - 1) := by
    have h3_pos : 0 < (3:ℝ) := by norm_num
    have hp3_cast : (3:ℝ) ≤ (p:ℝ) := by norm_cast
    -- rpow_le_rpow_of_nonpos: (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) : y ^ z ≤ x ^ z
    exact Real.rpow_le_rpow_of_nonpos h3_pos hp3_cast hexp_nonpos
  -- (2) 指数の単調：底 ≥ 1 なので t-1 ≤ α-1 ⇒ 3^(t-1) ≤ 3^(α-1)
  have hpow : (3:ℝ) ^ (t - 1) ≤ (3:ℝ) ^ (log 2 / log 3 - 1) := by
    have : t - 1 ≤ log 2 / log 3 - 1 := by linarith
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (3:ℝ)) this
  -- (3) 3^(α-1) = 2/3
  have h3_eq : (3:ℝ) ^ (log 2 / log 3 - 1) = (2:ℝ) / 3 := Alpha.three_pow_sub_one_eq_two_thirds
  calc (p:ℝ) ^ (t - 1)
      ≤ (3:ℝ) ^ (t - 1) := hbase
    _ ≤ (3:ℝ) ^ (log 2 / log 3 - 1) := hpow
    _ = (2:ℝ) / 3 := h3_eq

-- p ≥ 3, 0 < t ≤ log 2 / log 3 ⇒ 1/(1 - p^(t-1)) ≤ 3
lemma one_div_one_sub_rpow_le_3 {p : ℕ} (hp3 : p ≥ 3) {t : ℝ}
    (ht : 0 < t) (ht_le : t ≤ log 2 / log 3) :
    1 / (1 - (p : ℝ) ^ (t - 1)) ≤ 3 := by
  have hr_le : (p : ℝ) ^ (t - 1) ≤ 2/3 := ratio_le_two_thirds hp3 ht_le
  have hr_lt_1 : (p : ℝ) ^ (t - 1) < 1 := by
    have : t - 1 < 0 := t_sub_one_neg ht ht_le
    calc (p : ℝ) ^ (t - 1)
        < (p : ℝ) ^ 0 := Real.rpow_lt_rpow_of_exponent_lt (nat_ge_3_cast_gt_one hp3) this
      _ = 1 := by simp
  exact one_div_one_sub_le_3_of_le_two_thirds hr_le hr_lt_1


-- p ≥ 3 ⇒ 1/p ≤ 1/3
lemma one_div_nat_ge_3_le_one_third {p : ℕ} (hp3 : p ≥ 3) : 1 / (p : ℝ) ≤ 1 / 3 := by
  have hp : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have h3_pos : (0 : ℝ) < 3 := by norm_num
  exact one_div_le_one_div_of_le h3_pos hp


-- p ≥ 3, 0 < t ⇒ p^t > 1
lemma rpow_t_gt_one {p : ℕ} (hp3 : p ≥ 3) {t : ℝ} (ht : 0 < t) : 1 < (p : ℝ) ^ t := by
  have hp_gt1 : 1 < (p : ℝ) := nat_ge_3_cast_gt_one hp3
  exact one_lt_rpow hp_gt1 ht


-- p ≥ 3, 0 < t ⇒ p^t - 1 > 0
lemma rpow_t_sub_one_pos {p : ℕ} (hp3 : p ≥ 3) {t : ℝ} (ht : 0 < t) : 0 < (p : ℝ) ^ t - 1 := by
  have : 1 < (p : ℝ) ^ t := rpow_t_gt_one hp3 ht
  linarith

-- 尾項の決定版：X ≥ 3 なら (2X+2)^α ≤ X+1 （α = log 2 / log 3）
lemma tail_bound_alpha_X_ge3 {X : ℕ}
  (hX : 3 ≤ X) :
  (2 * (X : ℝ) + 2) ^ (log 2 / log 3) ≤ (X : ℝ) + 1 := by
  -- X + 1 ≥ 4
  have hX1 : (4:ℝ) ≤ (X:ℝ) + 1 := by
    have : 4 ≤ X + 1 := by omega
    norm_cast
  have hα_pos := Alpha.pos
  have hα_lt1 := Alpha.lt_one
  -- 基本性質
  have hX_pos : 0 < (X:ℝ) + 1 := by
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (by norm_num)
  have hX_nonneg : 0 ≤ (X:ℝ) + 1 := le_of_lt hX_pos
  -- 2(X+1) = 2 * (X+1)
  have h2X : (2 * (X:ℝ) + 2) = 2 * ((X:ℝ) + 1) := by ring
  -- (2(X+1))^α = 2^α * (X+1)^α
  rw [h2X]
  rw [Real.mul_rpow (by norm_num : 0 ≤ (2:ℝ)) hX_nonneg]
  -- Strategy: (2(X+1))^α = 2^α * (X+1)^α ≤ (X+1)^(1-α) * (X+1)^α = X+1
  -- Use two_pow_alpha_le_xplus1_pow_one_sub_alpha for X ≥ 3
  have h_main : (2:ℝ) ^ (log 2 / log 3) ≤ ((X:ℝ) + 1) ^ (1 - log 2 / log 3) :=
    two_pow_alpha_le_xplus1_pow_one_sub_alpha hX
  -- Step 2: 2^α * (X+1)^α ≤ (X+1)^(1-α) * (X+1)^α = (X+1)^1 = X+1
  calc (2:ℝ) ^ (log 2 / log 3) * ((X:ℝ) + 1) ^ (log 2 / log 3)
      ≤ ((X:ℝ) + 1) ^ (1 - log 2 / log 3) * ((X:ℝ) + 1) ^ (log 2 / log 3) := by
        gcongr
    _ = ((X:ℝ) + 1) ^ (1 - log 2 / log 3 + log 2 / log 3) := by
        rw [← Real.rpow_add hX_pos]
    _ = (X:ℝ) + 1 := by
        ring_nf
        rw [Real.rpow_one]


-- p ≥ 3, 0 < t ⇒ p^t ≠ 1
lemma rpow_t_ne_one {p : ℕ} (hp3 : p ≥ 3) {t : ℝ} (ht : 0 < t) : (p : ℝ) ^ t ≠ 1 := by
  have : 1 < (p : ℝ) ^ t := rpow_t_gt_one hp3 ht
  linarith


-- p ≥ 3 ⇒ p^(t-1) > 0
lemma rpow_t_sub_one_pos' {p : ℕ} (hp3 : p ≥ 3) {t : ℝ} : 0 < (p : ℝ) ^ (t - 1) := by
  exact Real.rpow_pos_of_pos (nat_ge_3_cast_pos hp3) (t - 1)


/-! ### Phase 2: 補題の整備 - 尾項用の補題 -/

def X_two_mul_sum (X : ℕ) : ℕ := 2 * X + 2

-- t ≤ 1/2 ⇒ (2X+2)^t ≤ √(2X+2)
lemma rpow_t_le_sqrt {X : ℕ} {t : ℝ} (ht_half : t ≤ 1 / 2) :
    (X_two_mul_sum X) ^ t ≤ Real.sqrt (X_two_mul_sum X) := by
  have h_nonneg : 0 ≤ (X_two_mul_sum X) := by rw [X_two_mul_sum]; omega
  have h_sqrt : Real.sqrt (X_two_mul_sum X) = (X_two_mul_sum X) ^ (1 / 2 : ℝ) := by
    exact Real.sqrt_eq_rpow _
  rw [h_sqrt, X_two_mul_sum]
  have h_base : (1 : ℝ) ≤ ↑(X_two_mul_sum X) := by norm_cast; rw [X_two_mul_sum]; omega
  rw [X_two_mul_sum] at h_base
  exact Real.rpow_le_rpow_of_exponent_le h_base ht_half


-- t ≤ 1/2 ⇒ p^t ≤ √p
lemma rpow_t_le_sqrt_nat {p : ℕ} {t : ℝ} (ht_half : t ≤ 1 / 2) (hp : p ≥ 1) :
    (p : ℝ) ^ t ≤ Real.sqrt p := by
  have h_nonneg : 0 ≤ (p : ℝ) := by norm_cast; omega
  have h_sqrt : Real.sqrt p = (p : ℝ) ^ (1 / 2 : ℝ) := by
    exact Real.sqrt_eq_rpow _
  rw [h_sqrt]
  have : 1 ≤ (p : ℝ) := by norm_cast
  exact Real.rpow_le_rpow_of_exponent_le this ht_half

/-- p ≥ 3 なら √p ≤ (p+1)/2 であること。 -/
lemma sqrt_le_p_add_one_div_two {p : ℕ} (hp3 : p ≥ 3) :
    Real.sqrt (p : ℝ) ≤ ((p + 1 : ℝ) / 2) := by
  have hpos : 0 ≤ (p : ℝ) := by norm_cast; omega
  have hsq : (Real.sqrt (p : ℝ)) ^ 2 ≤ ((p + 1 : ℝ) / 2) ^ 2 := by
    -- (sqrt p)^2 = p, so this is equivalent to p ≤ ((p+1)/2)^2
    have : (p : ℝ) ≤ ((p + 1 : ℝ) / 2) ^ 2 := by
      -- (p + 1)^2 / 4 - p = (p - 1)^2 / 4 ≥ 0
      have : 0 ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith [hp3]
      nlinarith
    simpa [Real.sq_sqrt] using this
  have hpos' : 0 ≤ ((p + 1 : ℝ) / 2) := by nlinarith
  have hRHS : Real.sqrt (((p + 1 : ℝ) / 2) ^ 2) = (p + 1 : ℝ) / 2 := by
    -- sqrt(x^2) = x for x ≥ 0
    simpa using (Real.sqrt_sq hpos')
  have h_le_sqrt : Real.sqrt (p : ℝ) ≤ Real.sqrt (((p + 1 : ℝ) / 2) ^ 2) :=
    Real.le_sqrt_of_sq_le hsq
  exact le_trans h_le_sqrt hRHS.le

/-- For p ≥ 3 and t ≤ 1/2, p^t ≤ (p+1)/2. -/
lemma rpow_t_le_p_add_one_div_two {p : ℕ} {t : ℝ} (hp3 : p ≥ 3) (ht_half : t ≤ 1 / 2) :
    (p : ℝ) ^ t ≤ ((p + 1 : ℝ) / 2) := by
  have h1 : (p : ℝ) ^ t ≤ Real.sqrt (p : ℝ) := rpow_t_le_sqrt_nat ht_half (by linarith)
  have h2 : Real.sqrt (p : ℝ) ≤ ((p + 1 : ℝ) / 2) := sqrt_le_p_add_one_div_two hp3
  exact le_trans h1 h2


-- 1/2 < t ≤ log 2 / log 3, X ≥ 1 ⇒ (X+1)^(t-1) は X=1 で最大
lemma pow_t_sub_one_decreasing {X : ℕ} {t : ℝ} (hX : X ≥ 1)
    (ht_le : t ≤ log 2 / log 3) :
    (X + 1 : ℝ) ^ (t - 1) ≤ (2 : ℝ) ^ (t - 1) := by
  have ht_sub_one : t - 1 < 0 := by
    have : t ≤ log 2 / log 3 := ht_le
    have : log 2 / log 3 < 1 := log2_div_log3_lt_one
    linarith
  have h_base : (2 : ℝ) ≤ (X + 1 : ℝ) := by norm_cast; omega
  -- 指数が負で底が大きいほど値は小さい
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) h_base (by linarith)

/-- 1 - p^{t-1} を (p - p^t)/p に書き換える補題。
    p > 0 が仮定で必要。
-/
lemma one_sub_rpow_sub_one_div {p : ℝ} (hp_pos : 0 < p) (t : ℝ) :
    1 - p ^ (t - 1) = (p - p ^ t) / p := by
  have hpow : p ^ (t - 1) = p ^ t / p := by
    simpa using (Real.rpow_sub hp_pos t 1)
  calc
    1 - p ^ (t - 1)
        = 1 - (p ^ t / p) := by simp [hpow]
    _ = (p - p ^ t) / p := by field_simp [hp_pos.ne']

/-- p ≥ 3, t ≤ 1/2 のとき、
    (p^t - 1) * p^{-1} / (1 - p^{t-1}) ≤ 1 が成り立つ補題。 -/
lemma rpow_main_term_le_one {p : ℕ} [hp : Fact p.Prime] (hp3 : p ≥ 3) {t : ℝ}
    (ht_half : t ≤ 1 / 2) :
    ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) /
        (1 - (p : ℝ) ^ (t - 1)) ≤ 1 := by
  have hp_pos : 0 < (p : ℝ) := nat_ge_3_cast_pos hp3
  have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpow_le : (p : ℝ) ^ t ≤ ((p + 1 : ℝ) / 2) :=
    rpow_t_le_p_add_one_div_two hp3 ht_half
  have hpow_lt_p : (p : ℝ) ^ t < (p : ℝ) := by
    have hmid_lt : ((p + 1 : ℝ) / 2) < (p : ℝ) := by
      nlinarith [show (3 : ℝ) ≤ (p : ℝ) by exact_mod_cast hp3]
    exact lt_of_le_of_lt hpow_le hmid_lt
  have hpow_sub : (p : ℝ) ^ (t - 1) = (p : ℝ) ^ t / (p : ℝ) := by
    simpa [Real.rpow_one] using (Real.rpow_sub hp_pos t 1)
  have hden_pos : 0 < (1 - (p : ℝ) ^ (t - 1)) := by
    have h_num_pos : 0 < (p : ℝ) - (p : ℝ) ^ t := sub_pos.mpr hpow_lt_p
    have hrewrite :
        1 - (p : ℝ) ^ (t - 1) = ((p : ℝ) - (p : ℝ) ^ t) / (p : ℝ) := by
      simpa [hpow_sub] using (one_sub_rpow_sub_one_div hp_pos t)
    rw [hrewrite]
    exact div_pos h_num_pos hp_pos
  have h_num_le_den :
      ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) ≤
        1 - (p : ℝ) ^ (t - 1) := by
    have hmain : (p : ℝ) ^ t - 1 ≤ (p : ℝ) - (p : ℝ) ^ t := by
      nlinarith [hpow_le]
    have hrewrite :
        1 - (p : ℝ) ^ (t - 1) = ((p : ℝ) - (p : ℝ) ^ t) / (p : ℝ) := by
      simpa [hpow_sub] using (one_sub_rpow_sub_one_div hp_pos t)
    have hinv : (p : ℝ) ^ (-1 : ℝ) = (p : ℝ)⁻¹ := by
      -- rpow (-1) は逆数になる
      simpa using (Real.rpow_neg_one (p : ℝ))
    have hpos_inv : 0 ≤ (p : ℝ) ^ (-1 : ℝ) := by
      positivity
    have hdiv_mul :
        ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) ≤
          ((p : ℝ) - (p : ℝ) ^ t) * (p : ℝ) ^ (-1 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hmain hpos_inv
    have htmp :
        ((p : ℝ) ^ t - 1) * (p : ℝ) ^ (-1 : ℝ) ≤
          ((p : ℝ) - (p : ℝ) ^ t) / (p : ℝ) := by
      simpa [div_eq_mul_inv, hinv] using hdiv_mul
    simpa [hrewrite] using htmp
  exact (div_le_iff hden_pos).2 (by simpa using h_num_le_den)


lemma log2_div_log3_le_zero : -log 2 / log 3 ≤ 0 := by
  -- log 2 > 0, log 3 > 0 より -log 2 < 0, log 3 > 0
  have h_log2_pos : 0 < log 2 := by apply log_pos; norm_num
  have h_log3_pos : 0 < log 3 := by apply log_pos; norm_num
  -- よって -log 2 / log 3 < 0 なので ≤ 0 も成立
  exact (div_neg_of_neg_of_pos (neg_lt_zero.mpr h_log2_pos) h_log3_pos).le


lemma rpow_div {a : ℝ} {b : ℝ} (ha : 0 < a) (hb : 0 < b) (r : ℝ) :
  (a / b) ^ r = a ^ r / b ^ r := by
  -- a, b > 0 なので rpow の分配公式が使える
  rw [div_eq_mul_inv]
  have hb_inv_pos : 0 < b⁻¹ := inv_pos.mpr hb
  -- (a * b⁻¹) ^ r = a ^ r * (b⁻¹) ^ r
  rw [Real.mul_rpow (le_of_lt ha) (le_of_lt hb_inv_pos)]
  -- (b⁻¹) ^ r = (b ^ r)⁻¹ は inv_rpow で証明できる
  rw [Real.inv_rpow (le_of_lt hb) r]
  -- a ^ r * (b ^ r)⁻¹ = a ^ r / b ^ r
  rw [←div_eq_mul_inv]



end Real
