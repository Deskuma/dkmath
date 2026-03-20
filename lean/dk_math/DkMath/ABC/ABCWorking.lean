/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC

set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.style.emptyLine false

#check ABC.rad

-- padicValNat_odd_prime_ge_two

namespace ABC

namespace Nat


-- Nat.even の定義を追加
/-- 自然数 `n` が偶数であることを表す述語 `even n` の定義。 -/
def even (n : ℕ) : Prop := n % 2 = 0
-- Nat.odd の定義を追加
/-- 自然数 `n` が奇数であることを表す述語 `odd n` の定義。 -/
def odd (n : ℕ) : Prop := n % 2 = 1


/--
`odd_iff_not_even` は、
自然数 `n` に対して「`n` が奇数であること」と「`n` が偶数でないこと」が同値である。
ということを示す補題です。

証明の概要:
- 奇数 (`odd n`) は `n % 2 = 1`、偶数 (`even n`) は `n % 2 = 0` で定義されています。
- まず、`n` が奇数ならば偶数ではないこと（`n % 2 = 1 → ¬ (n % 2 = 0)`）を示します。
  `n % 2 = 1` ならば `n % 2 = 0` とはならないので、矛盾します。
- 次に、`n` が偶数でないならば奇数であること（`¬ (n % 2 = 0) → n % 2 = 1`）を示します。
  `n % 2` は常に `0` または `1` なので、`0` でないなら必ず `1` です。

この補題は、偶奇判定の基本的な性質を形式的に証明しています。
-/

lemma odd_iff_not_even {n : ℕ} : odd n ↔ ¬ even n := by
  rw [even, odd]
  -- n % 2 = 1 ↔ ¬ (n % 2 = 0)
  constructor
  · -- (→) odd n → ¬ even n
    intro h heven
    rw [h] at heven
    -- h : n % 2 = 1, heven : n % 2 = 0
    linarith
  · -- (←) ¬ even n → odd n
    intro hne
    cases Nat.mod_two_eq_zero_or_one n with
    | inl h0 =>
      -- n % 2 = 0 の場合 even n なので ¬ even n は false
      exfalso
      apply hne
      exact h0
    | inr h1 =>
      -- n % 2 = 1 の場合 odd n
      exact h1


/--
`eq_two_of_even_prime` は、
自然数 `p` が素数かつ偶数である場合に `p = 2` であることを示す補題です。

数学的背景:
- 素数の定義より、`p` は 2 以上の自然数です。
- 2 より大きい素数は必ず奇数であり、偶数の素数は 2 のみです。
- `even p` より `p % 2 = 0` となるが、素数で 2 で割り切れるものは 2 しかありません。

証明の流れ:
1. `p` が偶数であることから `p % 2 = 0` または `p % 2 = 1` の場合分けをします。
2. `p % 2 = 0` の場合、`p` は 2 で割り切れる素数なので `p = 2` です。
3. `p % 2 = 1` の場合は `p` が偶数であることと矛盾します。

この補題は、偶数の素数が 2 のみであることを形式的に証明します。
-/

lemma eq_two_of_even_prime {p : ℕ} (hp : p.Prime) (heven : even p) : p = 2 := by
  -- 素数かつ偶数ならば p = 2 しかない
  rw [even] at heven
  -- 素数 p > 2 は必ず奇数なので、偶数素数は p = 2 のみ
  have hcases := Nat.mod_two_eq_zero_or_one p
  cases hcases with
  | inl h0 =>
    -- p % 2 = 0 かつ p は素数なので p = 2
    have hpos : 0 < p := hp.pos
    -- p ≠ 1 なので p ≥ 2
    have hge2 : 2 ≤ p := hp.two_le
    -- 2 で割り切れる素数は 2 のみ
    have hdiv : 2 ∣ p := Nat.dvd_of_mod_eq_zero h0
    rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hp] at hdiv
    exact Eq.symm hdiv
  | inr h1 =>
    -- p % 2 = 1 の場合は偶数ではないので矛盾
    exfalso
    rw [h1] at heven
    linarith


-- -------------------------------------------------------


/--
`odd_add_one_of_even` は、
自然数 `n` が偶数であるとき、`n + 1` が奇数であることを示す補題です。

数学的背景:
偶数とは、2で割り切れる整数（`n % 2 = 0`）です。奇数とは、2で割った余りが1になる整数（`n % 2 = 1`）です。
この補題では、`n` が偶数である（`even n`）という仮定から、`n + 1` が奇数（`odd (n + 1)`）であることを導きます。

証明の流れ:
1. `even n` の定義より、`n % 2 = 0` であることを仮定します。
2. `odd (n + 1)` の定義より、`(n + 1) % 2 = 1` を示します。
3. 加法の合同式 `Nat.add_mod` を用いて、`(n + 1) % 2 = (n % 2 + 1 % 2) % 2` であることを示します。
4. `n % 2 = 0` を代入し、`(0 + 1) % 2 = 1` となるため、`n + 1` は奇数です。

この補題は、偶数と奇数の性質に基づく基本的な事実を Lean で形式化したものです。
-/

lemma odd_add_one_of_even {n : ℕ} (heven : even n) : odd (n + 1) := by
  -- n が偶数ならば n + 1 は奇数
  rw [even] at heven
  rw [odd]
  -- (n + 1) % 2 = 1 を示す
  have hmod : (n + 1) % 2 = (n % 2 + 1 % 2) % 2 := by
    rw [Nat.add_mod]
  rw [hmod]
  rw [heven]


/--
`even_mul_left` 補題は、自然数 `a` が偶数であるとき、
任意の自然数 `b` に対して積 `a * b` も偶数であることを示します。

証明の流れ:
- `a` が偶数であることから、`a % 2 = 0` である。
- 積の剰余 `(a * b) % 2` は、`(a % 2) * (b % 2) % 2` と書ける（`Nat.mul_mod` より）。
- `a % 2 = 0` なので、`(a * b) % 2 = (0 * (b % 2)) % 2 = 0 % 2` となる。
- `0 % 2 = 0` であるため、`a * b` も偶数となる。

この補題は、偶数の性質を積に関して拡張する際に有用です。
-/

lemma even_mul_left {a b : ℕ} (heven : even a) : even (a * b) := by
  -- a が偶数ならば a * b も偶数
  rw [even] at heven
  rw [even]
  -- (a * b) % 2 = 0 を示す
  have hmod : (a * b) % 2 = ((a % 2) * (b % 2)) % 2 := by
    rw [Nat.mul_mod]
  rw [hmod]
  rw [heven]
  -- 0 * (b % 2) = 0
  rw [zero_mul]
  -- 0 % 2 = 0 を Nat.zero_mod で証明
  exact Nat.zero_mod 2


-- 2n+1 の形の数に関する補題

-- 2n+1 の形の数は奇数であることを示す補題です。
/--
`odd_of_form_two_n_plus_one` は、
任意の自然数 `n` に対して `2 * n + 1` の形の数が奇数であることを証明する補題です。

数学的には、`2n + 1` の形の数は常に奇数です。
これは、`2n` が偶数であり、そこに 1 を加えることで奇数になるためです。
証明では、`odd` の定義（`n % 2 = 1`）を用いて、`(2 * n + 1) % 2` を計算します。
加法の合同式 `Nat.add_mod` を使い、`2n % 2 = 0` と `1 % 2 = 1` を利用して、
最終的に `(0 + 1) % 2 = 1` となることを示しています。

この補題は、奇数の性質や合同式の計算の理解に役立ちます。
-/

lemma odd_of_form_two_n_plus_one (n : ℕ) : odd (2 * n + 1) := by
  -- 2n + 1 の形の数は奇数であることを示す
  rw [odd]
  -- (2n + 1) % 2 = 1 を示す
  have hmod : (2 * n + 1) % 2 = ((2 * n) % 2 + 1 % 2) % 2 := by
    rw [Nat.add_mod]
  rw [hmod]
  -- 2n % 2 = 0, 1 % 2 = 1 なので (0 + 1) % 2 = 1
  have h2n : (2 * n) % 2 = 0 := Nat.mul_mod_right _ _
  have h1 : 1 % 2 = 1 := by norm_num
  rw [h2n, h1]


-- odd n * odd m = odd (n * m) の形の補題です。
/--
`odd_mul_odd` 補題は、
2つの自然数 `n` と `m` がともに奇数であるとき、その積 `n * m` も奇数であることを示します。

証明の概要:
- `odd n` および `odd m` の仮定から、それぞれ `n % 2 = 1` および `m % 2 = 1` が成り立ちます。
- 積の剰余 `(n * m) % 2` は、`(n % 2) * (m % 2) % 2` と等しいことを利用します。
- したがって、`(n * m) % 2 = (1 * 1) % 2 = 1` となり、`n * m` も奇数です。

この補題は、奇数の積が必ず奇数になるという基本的な性質を形式的に証明しています。
-/

lemma odd_mul_odd (n m : ℕ) (hn : odd n) (hm : odd m) : odd (n * m) := by
  -- n, m が奇数ならば n * m も奇数
  rw [odd] at hn hm
  rw [odd]
  -- (n * m) % 2 = 1 を示す
  have hmod : (n * m) % 2 = ((n % 2) * (m % 2)) % 2 := by
    rw [Nat.mul_mod]
  rw [hmod]
  rw [hn, hm]


-- 3n + 1 の形の数に関する補題
/-
`odd_of_form_three_n_plus_one` は、
任意の自然数 `n` に対して `3 * n + 1` の形の数が偶数・奇数を反転させることを証明する補題です。
-/
/--
`odd_of_form_three_n_plus_one` は、
自然数 `n` に対して `3n + 1` の形の数が奇数であることと、`n` が偶数であることが同値であることを示す補題です。

具体的には、`odd (3 * n + 1) ↔ even n` を証明しています。

証明の流れ：
- `odd` と `even` の定義から、`(3 * n + 1) % 2 = 1 ↔ n % 2 = 0` を示します。
- まず、`odd (3 * n + 1)` ならば `n` が偶数であることを示します。
  - 加法・乗法の合同式を用いて、`(3 * n + 1) % 2` を分解します。
  - `n % 2` が 0 か 1 かで場合分けし、1 の場合は矛盾が生じることを示します。
- 次に、`n` が偶数ならば `3n + 1` が奇数であることを示します。
  - 同様に合同式を用いて計算し、`n % 2 = 0` から `3n + 1` が奇数となることを導きます。

この補題は、数論的な性質の証明や、合同式を用いた場合分けの典型例として有用です。
-/

lemma odd_of_form_three_n_plus_one (n : ℕ) : odd (3 * n + 1) ↔ even n := by
  -- 3n + 1 の形の数が奇数であることと n が偶数であることは同値
  rw [odd, even]
  -- (3n + 1) % 2 = 1 ↔ n % 2 = 0 を示す
  constructor
  · -- (→) odd (3n + 1) → even n
    intro h
    have hmod : (3 * n + 1) % 2 = ((3 * n) % 2 + 1 % 2) % 2 := by
      rw [Nat.add_mod]
    rw [hmod] at h
    -- (3n) % 2 + 1 % 2 ≡ 1 (mod 2)
    have h3n_mod : (3 * n) % 2 = (3 % 2 * (n % 2)) % 2 := by rw [Nat.mul_mod]
    rw [h3n_mod] at h
    -- (n % 2 * 1 + 1) % 2 = 1
    have h1 : 1 % 2 = 1 := by norm_num
    rw [h1] at h
    -- (n % 2 + 1) % 2 = 1
    -- h : (1 * (n % 2) % 2 + 1) % 2 = 1 から (n % 2 + 1) % 2 = 1 を導く
    have hsum : (n % 2 + 1) % 2 = 1 := by
      -- (1 * (n % 2) % 2 + 1) % 2 = ((n % 2) % 2 + 1) % 2
      rw [one_mul, Nat.mod_mod] at h
      exact h
    -- n % 2 = 0 を示す
    have hcases := Nat.mod_two_eq_zero_or_one n
    cases hcases with
    | inl h0 =>
      -- n % 2 = 0 の場合 even n
      exact h0
    | inr h1 =>
      -- n % 2 = 1 の場合は矛盾
      exfalso
      rw [h1] at hsum
      -- (1 + 1) % 2 = 0 ≠ 1 矛盾
      have hcontradict : (1 + 1) % 2 = 0 := by norm_num
      rw [hcontradict] at hsum
      linarith
  · -- (←) even n → odd (3n + 1)
    intro h
    have hmod : (3 * n + 1) % 2 = ((3 * n) % 2 + 1 % 2) % 2 := by
      rw [Nat.add_mod]
    have h3n_mod : (3 * n) % 2 = (3 % 2 * (n % 2)) % 2 := by
      rw [Nat.mul_mod]
    have h3 : 3 % 2 = 1 := by norm_num
    have h0 : n % 2 = 0 := h
    calc
      (3 * n + 1) % 2
          = ((3 * n) % 2 + 1 % 2) % 2 := hmod
      _ = ((3 % 2 * (n % 2)) % 2 + 1) % 2 := by rw [h3n_mod]
      _ = ((1 * (n % 2)) % 2 + 1) % 2 := by rw [h3]
      _ = ((n % 2) % 2 + 1) % 2 := by ring_nf
      _ = ((0 : ℕ) % 2 + 1) % 2 := by rw [h0]
      _ = (0 + 1) % 2 := by norm_num
      _ = 1 := by norm_num


/--
`padicValNat_le_iff_dvd` は、素数 `p` と 0 でない自然数 `n`、および自然数 `k` に対して、
`k ≤ padicValNat p n` と `p ^ k ∣ n` が同値であることを示す補題です。

ここで `padicValNat p n` は、`n` の `p` 進指数（`p` で割り切れる最大のべき指数）を表します。
つまり、`n` が `p^k` で割り切れることと、`n` の `p` 進指数が `k` 以上であることは同値です。

証明では、`mathlib4` の `padicValNat_dvd_iff_le` を型クラスインスタンス `[Fact p.Prime]` を明示的に与えて利用しています。
-/
lemma padicValNat_le_iff_dvd {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (k : ℕ) :
  k ≤ padicValNat p n ↔ p ^ k ∣ n := by
  -- mathlib4 の padicValNat_dvd_iff_le は [Fact p.Prime] instance を typeclass で要求する
  exact Iff.symm (@padicValNat_dvd_iff_le p (Fact.mk hp) n k hn)
  -- padicValNat_dvd_iff_le : p ^ k ∣ n ↔ k ≤ padicValNat p n
  -- Iff.symm で向きを変える(k ≤ padicValNat p n ↔ p ^ k ∣ n)
  -- Fact.mk hp で Fact p.Prime のインスタンスを明示的に与える（※ここが Mathlib の仮定と異なるところ）
  -- padicValNat_dvd_iff_le は n ≠ 0 の仮定も必要なので hn も与える


/--
`eq_zero_of_mul_eq_zero_left` は、自然数 `a` と `b` に対して、積 `a * b = 0` ならば `a = 0` または `b = 0` が成り立つことを示す補題です。
この性質は自然数の積に関する基本的な性質であり、積が 0 になるためには、少なくとも一方が 0 である必要があります。
証明では、`Nat.mul_eq_zero` の同値変形を利用して、仮定から直接結論を導いています。
-/
lemma eq_zero_of_mul_eq_zero_left {a b : ℕ} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  -- a * b = 0 ならば a = 0 または b = 0
  rw [Nat.mul_eq_zero] at h
  exact h


/--
`padicValNat_odd_prime_ge_two` は、奇素数 `p` と自然数 `n` に対して、`padicValNat p n ≥ 2` となる状況が非常に稀であることを示唆する補題です。

この補題の前提は以下の通りです：
- `p` は素数 (`p.Prime`)
- `p` は 2 ではない（奇素数）(`p ≠ 2`)
- `n` は 0 ではない (`n ≠ 0`)

`padicValNat p n ≥ 2` であれば、`p^2` が `n` を割り切ることになります。しかし、`p` が奇素数（すなわち `p ≥ 3`）である場合、一般的な `n` に対して `p^2 ∣ n` が成立することは稀です。したがって、追加の仮定（例えば、`n` の形が特定されている場合など）がなければ、矛盾を導くには十分な情報がありません。

この補題は、より具体的な `n` の構造に関する仮定が必要であることを示しています。
-/
lemma padicValNat_odd_prime_ge_two {p n : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) (hn : n ≠ 0) : 2 ≤ padicValNat p n → False := by
  -- For an odd prime p and general n, padicValNat p n ≥ 2 is rare.
  -- We show this leads to a contradiction under specific constraints.
  intro hge2
  -- If padicValNat p n ≥ 2, then p^2 divides n
  have hdiv : p ^ 2 ∣ n := (padicValNat_le_iff_dvd hp hn 2).mp hge2
  -- p is odd (p ≠ 2 and p prime), so p ≥ 3
  have hp_ge_3 : 3 ≤ p := by
    have : 2 < p := Nat.lt_of_le_of_ne hp.two_le (Ne.symm hpodd)
    omega
  -- For general n without specific structure (like n = 2m+1 exactly),
  -- p^2 ∣ n is unlikely to hold. This lemma would require more specific hypotheses
  -- about n (e.g., n is odd in a specific form) to derive a contradiction.
  -- For now, we acknowledge that the proof requires additional structure.
  sorry

end Nat

end ABC
