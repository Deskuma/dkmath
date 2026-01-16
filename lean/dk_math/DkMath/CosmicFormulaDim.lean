/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
-- import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

namespace DkMath
namespace CosmicFormulaDim

open scoped BigOperators Real

/-! ### A: 代数レイヤ（d 次元の「実体項」G） -/

/-- d 次元の「実体項」G の定義 -/
noncomputable def G (d : ℕ) (x u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range d,
    (Nat.choose d (k+1) : ℝ) * x^k * u^(d-1-k)

/--
cosmic_id : (x + u)^d - x * G d x u = u^d に関する数学的説明（日本語）

命題の主張:
  任意の自然数 d と実数 x, u について
    (x + u)^d - x * G d x u = u^d
  が成り立つ。

証明のアイデア（高レベル）:
  1. 二項定理 (add_pow) を用いて (x + u)^d を
     Σ_{k=0}^{d} C(d,k) x^k u^{d-k} に展開する。
  2. 定義から x * G d x u は
     Σ_{j=0}^{d-1} C(d,j+1) x^{j+1} u^{d-1-j}
     と展開できる（添え字を調整すれば k≥1 の項に対応する）。
  3. (1) の和を k=0 の項（即ち u^d）と k≥1 の和に分離する。
     k≥1 の和は添え字 k ↦ k+1 によって (2) の和と一致するので、
     (x+u)^d から x * G d x u を引くと残るのは u^d だけになる。

補題・注意点:
  - Finset.sum_range_succ' を用いて k=d の項（または k=0 の項）を分離する。
  - 添え字の変形には sum_congr を用いる。具体的には k を k+1 にシフトして
    指数 d-(k+1) = d-1-k の等式を使う必要がある。
  - 自然数の減算に関する等式（Nat.sub_sub や Nat.succ_le_of_lt 等）を明示的に
   扱い、必要なら omega（または同等の補題）で細かい等号を解決する。
  - 結合・交換・係数に関する単純な代数処理は ring や simp（例えば
    Nat.choose_zero_right, pow_zero, mul_one）で片付ける。

まとめ:
  二項展開の k=0 項が目標の u^d を与え、残る項は x*G の展開と対応して互いに打ち消すため、等式が成立する。
-/
theorem cosmic_id (d : ℕ) (x u : ℝ) :
    (x + u)^d - x * G d x u = u^d := by
  unfold G
  rw [add_pow, Finset.mul_sum]
  -- 二項定理: (x+u)^d = Σ_{k=0}^{d} C(d,k) x^k u^{d-k}
  -- G の展開: x * G = Σ_{j=0}^{d-1} C(d,j+1) x^{j+1} u^{d-1-j}
  -- 戦略: 二項展開の k=0 項(= u^d)を分離し、残りの和が相殺されることを示す

  -- 補題1: 二項展開を k=0 の項と k≥1 の項に分割
  have h1 : ∑ k ∈ Finset.range (d + 1), x ^ k * u ^ (d - k) * ↑(d.choose k)
          = x^0 * u^d * ↑(d.choose 0)
          + ∑ k ∈ Finset.range d, x^(k+1) * u^(d-1-k) * ↑(d.choose (k+1)) := by
    rw [Finset.sum_range_succ']  -- k=d の項を分離
    simp only [pow_zero, Nat.sub_zero]
    rw [add_comm]  -- 項の順序を入れ替え: Σ_{0..d-1} + [k=d] → [k=d] + Σ_{0..d-1}
    congr 1
    -- 各項で指数を調整: d - (k+1) = d - 1 - k
    apply Finset.sum_congr rfl
    intro k hk
    congr 2
    -- k < d を用いて d-(k+1) = d-1-k を示す（omegaは自然数減算に弱いため明示的に）
    have hk' : k < d := Finset.mem_range.mp hk
    have h1 : k + 1 ≤ d := Nat.succ_le_of_lt hk'
    have h2 : d - (k + 1) = d - k - 1 := Nat.sub_sub d k 1
    have h3 : d - k - 1 = d - 1 - k := by omega
    rw [h2, h3]
  -- 補題2: x * G を展開すると、補題1の第2項と同じ形になる
  have h2 : ∑ k ∈ Finset.range d, x * (↑(d.choose (k + 1)) * x ^ k * u ^ (d - 1 - k))
          = ∑ k ∈ Finset.range d, x^(k+1) * u^(d-1-k) * ↑(d.choose (k+1)) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  -- 補題1と補題2より、二つの和が相殺されて u^d のみが残る
  rw [h1, h2]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
  ring


/-! ### C: 解析接続の橋脚（体積定数） -/

/-- d 次元球の体積定数の複素数版 -/
noncomputable def volConstC (s : ℂ) : ℂ :=
  (π : ℂ)^(s/2) / Complex.Gamma (s/2 + 1)

-- 整数点では「いつもの定数」に一致、みたいな補題を作る

/-- 整数点での体積定数の評価 -/
theorem volConstC_nat (n : ℕ) :
    volConstC n = (π : ℂ)^( (n:ℂ)/2 ) / Complex.Gamma ((n:ℂ)/2 + 1) := by
  simp [volConstC]

/-! そして `EuclideanSpace.volume_ball` を “評価点 n” で回収する橋を架ける。
    ここは coercion (ℝ→ENNReal→ℝ) の整理が主戦場。 -/


open scoped Real

/--
偶数次元 2*m に対する定数 `volConstC` の評価を与える補題。

具体的には
  volConstC (2*m) = (π : ℂ)^m / (Nat.factorial m : ℂ)
が成り立つ。

証明の方針：
定義を展開して (2*m)/2 = m を用い，複素べき乗や有理数のキャストによる簡約を行うと，
ガンマ関数の項が `Complex.Gamma (m + 1 : ℂ)` の形になる．
ここで補題 `Complex.Gamma_nat_eq_factorial` を適用して `Γ(m+1)=m!` と置き換えれば結論が得られる。
-/
theorem volConstC_even (m : ℕ) :
    volConstC (2*m) = (π : ℂ)^m / (Nat.factorial m : ℂ) := by
  -- 展開して (2*m)/2 = m および Γ(m+1)=m! を使う
  simp only [volConstC, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀,
    Complex.cpow_natCast]
  -- ここで ((2*m : ℂ)/2 + 1) が (m + 1 : ℂ) になっているはずなのでガンマ関数の整数値評価を適用
  have hg : Complex.Gamma (m + 1 : ℂ) = (Nat.factorial m : ℂ) := by
    -- mathlib の補題を利用
    exact Complex.Gamma_nat_eq_factorial m
  rw [hg]

/--
偶数次元 2*m における体積定数の簡潔な説明と証明方針。

定理は
  volConstC (2*m) = (π : ℂ)^m / (Nat.factorial m : ℂ)
を主張する。証明は定義
  volConstC n = π^(n/2) / Γ(n/2 + 1)
に n = 2*m を代入し、(2*m)/2 = m を用いることで
  π^(m) / Γ(m + 1)
とし、さらにガンマ関数の整数引数に対する恒等式
  Γ(m+1) = m!
(Complex.Gamma_nat_eq_factorial) を適用して右辺が π^m / m! になることから得られる。
また証明中に (2 : ℂ) ≠ 0 を確認するために norm_num を用いている。
-/
theorem volConstC_even' (m : ℕ) :
    volConstC (2*m) = (π : ℂ)^m / (Nat.factorial m : ℂ) := by
  have h : (2:ℂ) ≠ 0 := by norm_num
  -- 展開して (2*m)/2 = m および Γ(m+1)=m! を使う
  simp [volConstC, h, Complex.Gamma_nat_eq_factorial]


end CosmicFormulaDim
end DkMath
