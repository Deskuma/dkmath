/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.CosmicFormulaDim  -- Cosmic Formula Dimensionality

#print "file: DkMath.CosmicFormulaBinom"

/-! ## 無次元宇宙式 Basic Dimless Cosmic Formula

### 一般化: 無次元宇宙式（d 次元完成）

差の因数分解の方程式より、以下の恒等式が導けます。

$$
f_d(x;u) = (x+u)^d - x^d - d x^{d-1} u
         = \binom{d}{2} u^2 x^{d-2} + \binom{d}{3} u^3 x^{d-3} + \cdots + u^d
$$

ここで、$d\in\mathbb{N}$ は任意の正整数です。この無次元宇宙式は、より高次の多項式に対しても同様の恒等式を提供します。

和の二項展開式表示では、

$$
f_d(x;u) = \sum_{k=2}^{d} \binom{d}{k} u^k x^{d-k}
$$

以下は Python 検証 OK

$$
Z_d(x;u) = (x+u)^d -\left( x \sum_{k=0}^{d-1} \binom{d}{k+1} u^{d-1-k} x^k \right) = u^d
$$
-/

namespace DkMath.CosmicFormulaBinom

open scoped BigOperators

-- ----------------------------------------------------------------------------
-- 減算形の恒等式 (CommRing)
-- ----------------------------------------------------------------------------

section CommRing

/-! ### 無次元版: G と Z_d の定義と恒等式の証明 -/

/-- d 次元の「無次元実体項」G の定義（係数は Nat.choose を射影したもの） -/
def G {R : Type _} [CommRing R] (d : ℕ) (x u : R) : R :=
    ∑ k ∈ Finset.range d, (Nat.choose d (k + 1) : R) * x ^ k * u ^ (d - 1 - k)

/-- d 次元の「無次元実体項」G の定義（係数は Nat.choose を射影したもの） -/
theorem cosmic_id {R : Type _} [CommRing R] (d : ℕ) (x u : R) :
        (x + u) ^ d - x * G d x u = u ^ d := by
    unfold G
    rw [add_pow, Finset.mul_sum]
    -- 二項展開を k=0 項と k≥1 項に分ける（項の順序を `add_pow` の出力に合わせる）
    have h1 : ∑ k ∈ Finset.range (d + 1), x ^ k * u ^ (d - k) * (Nat.choose d k : R)
      = x ^ 0 * u ^ d * (Nat.choose d 0 : R)
      + ∑ k ∈ Finset.range d, x ^ (k + 1) * u ^ (d - 1 - k) * (Nat.choose d (k + 1) : R) := by
        rw [Finset.sum_range_succ']
        simp only [pow_zero, Nat.sub_zero]
        rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        congr 2
        have hk' : k < d := Finset.mem_range.mp hk
        have hss : k + 1 ≤ d := Nat.succ_le_of_lt hk'
        have h2 : d - (k + 1) = d - k - 1 := Nat.sub_sub d k 1
        have h3 : d - k - 1 = d - 1 - k := by omega
        rw [h2, h3]
    -- x * G を展開すると h1 の第2項と一致する（項順序を合わせる）
    have h2 : ∑ k ∈ Finset.range d, x * ((Nat.choose d (k + 1) : R) * x ^ k * u ^ (d - 1 - k))
      = ∑ k ∈ Finset.range d, x ^ (k + 1) * u ^ (d - 1 - k) * (Nat.choose d (k + 1) : R) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
    rw [h1, h2]
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
    ring

/-- 無次元 Z_d の定義:
LaTeX:
Z_d(x;u) = (x+u)^d -\left( x \sum_{k=0}^{d-1} \binom{d}{k+1} u^{d-1-k} x^k \right) -u^d
-/
def Z {R : Type _} [CommRing R] (d : ℕ) (x u : R) : R :=
    (x + u) ^ d - (x * G d x u) - u ^ d

/-- Z_d は恒等的に 0 である -/
theorem Z_eq_zero {R : Type _} [CommRing R] (d : ℕ) (x u : R) : Z d x u = 0 := by
    unfold Z
    have h := cosmic_id d x u
    rw [h]
    simp

/-! ### f_d の定義と二項展開による表現 -/

/-- d 次の無次元多項式 f の定義: k=0,1 の項を除いた二項和 -/
def f {R : Type _} [CommRing R] (d : ℕ) (x u : R) : R :=
    (∑ k ∈ Finset.range (d + 1), (Nat.choose d k : R) * x ^ k * u ^ (d - k))
    - (Nat.choose d 0 : R) * x ^ 0 * u ^ d
    - (Nat.choose d 1 : R) * x ^ 1 * u ^ (d - 1)

/-! f は二項展開から (x+u)^d - u^d - (choose d 1) * x * u^(d-1) に等しい -/
theorem f_eq_pow_sub {R : Type _} [CommRing R] (d : ℕ) (x u : R) :
        f d x u = (x + u) ^ d - u ^ d - (Nat.choose d 1 : R) * x * u ^ (d - 1) := by
    unfold f
    rw [add_pow]
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
    have hsum : ∑ k ∈ Finset.range (d + 1), (Nat.choose d k : R) * x ^ k * u ^ (d - k) =
        ∑ k ∈ Finset.range (d + 1), x ^ k * u ^ (d - k) * ↑(d.choose k) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
    rw [hsum]
    simp

/-- 無次元版: R の定義 -/
def R (d : ℕ) (x u : ℝ) : ℝ := (x + u) ^ d - u ^ d - (Nat.choose d 1 : ℝ) * x * u ^ (d - 1)

#eval R 3 2 1  -- 20
#eval R 4 2 1  -- 72
#eval R 5 2 1  -- 232
#eval R 6 2 1  -- 716

/-- f は無次元宇宙式の関係式に等しい -/
theorem f_eq_relation {R : Type _} [CommRing R] (d : ℕ) (x u : R) :
    f d x u = x * (G d x u - (Nat.choose d 1 : R) * u ^ (d - 1)) := by
    rw [f_eq_pow_sub]
    have h := cosmic_id d x u
    rw [←h]
    simp
    ring

-- ----------------------------------------------------------------------------
-- 恒等式の同値変形 (iff)
-- ----------------------------------------------------------------------------

/-- 無次元宇宙式の恒等式の同値変形: f_eq_zero_iff -/
lemma f_eq_zero_iff {R : Type _} [CommRing R] (d : ℕ) (x u : R) :
    f d x u = 0 ↔ x * (G d x u - (Nat.choose d 1 : R) * u ^ (d - 1)) = 0 := by
    rw [f_eq_relation]

/-- 無次元宇宙式の恒等式の同値変形: dim_G_iff (加法形) -/
lemma dim_G_iff (d : ℕ) (x u : ℝ) :
    (x + u) ^ d = x * DkMath.CosmicFormulaDim.G d x u + u ^ d
        ↔ (x + u) ^ d = x * G d x u + u ^ d := by
    simp [DkMath.CosmicFormulaDim.G, G]

end CommRing

-- ----------------------------------------------------------------------------
-- 無減算形の恒等式 (CommSemiring)
-- ----------------------------------------------------------------------------

section CommSemiring

/-- d 次元の「無次元実体項」G (CommSemiring) の定義（係数は Nat.choose を射影したもの） -/
def G' {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) : R :=
    ∑ k ∈ Finset.range d, (Nat.choose d (k + 1) : R) * x ^ k * u ^ (d - 1 - k)

/-! 無減算形の恒等式: (x+u)^d = x * G d x u + u^d (CommSemiring) -/
theorem cosmic_id' {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) :
        (x + u) ^ d = x * G' d x u + u ^ d := by
    unfold G'
    rw [add_pow, Finset.mul_sum]
    -- 二項展開を k=0 項と k≥1 項に分ける（項の順序を `add_pow` の出力に合わせる）
    have h1 : ∑ k ∈ Finset.range (d + 1), x ^ k * u ^ (d - k) * (Nat.choose d k : R)
        = x ^ 0 * u ^ d * (Nat.choose d 0 : R)
            + ∑ k ∈ Finset.range d, x ^ (k + 1) * u ^ (d - 1 - k) * (Nat.choose d (k + 1) : R) := by
        rw [Finset.sum_range_succ']
        simp only [pow_zero, Nat.sub_zero]
        rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        congr 2
        have hk' : k < d := Finset.mem_range.mp hk
        have hss : k + 1 ≤ d := Nat.succ_le_of_lt hk'
        have h2 : d - (k + 1) = d - k - 1 := Nat.sub_sub d k 1
        have h3 : d - k - 1 = d - 1 - k := by omega
        rw [h2, h3]
    -- x * G を展開すると h1 の第2項と一致する（項順序を合わせる）
    have h2 : ∑ k ∈ Finset.range d, x * ((Nat.choose d (k + 1) : R) * x ^ k * u ^ (d - 1 - k))
        = ∑ k ∈ Finset.range d, x ^ (k + 1) * u ^ (d - 1 - k) * (Nat.choose d (k + 1) : R) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
    -- 以上の等式から二項展開の和が x*G + u^d に一致する
    rw [h1, h2]
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
    ring

end CommSemiring

end DkMath.CosmicFormulaBinom
