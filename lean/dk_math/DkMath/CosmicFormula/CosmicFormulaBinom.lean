/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.Algebra.BinomTail
import DkMath.CosmicFormula.Defs
import DkMath.CosmicFormula.CosmicFormulaDim  -- Cosmic Formula Dimensionality

#print "file: DkMath.CosmicFormula.CosmicFormulaBinom"

set_option linter.style.longLine false

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

ゆえに

$$
Z_d(x;u) = (x+u)^d -\left( x \sum_{k=0}^{d-1} \binom{d}{k+1} u^{d-1-k} x^k \right) - u^d = 0
$$

-/

namespace DkMath.CosmicFormulaBinom

open scoped BigOperators

-- ----------------------------------------------------------------------------
-- 減算形の恒等式 (CommRing)
-- ----------------------------------------------------------------------------

section CommRing

/-! ### 無次元版: G と Z_d の定義と恒等式の証明

[GNZC] Migration note:
this `CommRing` section still exposes the legacy name `G`.
Canonical naming is being centralized as `Defs.GZ`, so downstream comments and
new code should prefer `GZ` when referring to the Body-normalized kernel.
-/

/-- d 次元の「無次元実体項」G の定義（係数は Nat.choose を射影したもの）.

[GNZC] Legacy public name in the `CommRing` layer.
Long term this vocabulary should align with `Defs.GZ`.
-/
def G {R : Type _} [CommRing R] (d : ℕ) (x u : R) : R :=
    ∑ k ∈ Finset.range d, (Nat.choose d (k + 1) : R) * x ^ k * u ^ (d - 1 - k)

/-- 無次元版: Big の定義 -/
def Big {R : Type _} [CommRing R] (d : ℕ) (x u : R) : R := (x + u) ^ d

/-- 無次元版: Gap の定義 -/
def Gap {R : Type _} [CommRing R] (d : ℕ) (u : R) : R := u ^ d

/-- 無次元版: Body の定義 -/
def Body {R : Type _} [CommRing R] (d : ℕ) (x u : R) : R := x * G d x u

/--
`CommRing` legacy kernel `G` and canonical `Defs.GZ` differ by one boundary factor `x`.

[GNZC] This is the key bridge showing why `CommRing.G` cannot be replaced by a
mere alias of `Defs.GZ`: `G` is the pre-normalized kernel, while `GZ` is the
Body-normalized kernel.
-/
theorem mul_G_eq_GZ {R : Type _} [CommRing R] (d : ℕ) (x u : R) :
    x * G d x u = DkMath.CosmicFormula.GZ R x u d := by
  unfold G DkMath.CosmicFormula.GZ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [DkMath.CosmicFormula.d1k, DkMath.CosmicFormula.d_sub_one_k, DkMath.CosmicFormula.d_sub_n_k]
  ring

/--
`CommRing` Body is exactly the canonical `Defs.GZ` kernel.

[GNZC] New code that only needs the Body-normalized side should use this bridge
instead of referring to the legacy `G` spelling.
-/
theorem Body_eq_GZ {R : Type _} [CommRing R] (d : ℕ) (x u : R) :
    Body d x u = DkMath.CosmicFormula.GZ R x u d := by
  simp [Body, mul_G_eq_GZ]

/-- 無次元版: Big は Body と Gap の和に等しい。

[GNZC] Via `Body_eq_GZ`, this is also the canonical Body-normalized identity
`Big = GZ + Gap` in the `CommRing` layer.
-/
theorem big_is_body_and_gap {R : Type _} [CommRing R] (d : ℕ) (x u : R) :
    Big d x u = Body d x u + Gap d u := by
    unfold Big Body Gap G
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

/-- 無次元宇宙式に対する恒等式：
`CommRing` 上で任意の `d, x, u` について
`(x + u) ^ d - x * G d x u = u ^ d` が成り立つことを示す定理。

[GNZC] Using `Body_eq_GZ`, the same statement can be read as
`(x + u)^d - GZ = u^d`.
-/
theorem cosmic_id {R : Type _} [CommRing R] (d : ℕ) (x u : R) :
    Big d x u - Body d x u = Gap d u := by
    unfold Big Body Gap G
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

/-- `[GNZC]` Thin corollary form of `cosmic_id`, still phrased through `Body`.
Use `Body_eq_GZ` if a downstream theorem wants the canonical `GZ` spelling. -/
@[simp]
theorem cosmic_formula_binom {R : Type _} [CommRing R] (d : ℕ) (x u : R) :
        (x + u) ^ d - (Body d x u) = u ^ d := by
        simpa using cosmic_id d x u

/-- `[GNZC]` Legacy duplicate of `cosmic_formula_binom`.
Kept for compatibility while docstrings and theorem names are normalized. -/
theorem cosmic_id' {R : Type _} [CommRing R] (d : ℕ) (x u : R) :
        (x + u) ^ d - (Body d x u) = u ^ d := by
    unfold Body G
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
    (x + u) ^ d - (Body d x u) - u ^ d

def Z' {R : Type _} [CommRing R] (d : ℕ) (x u : R) : R :=
    (x + u) ^ d - (x * G d x u) - u ^ d

/-- Z_d は恒等的に 0 である -/
theorem Z_eq_zero {R : Type _} [CommRing R] (d : ℕ) (x u : R) : Z d x u = 0 := by
    unfold Z
    -- Use cosmic_formula_binom which states (x + u)^d - x * G d x u = u^d
    -- Thus, we have (x + u)^d - x * G d x u - u^d = u^d - u^d = 0
    simp only [cosmic_formula_binom, sub_self]

/-! ### f_d の定義と二項展開による表現 -/

/-- d 次の無次元多項式 f の定義: k=0,1 の項を除いた二項和
LaTeX:
f_d(x;u) = \sum_{k=2}^{d} \binom{d}{k} u^k x^{d-k}
-/
def f {R : Type _} [CommRing R] (d : ℕ) (x u : R) : R :=
    (∑ k ∈ Finset.range (d + 1), (Nat.choose d k : R) * x ^ k * u ^ (d - k))
    - (Nat.choose d 0 : R) * x ^ 0 * u ^ d
    - (Nat.choose d 1 : R) * x ^ 1 * u ^ (d - 1)

/-- f は二項展開から (x+u)^d - u^d - (choose d 1) * x * u^(d-1) に等しい
LaTeX:
f_d(x;u) = (x + u)^d - u^d - \binom{d}{1} x u^{d-1}
-/
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

-- #eval R 3 2 1  -- 20
-- #eval R 4 2 1  -- 72
-- #eval R 5 2 1  -- 232
-- #eval R 6 2 1  -- 716
-- #print "verify: 20, 72, 232, 716 -- これは f_d(2;1) の値で、d=3,4,5,6 に対応"

/-- f は無次元宇宙式の関係式に等しい -/
theorem f_eq_relation {R : Type _} [CommRing R] (d : ℕ) (x u : R) :
    f d x u = x * (G d x u - (Nat.choose d 1 : R) * u ^ (d - 1)) := by
    rw [f_eq_pow_sub]
    -- Use cosmic_formula_binom which states (x + u)^d - x * G d x u = u^d
    have h' : (x + u) ^ d - u ^ d = Body d x u := by
      simp [←cosmic_formula_binom d x u, Body]
    rw [h']
    simp [Body, G]
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
    (x + u) ^ d = x * DkMath.CosmicFormulaDim.GReal d x u + u ^ d
        ↔ (x + u) ^ d = Body d x u + u ^ d := by
    simp [DkMath.CosmicFormulaDim.GReal, Body, G]

end CommRing

-- ----------------------------------------------------------------------------
-- 無減算形の恒等式 (CommSemiring)
-- ----------------------------------------------------------------------------

section CommSemiring

/--
`GTail` の `r = 1` specialization としての legacy `GN` wrapper。

[GNZC] Migration note:
the canonical naming home is now `DkMath.CosmicFormula.GN` in `Defs.lean`.
This wrapper is kept to avoid breaking downstream imports during the transition.

refactor 移行期のあいだはこの公開名を温存し、downstream は段階的に
`GTail` 直接参照へ寄せていく。
-/
@[simp] abbrev GN {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) : R :=
  DkMath.CosmicFormula.GN R x u d

/--
Compatibility bridge to the legacy explicit sum shape of `GN`.

This lemma is kept so that downstream files depending on the old expansion can
be migrated incrementally instead of switching to `GTail` all at once.
-/
theorem GN_eq_sum {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) :
    GN d x u =
      ∑ k ∈ Finset.range d, (Nat.choose d (k + 1) : R) * x ^ k * u ^ (d - 1 - k) := by
  simpa [GN] using DkMath.CosmicFormula.GTail_one_eq_sum (R := R) d x u

/-- 無次元版: Big の定義 -/
@[simp] def BigN {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) : R := (x + u) ^ d

/-- 無次元版: Gap の定義 -/
@[simp] def GapN {R : Type _} [CommSemiring R] (d : ℕ) (u : R) : R := u ^ d

/-- 無次元版: Body の定義 -/
@[simp] def BodyN {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) : R := x * GN d x u

/-- 無次元宇宙式に対する恒等式（CommSemiring）：
`(x + u) ^ d = x * G d x u + u ^ d` が成り立つことを示す定理。 -/
theorem cosmic_id_csr {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) :
    BigN d x u = BodyN d x u + GapN d u := by
  by_cases hd : d = 0
  · subst hd
    simp [BigN, BodyN, GapN, GN]
  · have hle : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd)
    have htail :=
      DkMath.CosmicFormula.add_pow_eq_prefix_add_xpow_mul_GTail (R := R) d 1 x u hle
    simpa [BigN, BodyN, GapN, GN, Finset.range_one, Nat.choose_zero_right, Nat.cast_one,
      pow_zero, pow_one, Nat.sub_zero, one_mul, add_comm, add_left_comm, add_assoc] using htail

/-! 無減算形の恒等式: (x+u)^d = x * G d x u + u^d (CommSemiring) -/
theorem cosmic_id_csr' {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) :
        (x + u) ^ d = x * GN d x u + u ^ d := by
  by_cases hd : d = 0
  · subst hd
    simp [GN]
  · have hle : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd)
    have htail :=
      DkMath.CosmicFormula.add_pow_eq_prefix_add_xpow_mul_GTail (R := R) d 1 x u hle
    simpa [GN, Finset.range_one, Nat.choose_zero_right, Nat.cast_one, pow_zero, pow_one,
      Nat.sub_zero, one_mul, add_comm, add_left_comm, add_assoc] using htail

/--
Big-Gap（1 Gap 抽出版）:
`(x+u)^d - u^d` は必ず `x` を因子に持つ（加法形）。
-/
theorem add_pow_gap_factor {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) :
    (x + u) ^ d = u ^ d + x * GN d x u := by
  simpa [add_comm, add_left_comm, add_assoc] using (cosmic_id_csr' (R := R) d x u)

/--
Nat 上で `2 ≤ d` かつ `x,u > 0` なら、`BigN d x u` は端点の 2 項
`x ^ d + GapN d u` に一致しない。

これは `BigN` に必ず正の混合項が残ることの、`GN` 側語彙での直接版。
-/
theorem bigN_ne_xpow_add_gapN_nat_of_two_le {d x u : ℕ}
    (hd : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) :
    BigN d x u ≠ x ^ d + GapN d u := by
  simpa [BigN, GapN] using
    DkMath.Algebra.BinomTail.add_pow_ne_sum_pows_nat_of_two_le x u hd hx hu

/--
Nat 上で `2 ≤ d` かつ `x,u > 0` なら、`BigN d x u` は端点の 2 項和より真に大きい。

したがって、`BigN` を端点 2 項だけで表そうとする試みは失敗し、
混合項を保持する `GN` のような中間層が必要になる。
-/
theorem xpow_add_gapN_lt_bigN_nat_of_two_le {d x u : ℕ}
    (hd : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) :
    x ^ d + GapN d u < BigN d x u := by
  simpa [BigN, GapN] using
    DkMath.Algebra.BinomTail.add_pow_gt_sum_pows_nat_of_two_le x u hd hx hu

/--
Nat 上で `2 ≤ d` かつ `x,u > 0` なら、`BodyN d x u = x * GN d x u` は
端点冪 `x ^ d` より真に大きい。

これは `BigN = GapN + BodyN` と混合項の正性から直ちに従う。
-/
theorem xpow_lt_bodyN_nat_of_two_le {d x u : ℕ}
    (hd : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) :
    x ^ d < BodyN d x u := by
  have hlt : x ^ d + GapN d u < GapN d u + BodyN d x u := by
    simpa [BigN, add_pow_gap_factor, add_comm, add_left_comm, add_assoc] using
      xpow_add_gapN_lt_bigN_nat_of_two_le (d := d) (x := x) (u := u) hd hx hu
  have hlt' : GapN d u + x ^ d < GapN d u + BodyN d x u := by
    simpa [add_comm, add_left_comm, add_assoc] using hlt
  omega

/--
Nat 上で `2 ≤ d` かつ `x,u > 0` なら、`BodyN d x u` は正である。
-/
theorem bodyN_pos_nat_of_two_le {d x u : ℕ}
    (hd : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) :
    0 < BodyN d x u := by
  have hxpow_pos : 0 < x ^ d := Nat.pow_pos hx
  exact lt_trans hxpow_pos (xpow_lt_bodyN_nat_of_two_le (d := d) (x := x) (u := u) hd hx hu)

/--
Nat 上で `2 ≤ d` かつ `x,u > 0` なら、`GN d x u` は 0 でない。

`BodyN = x * GN` が正なので、`GN = 0` はあり得ない。
-/
theorem GN_ne_zero_nat_of_two_le {d x u : ℕ}
    (hd : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) :
    GN d x u ≠ 0 := by
  have hbody_pos : 0 < BodyN d x u :=
    bodyN_pos_nat_of_two_le (d := d) (x := x) (u := u) hd hx hu
  intro hGN
  have : BodyN d x u = 0 := by
    rw [BodyN, hGN]
    simp
  omega

/--
Nat 上で `2 ≤ d` かつ `x,u > 0` なら、`GN d x u` は少なくとも 1。
-/
theorem one_le_GN_nat_of_two_le {d x u : ℕ}
    (hd : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) :
    1 ≤ GN d x u := by
  exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (GN_ne_zero_nat_of_two_le (d := d) (x := x) (u := u) hd hx hu))

/--
If a squarefree natural number is divisible by a prime `p`, then its `p`-adic
valuation is exactly `1`.
-/
private lemma padicValNat_eq_one_of_prime_dvd_of_squarefree
    {p n : ℕ}
    (hp : Nat.Prime p) (hn : n ≠ 0)
    (hpd : p ∣ n) (hsq : Squarefree n) :
    padicValNat p n = 1 := by
  have hle : padicValNat p n ≤ 1 := by
    by_contra hnot
    have htwo : 2 ≤ padicValNat p n := by omega
    have hp2dvd : p ^ 2 ∣ n := by
      exact (DkMath.ABC.padicValNat_le_iff_dvd hp hn 2).mp htwo
    have hfac_le : n.factorization p ≤ 1 := by
      exact (Nat.squarefree_iff_factorization_le_one hn).mp hsq p
    have hfac_ge : 2 ≤ n.factorization p := by
      exact (hp.pow_dvd_iff_le_factorization hn).mp hp2dvd
    exact (Nat.not_succ_le_self 1) (le_trans hfac_ge hfac_le)
  have hge : 1 ≤ padicValNat p n := by
    exact DkMath.ABC.padicValNat_one_le_of_prime_dvd hp hn hpd
  omega

/--
Squarefree `GN` obstructs the corresponding Body difference from being a
perfect `d`-th power.

This is the direct `GN`-layer wrapper of the valuation argument:
choose a prime factor `q` of the squarefree kernel `GN`, use coprimality to
keep `q` out of the boundary factor `x`, and conclude that
`v_q ((x+u)^d - u^d) = 1`, which is incompatible with a `d`-th power when
`d > 1`.
-/
theorem body_not_perfect_pow_of_squarefree_GN
    {d x u : ℕ}
    (hd : 1 < d)
    (hGN_gt : 1 < GN d x u)
    (hcop : Nat.Coprime x (GN d x u))
    (hSq : Squarefree (GN d x u)) :
    ¬ ∃ t : ℕ, 0 < t ∧ (x + u) ^ d - u ^ d = t ^ d := by
  let N := GN d x u
  have hN_ne1 : N ≠ 1 := Nat.ne_of_gt hGN_gt
  have hN_ne0 : N ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one hGN_gt)
  obtain ⟨q, hq_prime, hq_dvd_N⟩ := Nat.exists_prime_and_dvd hN_ne1
  have hq_not_dvd_x : ¬ q ∣ x := by
    intro hq_dvd_x
    have hq_dvd_gcd : q ∣ Nat.gcd x N := Nat.dvd_gcd hq_dvd_x hq_dvd_N
    rw [hcop.gcd_eq_one] at hq_dvd_gcd
    exact hq_prime.not_dvd_one hq_dvd_gcd
  have hval_N_eq : padicValNat q N = 1 := by
    exact padicValNat_eq_one_of_prime_dvd_of_squarefree hq_prime hN_ne0 hq_dvd_N (by simpa [N] using hSq)
  have hx_ne : x ≠ 0 := by
    intro hx0
    exact hq_not_dvd_x (by simp [hx0])
  have hbody_factor : (x + u) ^ d - u ^ d = x * N := by
    rw [show N = GN d x u by rfl]
    rw [add_pow_gap_factor]
    exact Nat.add_sub_cancel_left _ _
  letI : Fact (Nat.Prime q) := ⟨hq_prime⟩
  have hval_body : padicValNat q ((x + u) ^ d - u ^ d) = 1 := by
    rw [hbody_factor, padicValNat.mul hx_ne hN_ne0]
    rw [padicValNat.eq_zero_of_not_dvd hq_not_dvd_x, hval_N_eq]
  intro hpow
  rcases hpow with ⟨t, ht_pos, ht_eq⟩
  have ht_ne : t ≠ 0 := Nat.ne_of_gt ht_pos
  have hdvd : d ∣ padicValNat q (t ^ d) := by
    exact DkMath.ABC.dvd_padicValNat_pow hq_prime d ht_ne
  have hone : padicValNat q (t ^ d) = 1 := by
    calc
      padicValNat q (t ^ d) = padicValNat q ((x + u) ^ d - u ^ d) := by
        rw [ht_eq]
      _ = 1 := hval_body
  have hdvd_one : d ∣ 1 := by
    simpa [hone] using hdvd
  have hle_one : d ≤ 1 := Nat.le_of_dvd (by decide : 0 < 1) hdvd_one
  omega

/--
`d=3` の Tail は `u^2` ではなく（変数名を `x,u` に取っているため）`x^2` を因子に持つ。
すなわち:
`(x+u)^3 = u^3 + 3*x*u^2 + x^2*(x+3*u)`。
-/
theorem add_pow_tail_u2_d3 {R : Type _} [CommSemiring R] (x u : R) :
    (x + u) ^ 3 = u ^ 3 + (3 : R) * x * u ^ 2 + x ^ 2 * (x + (3 : R) * u) := by
  ring

/--
`Nat` 版の `d=3` Tail 割り切り:
`x^2 ∣ ((x+u)^3 - u^3 - 3*x*u^2)`。
-/
theorem add_pow_tail_u2_d3_nat_dvd (x u : ℕ) :
    x ^ 2 ∣ ((x + u) ^ 3 - u ^ 3 - 3 * x * u ^ 2) := by
  let w : ℕ := x + 3 * u
  refine ⟨w, ?_⟩
  have h :
      (x + u) ^ 3 = u ^ 3 + (3 : ℕ) * x * u ^ 2 + x ^ 2 * w := by
    simpa [w, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using (add_pow_tail_u2_d3 (R := ℕ) x u)
  calc
    (x + u) ^ 3 - u ^ 3 - 3 * x * u ^ 2
        = (u ^ 3 + (3 * x * u ^ 2 + x ^ 2 * w) - u ^ 3) - 3 * x * u ^ 2 := by
            simp [h, Nat.add_assoc]
    _ = (3 * x * u ^ 2 + x ^ 2 * w) - 3 * x * u ^ 2 := by
          simp
    _ = x ^ 2 * w := by
          simp

/--
2 Gap 抽出（d=3）:
`(x+y)^3` から `x^3` と `y^3` を抜いた差は `x*y` を因子に持つ。
-/
theorem two_gap_xy_factor_d3 {R : Type _} [CommSemiring R] (x y : R) :
    (x + y) ^ 3 = x ^ 3 + y ^ 3 + x * y * ((3 : R) * (x + y)) := by
  ring

/--
2 Gap 抽出（d=3, Nat `dvd` 版）:
`x*y ∣ ((x+y)^3 - x^3 - y^3)`。
-/
theorem two_gap_xy_factor_d3_nat_dvd (x y : ℕ) :
    x * y ∣ ((x + y) ^ 3 - x ^ 3 - y ^ 3) := by
  let w : ℕ := 3 * (x + y)
  refine ⟨w, ?_⟩
  have h :
      (x + y) ^ 3 = x ^ 3 + y ^ 3 + x * y * w := by
    simpa [w, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using (two_gap_xy_factor_d3 (R := ℕ) x y)
  calc
    (x + y) ^ 3 - x ^ 3 - y ^ 3
        = (x ^ 3 + (y ^ 3 + x * y * w) - x ^ 3) - y ^ 3 := by
            simp [h, Nat.add_assoc]
    _ = (y ^ 3 + x * y * w) - y ^ 3 := by
          simp
    _ = x * y * w := by
          simp

/--
2 Gap 抽出（一般版, `d+2` 形）:
`(x+y)^(d+2)` から `x^(d+2)` と `y^(d+2)` を抜いた差は `x*y` を因子に持つ。
-/
theorem two_gap_xy_factor {R : Type _} [CommSemiring R] (d : ℕ) (x y : R) :
    (x + y) ^ (d + 2)
      = x ^ (d + 2) + y ^ (d + 2)
        + x * y
            * (∑ k ∈ Finset.range (d + 1),
                (Nat.choose (d + 2) (k + 1) : R) * x ^ k * y ^ (d - k)) := by
  rw [add_pow]
  have hsplit0 :
      (∑ k ∈ Finset.range (d + 3),
        x ^ k * y ^ (d + 2 - k) * (Nat.choose (d + 2) k : R))
      =
      x ^ 0 * y ^ (d + 2) * (Nat.choose (d + 2) 0 : R)
        + ∑ k ∈ Finset.range (d + 2),
            x ^ (k + 1) * y ^ (d + 1 - k) * (Nat.choose (d + 2) (k + 1) : R) := by
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Nat.sub_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    congr 2
    have hk' : k < d + 2 := Finset.mem_range.mp hk
    have h2 : d + 2 - (k + 1) = d + 1 - k := by omega
    rw [h2]
  have hsplit1 :
      (∑ k ∈ Finset.range (d + 2),
        x ^ (k + 1) * y ^ (d + 1 - k) * (Nat.choose (d + 2) (k + 1) : R))
      =
      (∑ k ∈ Finset.range (d + 1),
        x ^ (k + 1) * y ^ (d + 1 - k) * (Nat.choose (d + 2) (k + 1) : R))
      + x ^ (d + 2) * y ^ 0 * (Nat.choose (d + 2) (d + 2) : R) := by
    rw [Finset.sum_range_succ]
    simp
  have hfactor :
      (∑ k ∈ Finset.range (d + 1),
        x ^ (k + 1) * y ^ (d + 1 - k) * (Nat.choose (d + 2) (k + 1) : R))
      =
      x * y
        * (∑ k ∈ Finset.range (d + 1),
            (Nat.choose (d + 2) (k + 1) : R) * x ^ k * y ^ (d - k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < d + 1 := Finset.mem_range.mp hk
    have hy' : d + 1 - k = Nat.succ (d - k) := by omega
    rw [pow_succ, hy', pow_succ]
    ring
  rw [hsplit0, hsplit1, hfactor]
  simp [Nat.choose_zero_right, Nat.choose_self]
  ring

/--
2 Gap 抽出（一般版, Nat `dvd` 版, `d+2` 形）:
`x*y ∣ ((x+y)^(d+2) - x^(d+2) - y^(d+2))`。
-/
theorem two_gap_xy_factor_nat_dvd (d x y : ℕ) :
    x * y ∣ ((x + y) ^ (d + 2) - x ^ (d + 2) - y ^ (d + 2)) := by
  let w : ℕ :=
    ∑ k ∈ Finset.range (d + 1),
      (Nat.choose (d + 2) (k + 1) : ℕ) * x ^ k * y ^ (d - k)
  refine ⟨w, ?_⟩
  have h :
      (x + y) ^ (d + 2)
        = x ^ (d + 2) + y ^ (d + 2) + x * y * w := by
    simpa [w] using (two_gap_xy_factor (R := ℕ) d x y)
  calc
    (x + y) ^ (d + 2) - x ^ (d + 2) - y ^ (d + 2)
        = (x ^ (d + 2) + (y ^ (d + 2) + x * y * w) - x ^ (d + 2)) - y ^ (d + 2) := by
            simp [h, Nat.add_assoc]
    _ = (y ^ (d + 2) + x * y * w) - y ^ (d + 2) := by
          simp
    _ = x * y * w := by
          simp

/--
`2 ≤ d` 形のラッパー版。
-/
theorem two_gap_xy_factor_of_two_le {R : Type _} [CommSemiring R]
    {d : ℕ} (hd : 2 ≤ d) (x y : R) :
    (x + y) ^ d
      = x ^ d + y ^ d
        + x * y
            * (∑ k ∈ Finset.range (d - 1),
                (Nat.choose d (k + 1) : R) * x ^ k * y ^ (d - 2 - k)) := by
  rcases Nat.exists_eq_add_of_le hd with ⟨n, rfl⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using (two_gap_xy_factor (R := R) n x y)

/--
Nat 上で `2 ≤ d` かつ `x,u > 0` なら、`(x+u)^d` は端点の 2 項
`x ^ d + u ^ d` に一致しない。

言い換えると、`(x+u)^d` には必ず正の混合項が残るため、
`x^d + u^d` 型を扱うには `G` / `GN` のような中間層が必要になる。
-/
theorem add_pow_ne_sum_pows_nat_of_two_le_binom {d x u : ℕ}
    (hd : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) :
    (x + u) ^ d ≠ x ^ d + u ^ d := by
  simpa using DkMath.Algebra.BinomTail.add_pow_ne_sum_pows_nat_of_two_le x u hd hx hu

/--
Nat 上で `2 ≤ d` かつ `x,u > 0` なら、`(x+u)^d` は端点の 2 項和より真に大きい。
-/
theorem add_pow_gt_sum_pows_nat_of_two_le_binom {d x u : ℕ}
    (hd : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) :
    x ^ d + u ^ d < (x + u) ^ d := by
  simpa using DkMath.Algebra.BinomTail.add_pow_gt_sum_pows_nat_of_two_le x u hd hx hu

end CommSemiring

end DkMath.CosmicFormulaBinom
