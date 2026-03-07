/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Basic
import DkMath.CosmicFormula.CosmicFormulaBinom
import DkMath.CosmicFormula.Gap
import DkMath.ABC.PadicValNat
import Mathlib.NumberTheory.FLT.Three

set_option linter.style.longLine false

/-!
# FLT Core Lemmas
このファイルは Lean 4 で Fermat の Last Theorem (FLT) の証明に必要なコア補題を集めたモジュールです。

**概要:**
- **インポート**: 基本的な数学ライブラリ、宇宙式（二項版）、ギャップ理論、p進付値に関するモジュールをインポート

**主要な定理・補題:**

1. **`zpow_eq_sub_mul_GN_add`**: 宇宙式（Cosmic Formula）の因数分解を利用して、`z^d = (z-y) * GN d (z-y) y + y^d` を導出する補題

2. **`pow_eq_sub_mul_GN_of_add_pow_eq`**: FLT 形式 `x^d + y^d = z^d` と宇宙式を組み合わせて、`x^d = (z-y) * GN d (z-y) y` を得る補題

3. **`GN_eq_head_of_x_eq_zero`**: `x = 0` のとき、GN 多項式が先頭項 `choose d 1 * u^(d-1)` に簡約される（一般的な可換半環で成立）

4. **`GN_zmod_eq_head_of_dvd`**: ZMod 版：`p ∣ x` なら GN が先頭項に簡約される

5. **`GN_zmod_ne_zero_of_dvd_x`**: `p ∣ x` かつ `(d : ZMod p) ≠ 0`、`(u : ZMod p) ≠ 0` ならば GN ≠ 0

6. **`exponent_alignment_failure_of_val_not_dvd`**: p 進付値による指数整合の破綻を示す補題。`x^d = u*G` で `p ∤ G` なのに `d ∤ v_p(u)` なら矛盾を導出

**構造**: 宇宙式と p 進付値理論を組み合わせて、FLT の反例が存在しないことを証明するための基盤となっています。
-/

namespace DkMath

open scoped BigOperators

open DkMath.CosmicFormulaBinom
open DkMath.ABC  -- padicValNat_mul_eq_left がこのへんに居る想定

/-- `y ≤ z` のとき、宇宙式（二項版）から `z^d = (z - y) * GN d (z - y) y + y^d` を得る。 -/
lemma zpow_eq_sub_mul_GN_add (d y z : ℕ) (hyz : y ≤ z) :
    z ^ d = (z - y) * GN d (z - y) y + y ^ d := by
  -- cosmic_id_csr' : ((z-y)+y)^d = (z-y)*GN ... + y^d
  have h :=
    (cosmic_id_csr' (R := ℕ) d (z - y) y)
  -- (z - y) + y = z
  simpa [Nat.sub_add_cancel hyz] using h

/-- FLT 形 `x^d + y^d = z^d` と宇宙式因数分解を合わせて `x^d = (z - y) * GN d (z - y) y` を得る（= 破綻補題へ渡す形）。 -/
lemma pow_eq_sub_mul_GN_of_add_pow_eq
    (d x y z : ℕ) (hyz : y ≤ z)
    (hxyz : x ^ d + y ^ d = z ^ d) :
    x ^ d = (z - y) * GN d (z - y) y := by
  have hz : z ^ d = (z - y) * GN d (z - y) y + y ^ d :=
    zpow_eq_sub_mul_GN_add d y z hyz
  -- `x^d + y^d = z^d = ... + y^d` なので右をキャンセル
  have : x ^ d + y ^ d = (z - y) * GN d (z - y) y + y ^ d := by
    calc
      x ^ d + y ^ d = z ^ d := hxyz
      _ = (z - y) * GN d (z - y) y + y ^ d := hz
  exact Nat.add_right_cancel this

/-- 「ZMod に限らず」: `x = 0` なら `GN` は先頭項 `choose d 1 * u^(d-1)` に潰れる。 -/
lemma GN_eq_head_of_x_eq_zero
    {R : Type _} [CommSemiring R]
    (d : ℕ) (hd : 1 ≤ d) (u : R) :
    GN (R := R) d (0 : R) u = (Nat.choose d 1 : R) * u ^ (d - 1) := by
  cases d with
  | zero =>
      cases (Nat.not_succ_le_zero 0 hd)
  | succ d =>
      -- `range (succ d)` を先頭 k=0 と残りに分解
      unfold GN
      rw [Finset.sum_range_succ']
      -- k=0 項だけ残り、k≥1 項は `0^(k+1)=0` で全部消える
      simp

/-- ZMod 版：`p ∣ x` なら `x ≡ 0 (mod p)` なので `GN` が先頭項に潰れる。 -/
lemma GN_zmod_eq_head_of_dvd
    (p d x u : ℕ) (_hp : Nat.Prime p) (hd : 1 ≤ d) (hx : p ∣ x) :
    GN (R := ZMod p) d (x : ZMod p) (u : ZMod p)
      = (Nat.choose d 1 : ZMod p) * (u : ZMod p) ^ (d - 1) := by
  have hx0 : (x : ZMod p) = 0 := by
    rcases hx with ⟨k, rfl⟩
    -- (p*k : ZMod p) = (p:ZMod p) * k = 0
    simp
  -- x を 0 に潰して上の一般補題へ
  simpa [hx0] using (GN_eq_head_of_x_eq_zero (R := ZMod p) d hd (u := (u : ZMod p)))

end DkMath

namespace DkMath.FLT

/--
`Basic` の GN3 valuation spine が要求する最小 NoLift 供給インターフェイス。

`a, y` を固定した文脈で、任意の素数 `q` について
`q ∣ GN 3 (a^3) y` かつ `q ∤ a^3` なら `q^2 ∤ GN 3 (a^3) y` を返す。
-/
structure GN3NoLiftProvider (a y : ℕ) : Prop where
  noLift_GN3 :
    ∀ {q : ℕ},
      Nat.Prime q ->
      ¬ q ∣ a ^ 3 ->
      q ∣ DkMath.CosmicFormulaBinom.GN 3 (a ^ 3) y ->
      ¬ q ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 (a ^ 3) y

end DkMath.FLT

-- －－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－－

namespace DkMath

open DkMath.CosmicFormulaBinom

/-- ZMod版（短い）：
`p ∣ x` なら `GN d x u` は先頭項に潰れる。
さらに `(d : ZMod p) ≠ 0` かつ `(u : ZMod p) ≠ 0` なら `GN ≠ 0`。 -/
lemma GN_zmod_ne_zero_of_dvd_x
    (p d x u : ℕ) (hp : Nat.Prime p) (hd : 1 ≤ d)
    (hx : p ∣ x)
    (hd0 : (d : ZMod p) ≠ 0)
    (hu0 : (u : ZMod p) ≠ 0) :
    GN (R := ZMod p) d (x : ZMod p) (u : ZMod p) ≠ 0 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hhead :=
    GN_zmod_eq_head_of_dvd (p := p) (d := d) (x := x) (u := u) hp hd hx
  -- GN を先頭項へ
  rw [hhead]
  -- choose d 1 = d
  have hchoose : (Nat.choose d 1 : ZMod p) = (d : ZMod p) := by
    simp
  -- 先頭項が非ゼロなら GN も非ゼロ
  -- (d : ZMod p) ≠ 0 と u^(d-1) ≠ 0 を掛け合わせる
  have hpow : (u : ZMod p) ^ (d - 1) ≠ 0 := by
    exact pow_ne_zero _ hu0
  -- まとめ
  simpa [hchoose] using (mul_ne_zero hd0 hpow)

/-- `n = 3` の `gcd(u, GN 3 u y) = 3` 分岐を処理するための共通補題テンプレート。

`FLT_case_3` と `FLT_of_coprime` の双方から呼べる形で切り出しておき、
実証明はここに一元化する。 -/
lemma gcd_three_case_contra_template
    (x u y : ℕ)
    (hx0 : x ≠ 0) (hu0 : u ≠ 0) (hy0 : y ≠ 0)
    (h_x3 : x ^ 3 = u * GN 3 u y)
    (_h_gcd3 : u.gcd (GN 3 u y) = 3) : False := by
  have h_big : (u + y) ^ 3 = u * GN 3 u y + y ^ 3 := by
    simpa [DkMath.CosmicFormulaBinom.BigN,
      DkMath.CosmicFormulaBinom.BodyN,
      DkMath.CosmicFormulaBinom.GapN] using
      (DkMath.CosmicFormulaBinom.cosmic_id_csr (R := ℕ) (d := 3) (x := u) (u := y))
  have h_flt : x ^ 3 + y ^ 3 = (u + y) ^ 3 := by
    calc
      x ^ 3 + y ^ 3 = u * GN 3 u y + y ^ 3 := by simp [h_x3]
      _ = (u + y) ^ 3 := by simpa using h_big.symm
  have _hu0 : u ≠ 0 := hu0
  have huz0 : u + y ≠ 0 := by
    omega
  exact fermatLastTheoremThree x y (u + y) hx0 hy0 huz0 h_flt

/-- 指数整合の破綻（一般版）：
`x^d = u*G` で `p ∤ G` なのに `d ∤ v_p(u)` なら矛盾。 -/
lemma exponent_alignment_failure_of_val_not_dvd
    {p x u G d : ℕ}
    (hp : Nat.Prime p) (_hd : 2 ≤ d)
    (hx : x ≠ 0) (hu0 : u ≠ 0) (hG0 : G ≠ 0)
    (hG : ¬ p ∣ G)
    (hndvd : ¬ d ∣ padicValNat p u)
    (h : x ^ d = u * G) : False := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpow : padicValNat p (x ^ d) = d * padicValNat p x := by
    simpa using (padicValNat.pow (p := p) (a := x) d hx)
  have hdvd_left : d ∣ padicValNat p (x ^ d) := by
    -- d | (d * v_p(x))
    simp only [hpow, dvd_mul_right]
  have hdvd_right : d ∣ padicValNat p (u * G) := by
    simpa [h] using hdvd_left
  have hval_right :
      padicValNat p (u * G) = padicValNat p u :=
    padicValNat_mul_eq_left (p := p) (a := u) (b := G) hu0 hG0 hG
  have : d ∣ padicValNat p u := by
    simpa [hval_right] using hdvd_right
  exact hndvd this

end DkMath
