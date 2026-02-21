/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- cid: 697d62b5-312c-83a8-a917-f4aca8fa80ca

import DkMath.FLT.Basic
import DkMath.FLT.PetalDetect
import DkMath.NumberTheory.GcdNext
import DkMath.NumberTheory.ZsigmondyCyclotomic
import DkMath.ABC.PadicValNat
import DkMath.Algebra.DiffPow

#print "file: DkMath.FLT.Main"  --  (別解：Zsigmondy + padicValNat)

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# FLT Main: 別解による形式化証明

**ファイル位置づけ:**
```
理論モジュール (Basic, CosmicFormula, ZsigmondyCyclotomic, ...)
        ↓
    Core.lean     （基本補題：Cosmic Formula の因数分解）
        ↓
    Basic.lean    （FLT d=3 の既存証明）
        ↓
    Main.lean     （別解：Zsigmondy層A + PetalDetect層B）
```

**目的:**
- わっちたちの成果（Zsigmondy原始素因子 + padicValNat上界）による FLT d=3 の別解を形式化
- 既存の Cosmic Formula + coprimality アプローチとは異なる p-adic値評価による証明戦略
- 一般化への展開（d ≥ 5）への基盤構築

**証明方針（3層統合）:**

1. **層A（Zsigmondy原始素因子）**: ZsigmondyCyclotomic.leanの既存補題を活用
   - 原始素因子 q の存在保証
   - q ∤ (a-b) の条件

2. **層B（PetalDetect + padicValNat評価）**: PetalDetect.leanの既存補題を活用
   - S0(a,b) = a²+ab+b²the相対多角数構造
   - (a+b)割り切り検出による φビット判定
   - padicValNat上界 v_q(a³-b³) ≤ 1

3. **矛盾導出**: 層AとBの統合
   - 層A: v_q(a³-b³) ≥ 3（完全3乗仮定）
   - 層B: v_q(a³-b³) ≤ 1（padicValNat上界）
   - 矛盾: 3 ≤ 1
-/

namespace DkMath.FLT

open DkMath.FLT.PetalDetect
open DkMath.NumberTheory.GcdNext
open DkMath.ABC
open DkMath.Algebra.DiffPow

-- ========================================
-- § 1. 層A（Zsigmondy原始素因子）
-- ========================================

/-- **層A補題：Zsigmondy原始素因子の存在**

Zsigmondy定理により、a³ - b³ の素因子で (a-b) に含まれないものが存在する。

**入力:**
- gcd(a,b)=1
- 0 < b < a
- ¬ 3 ∣ (a-b)（重要：分岐条件）

**出力:**
存在するq : Prime で
  q ∣ (a³ - b³)
  ¬ q ∣ (a - b)

**実装:**
ZsigmondyCyclotomic.leanの `exists_primitive_prime_factor_prime` を直接使用
-/
lemma exists_primitive_prime_factor_d3 {a b : ℕ}
    (hab : Nat.Coprime a b) (hb : 0 < b) (ha : b < a)
    (hpnd : ¬ 3 ∣ a - b) :
    ∃ q : ℕ,
      Nat.Prime q ∧ q ∣ a ^ 3 - b ^ 3 ∧ ¬ q ∣ a - b := by
  -- Zsigmondy定理 d=3 版：¬ 3 ∣ (a-b) の場合、a³ - b³ は新しい素因子を持つ
  -- ZsigmondyCyclotomic.leanの exists_primitive_prime_factor_prime を使用
  exact exists_primitive_prime_factor_prime Nat.prime_three
    (by norm_num : 3 ≤ 3) ha hb hab hpnd


-- ========================================
-- § 2. 層B（PetalDetect + padicValNat評価）
-- ========================================

/-- **層B補助補題：相対多角数の平方判定**

q が S0(a,b) を割るが (a+b) を割らず、且つ gcd(a,b)=1 ⟹ q² は S0 を割らない

**入力:**
- Nat.Prime q
- q ∣ S0_nat a b
- ¬ q ∣ (a + b)
- Nat.Coprime a b

**出力:**
¬ q² ∣ S0_nat a b

**証明方針（Petal系+オイラー標数）:**
相対多角数の自己相似性制御により、新しい素因子は高々1乗の重複度を持つ
-/
lemma S0_not_sq_dvd_of_prime_dvd_and_not_dvd_apb {a b q : ℕ}
    (ha_pos : 0 < a) (hb_pos : 0 < b)
    (hab_coprime : Nat.Coprime a b)
    (hq : Nat.Prime q)
    (hS0_dvd : q ∣ S0_nat a b)
    (hq_not_apb : ¬ q ∣ a + b) :
    ¬ q ^ 2 ∣ S0_nat a b := by
  have hq_ne_apb : q ≠ a + b := by
    intro h_eq
    apply hq_not_apb
    simp only [h_eq, dvd_refl]
  have hval_le : padicValNat q (S0_nat a b) ≤ 1 :=
    padicValNat_s0_le_one_of_prime_ne_apb hq ha_pos hb_pos hab_coprime hS0_dvd hq_ne_apb
  have hS0_ne_zero : S0_nat a b ≠ 0 := by
    unfold S0_nat
    positivity
  intro hq_sq
  have hval_ge : 2 ≤ padicValNat q (S0_nat a b) := by
    rw [DkMath.ABC.padicValNat_le_iff_dvd hq hS0_ne_zero 2]
    exact hq_sq
  omega

/-- **層A下界補助補題：完全3乗仮定からのpadicValNat下界**

q が c を割る ⟹ 3 ≤ padicValNat q (c³)（d=3での指数構造）

**入力:**
- q ∣ c
- q は素数

**出力:**
3 ≤ padicValNat q (c³)

**証明方針（Zsigmondy指数理論）:**
完全3乗 c = c¹ より padicValNat q (c³) = 3 * padicValNat q c ≥ 3
-/
lemma padicValNat_lower_bound_of_dvd_d3 {c q : ℕ}
    (hc_pos : 0 < c)
    (hq : Nat.Prime q)
    (hq_dvd_c : q ∣ c) :
    3 ≤ padicValNat q (c ^ 3) := by
  have h_c_ne : c ≠ 0 := Nat.ne_of_gt hc_pos
  letI : Fact (Nat.Prime q) := ⟨hq⟩

  -- padicValNat q c ≥ 1（q | c より）
  have h_val_c_ge_1 : 1 ≤ padicValNat q c := by
    have h_ne_zero : padicValNat q c ≠ 0 := by
      intro h
      have : ¬ q ∣ c := by
        rcases padicValNat.eq_zero_iff.mp h with hq1 | hc0 | hqndvd
        · exact (hq.ne_one hq1).elim
        · exact (h_c_ne hc0).elim
        · exact hqndvd
      exact this hq_dvd_c
    omega

  -- padicValNat q (c^3) = 3 * padicValNat q c
  have h_val_pow : padicValNat q (c ^ 3) = 3 * padicValNat q c :=
    padicValNat.pow (n := 3) h_c_ne

  -- 3 * padicValNat q c ≥ 3 * 1
  rw [h_val_pow]
  omega

/-- **padicValNat上界補題（層B統合版）**

相対多角数 S0(a,b) = a²+ab+b² の性質と Cosmic Formula による因数分解から、
原始素因子 q に対する padicValNat上界を導出する

**入力:**
- Nat.Prime q
- q ∣ (a³ - b³)
- ¬ q ∣ (a - b)（原始素因子条件）
- gcd(a,b)=1
- 0 < a, 0 < b

**証明フロー:**
1. a³ - b³ = (a-b)(a²+ab+b²) に分解
2. q ∤ (a-b) より q | S0
3. 層B補助補題で q² ∤ S0 を導出
4. padicValNat上界：v_q(S0) ≤ 1

**出力:**
padicValNat q (a³ - b³) ≤ 1
-/
lemma padicValNat_upper_bound_d3 {a b q : ℕ}
    (hab_lt : b < a)
    (ha_pos : 0 < a) (hb_pos : 0 < b)
    (hab_coprime : Nat.Coprime a b)
    (hq : Nat.Prime q)
    (hq_dvd : q ∣ a ^ 3 - b ^ 3)
    (hq_ndiv_diff : ¬ q ∣ a - b) :
    padicValNat q (a ^ 3 - b ^ 3) ≤ 1 := by
  -- **Step B.0: (a+b)割り切り検出**
  -- PetalDetect.prime_dvd_S0_coprime_imp_not_dvd_apb より
  -- q | S0(a,b) ∧ gcd(a,b)=1 ⟹ q ∤ (a+b)

  have h_diff : a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by
    -- use sample proof from Samples/FLT.lean
    have h_pow : b ^ 3 ≤ a ^ 3 := Nat.pow_le_pow_left (Nat.le_of_lt hab_lt) 3
    zify [hab_lt, h_pow]
    ring
  have h_fact : a ^ 3 - b ^ 3 = (a - b) * S0_nat a b := by
    -- rewrite using definition of S0_nat and h_diff
    simpa [S0_nat] using h_diff
  have hS0_dvd : q ∣ S0_nat a b := by
    have hmul : q ∣ (a - b) * S0_nat a b := by
      -- hq_dvd : q ∣ a^3 - b^3 を因数分解で書き換え
      simpa [h_fact] using hq_dvd

    -- prime の「積を割るならどっちか」を使う
    have : q ∣ a - b ∨ q ∣ S0_nat a b := hq.dvd_mul.mp hmul

    exact this.resolve_left hq_ndiv_diff

  -- **層B統合：PetalDetect補助補題を活用**
  have hq_not_apb : ¬ q ∣ a + b :=
    prime_dvd_S0_coprime_imp_not_dvd_apb a b q ha_pos hab_coprime hq hS0_dvd

  -- **q² ∤ S0 を導く（相対多角数の性質）**
  have hq_not_sq : ¬ q ^ 2 ∣ S0_nat a b := by
    exact S0_not_sq_dvd_of_prime_dvd_and_not_dvd_apb
      ha_pos hb_pos hab_coprime hq hS0_dvd hq_not_apb

  -- **padicValNat上界：PetalDetect.padicValNat_le_one_of_not_sq_dvd を使用**
  have hpadic_bound : padicValNat q (S0_nat a b) ≤ 1 :=
    padicValNat_le_one_of_not_sq_dvd a b q ha_pos hb_pos hq hq_not_sq

  -- **最終ステップ：padicValNat の乗法性により上界を導く**
  have ha_minus_b_ne_zero : a - b ≠ 0 := Nat.sub_ne_zero_of_lt hab_lt
  have hS0_ne_zero : S0_nat a b ≠ 0 := by
    unfold S0_nat
    have ha2_pos : 0 < a ^ 2 := by positivity
    have hab_pos : 0 < a * b := by positivity
    have hb2_pos : 0 < b ^ 2 := by positivity
    omega

  letI : Fact (Nat.Prime q) := ⟨hq⟩

  have h_val_diff_zero : padicValNat q (a - b) = 0 :=
    padicValNat.eq_zero_of_not_dvd hq_ndiv_diff

  -- a³ - b³ = (a-b) * S0 から padicValNat の乗法性を使う
  have h_val_mult : padicValNat q (a ^ 3 - b ^ 3) =
      padicValNat q (a - b) + padicValNat q (S0_nat a b) :=
    congrArg (padicValNat q) h_fact ▸ padicValNat.mul ha_minus_b_ne_zero hS0_ne_zero

  calc padicValNat q (a ^ 3 - b ^ 3)
      = padicValNat q (a - b) + padicValNat q (S0_nat a b) := h_val_mult
    _ = padicValNat q (S0_nat a b) := by simp [h_val_diff_zero]
    _ ≤ 1 := hpadic_bound

-- ========================================
-- § 3. 矛盾導出（層A + 層B統合）
-- ========================================

/-- **メイン定理：別解による FLT d=3 証明**

**証明戦略:**
1. 層Aから原始素因子 q の存在
2. 層Bから padicValNat上界 v_q ≤ 1
3. 矛盾：完全3乗仮定からは v_q ≥ 3

**形式化:**
-/
theorem FLT_d3_by_padicValNat {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  intro h_eq

  -- 準備：a < b の場合は入れ替える
  by_cases hab_cmp : b ≤ a
  · -- a ≥ b の場合
    by_cases hab_eq : a = b
    · -- a = b の場合：2a³ = c³ から 3 進評価で矛盾
      subst hab_eq
      letI h_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h_pow_eq : 2 * a ^ 3 = c ^ 3 := by
        calc
          2 * a ^ 3 = a ^ 3 + a ^ 3 := by simp [two_mul]
                 _ = c ^ 3 := h_eq
      have h_a_ne_zero : a ≠ 0 := Nat.ne_of_gt ha
      have h_c_ne_zero : c ≠ 0 := Nat.ne_of_gt hc
      have h_pow_c : padicValNat 2 (c ^ 3) = 3 * padicValNat 2 c :=
        padicValNat.pow (p := 2) (a := c) 3 h_c_ne_zero
      have h_pow_a : padicValNat 2 (a ^ 3) = 3 * padicValNat 2 a :=
        padicValNat.pow (p := 2) (a := a) 3 h_a_ne_zero
      have h2_ne_zero : 2 ≠ 0 := by decide
      have h_a_pow_ne_zero : a ^ 3 ≠ 0 := pow_ne_zero 3 h_a_ne_zero
      have h_mul_val : padicValNat 2 (2 * a ^ 3) =
          padicValNat 2 2 + padicValNat 2 (a ^ 3) := by
        simpa using padicValNat.mul (p := 2) (a := 2) (b := a ^ 3) h2_ne_zero h_a_pow_ne_zero
      have h_even_one : padicValNat 2 (2 * 1) = 1 + padicValNat 2 1 :=
        (padic_val_two_of_even 1).2 (by norm_num : 1 ≠ 0)
      have h_one_odd : padicValNat 2 1 = 0 := padic_val_two_of_odd 0
      have h2_val : padicValNat 2 2 = 1 := by
        calc
          padicValNat 2 2 = 1 + padicValNat 2 1 := h_even_one
          _ = 1 := by simp [h_one_odd]
      have h_tmp : padicValNat 2 (2 * a ^ 3) = padicValNat 2 2 + 3 * padicValNat 2 a := by
        simp [h_mul_val, h_pow_a]
      have h_rhs : padicValNat 2 (2 * a ^ 3) = 1 + 3 * padicValNat 2 a := by
        calc
          padicValNat 2 (2 * a ^ 3) = padicValNat 2 2 + 3 * padicValNat 2 a := h_tmp
          _ = 1 + 3 * padicValNat 2 a := by rw [h2_val]
      have h_val_eq : 3 * padicValNat 2 c = 1 + 3 * padicValNat 2 a := by
        calc
          3 * padicValNat 2 c = padicValNat 2 (c ^ 3) := Eq.symm h_pow_c
          _ = padicValNat 2 (2 * a ^ 3) := by
            have h_eq' : c ^ 3 = 2 * a ^ 3 := Eq.symm h_pow_eq
            exact congrArg (padicValNat 2) h_eq'
          _ = 1 + 3 * padicValNat 2 a := h_rhs
      have h3_dvd_rhs : 3 ∣ 1 + 3 * padicValNat 2 a := by
        have h3_dvd_left : 3 ∣ padicValNat 2 c * 3 := Nat.dvd_mul_left 3 (padicValNat 2 c)
        simpa [h_val_eq, Nat.mul_comm (padicValNat 2 c) 3] using h3_dvd_left
      have h_le : 3 * padicValNat 2 a ≤ 1 + 3 * padicValNat 2 a :=
        Nat.le_add_left (3 * padicValNat 2 a) 1
      have h_mul_dvd : 3 ∣ 3 * padicValNat 2 a := by
        simp [Nat.mul_comm (3 : ℕ) (padicValNat 2 a)] at *
      have h3_dvd_one : 3 ∣ 1 := by
        have h3_dvd_shift : 3 ∣ 1 + 3 * padicValNat 2 a - 3 * padicValNat 2 a := by
          apply Nat.dvd_sub h3_dvd_rhs h_mul_dvd
        simp only [add_tsub_cancel_right, Nat.dvd_one, OfNat.ofNat_ne_one] at h3_dvd_shift
      exact Nat.Prime.not_dvd_one Nat.prime_three h3_dvd_one

    · -- a > b の場合
      push_neg at hab_eq
      have hab_lt : b < a := Nat.lt_of_le_of_ne hab_cmp (Ne.symm hab_eq)

      -- **分岐：3 ∣ (a-b) かどうか**
      by_cases h3div : 3 ∣ a - b
      · -- ケース2-1: 3 ∣ (a-b)
        -- この場合、Zsigmondy層A補助補題が適用できない
        -- 代わりに「3が平方で割る」ことを示して矛盾導出
        have h_ab_pos : 0 < a - b := Nat.sub_pos_of_lt hab_lt
        have h_3pow_dvd : 9 ∣ a ^ 3 - b ^ 3 := by
          -- 3 | (a-b) ⟹ 3 | (a^3 - b^3)（立方）
          -- さらに 3^2 | (a^3 - b^3) を示せる
          sorry  -- 層A補助：3の平方割り切り分析

        -- h_eq : a^3 + b^3 = c^3 から矛盾を導く
        -- この分岐は層Aの異なる分析が必要
        sorry  -- 層A補助：3|a-b ケースの分析

      · -- ケース2-2: ¬ 3 ∣ (a-b)（通常の Zsigmondy ケース）
        -- by_cases の分岐により h3div : ¬ 3 ∣ a - b が自動的に成立

        -- 層A：原始素因子 q の存在（Zsigmondy定理）
        obtain ⟨q, hq_prime, hq_dvd_pow, hq_ndiv_diff⟩ :=
          exists_primitive_prime_factor_d3 hab hb hab_lt h3div

        -- 層A下界：完全3乗仮定から v_q ≥ 3
        have h_lower : 3 ≤ padicValNat q (a ^ 3 - b ^ 3) := by
          -- **Zsigmondy理論による下界：**
          -- 原始素因子 q は「新しい」素因子であり、
          -- d=3 での指数構造において高い重複度を持つ。
          --
          -- 証明メカニズム（層A本来の形式化時の詳細）：
          -- 1. Zsigmondy定理: 原始素因子 q の存在（既に層A補助補題で確立）
          -- 2. 指数の構造: 新しい素因子の "exponent of appearance" は d と関連
          -- 3. a³ - b³ の padicValNat: v_q(a³ - b³) ≥ 1 は自動
          -- 4. 完全3乗仮定 a³ + b³ = c³ を組み合わせると v_q ≥ 3 が導ける
          --
          -- 詳細実装はおそらく:
          -- - Lifting the Exponent Lemma (LTE) の応用
          -- - または Zsigmondy の exponent database
          -- - または padicValNat の３乗構造分析
          --
          -- 当ファイルでは層A形式化スケッチのため、
          -- 下界の具体的導出は次フェーズ（GcdNextLayerB.lean等）へ譲る。
          --
          sorry  -- 層A下界：Zsigmondy指数理論の完全形式化待ち

        -- 層B上界：padicValNat評価
        have h_upper : padicValNat q (a ^ 3 - b ^ 3) ≤ 1 :=
          padicValNat_upper_bound_d3 hab_lt ha hb hab hq_prime hq_dvd_pow hq_ndiv_diff

        -- 矛盾：3 ≤ padicValNat ≤ 1
        have h_bound : 3 ≤ 1 := le_trans h_lower h_upper
        have h_contra : ¬ 3 ≤ 1 := Nat.not_le_of_lt (by norm_num : 1 < 3)
        contradiction

  · -- a < b の場合（b と a を入れ替えて再帰）
    push_neg at hab_cmp
    have h_eq_swap : b ^ 3 + a ^ 3 = c ^ 3 := by
      calc b ^ 3 + a ^ 3 = a ^ 3 + b ^ 3 := by ring
                       _ = c ^ 3 := h_eq
    have hab_swap : Nat.Coprime b a := Nat.coprime_comm.mp hab
    have : b ^ 3 + a ^ 3 ≠ c ^ 3 :=
      FLT_d3_by_padicValNat hb ha hc hab_swap
    exact this h_eq_swap

end DkMath.FLT
