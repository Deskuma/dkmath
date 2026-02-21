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

/-- **層A補題：原始素因子の存在**

Zsigmondy定理により、a³ - b³ の素因子で (a-b) に含まれないものが存在する。

**入力:**
- gcd(a,b)=1
- 0 < b < a
- a³ - b³ > 1（非一般性）

**出力:**
存在するq : Prime で
  q | (a³ - b³)
  ¬ q ∣ (a - b)
  q ∣ c（完全3乗仮定時）

**実装:**
ZsigmondyCyclotomic.leanの既存補題を直接使用
-/
lemma exists_primitive_prime_factor_d3 {a b c : ℕ}
    (hab : Nat.Coprime a b) (hb : 0 < b) (ha : b < a) (hc : 0 < c)
    (h_eq : a ^ 3 + b ^ 3 = c ^ 3) :
    ∃ q : ℕ,
      Nat.Prime q ∧ q ∣ c ∧ q ≠ c ∧
      q ∣ a ^ 3 - b ^ 3 ∧ ¬ q ∣ a - b := by
  -- Zsigmondy定理：a³ - b³ の原始素因子の存在
  -- （実装は ZsigmondyCyclotomic.leanで provide）
  sorry  -- 層A補助補題（Zsigmondy理論）が完成したら埋まる

-- ========================================
-- § 2. 層B（PetalDetect + padicValNat評価）
-- ========================================

/-- **層B補題：padicValNat上界**

相対多角数 S0(a,b) = a²+ab+b² の性質と Cosmic Formula による因数分解から、
原始素因子 q に対する padicValNat上界を導出する。

**入力:**
- Nat.Prime q
- q ∣ (a³ - b³)
- ¬ q ∣ (a - b)（原始素因子条件）
- gcd(a,b)=1
- 0 < a, 0 < b

**証明フロー:**

1. a³ - b³ = (a-b)(a²+ab+b²) に分解（Cosmic Formula）

2. q ∤ (a-b) より q | (a²+ab+b²) が必然的に従う

3. PetalDetect補題群により：
   - prime_dvd_S0_coprime_imp_not_dvd_apb: q|S0 ∧ gcd(a,b)=1 ⟹ q∤(a+b)
   - mod_q_ab_analysis: q|(a+b) ∧ q|S0 ⟹ q|b²
   - padicValNat_le_one_of_not_sq_dvd: q|S0 ∧ gcd(a,b)=1 ⟹ ¬q²|S0

4. 結果：v_q(a³-b³) = v_q(a²+ab+b²) ≤ 1

**出力:**
padicValNat q (a³ - b³) ≤ 1

**実装:**
PetalDetect.leanの層B補助補題を活用
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

  have hq_not_apb : ¬ q ∣ a + b :=
    prime_dvd_S0_coprime_imp_not_dvd_apb a b q ha_pos hab_coprime hq hS0_dvd

  -- **Step B.1/B.2/B.3: padicValNat精密評価**
  -- 層B補助補題が完成すれば、以下のロジックで埋まる：
  -- 1. q | S0 ∧ q ∤ (a+b) から q | (a²+ab+b²)
  -- 2. 相対多角数の平方判定：q² ∤ S0
  -- 3. Lucas/Kummer定理による v_q上界

  -- 当面、層B補助補題の完成を待つ
  sorry  -- padicValNat上界補題（層B補助）が完成したら埋まる

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
        simpa [Nat.mul_comm (3 : ℕ) (padicValNat 2 a)] using Nat.dvd_mul_left 3 (padicValNat 2 a)
      have h3_dvd_one : 3 ∣ 1 := by
        have h3_dvd_shift : 3 ∣ 1 + 3 * padicValNat 2 a - 3 * padicValNat 2 a := by
          apply Nat.dvd_sub h3_dvd_rhs h_mul_dvd
        simpa [add_sub_cancel_left, Nat.mul_comm (padicValNat 2 a) 3] using h3_dvd_shift
      exact Nat.Prime.not_dvd_one Nat.prime_three h3_dvd_one
      done

    · -- a > b の場合
      push_neg at hab_eq
      have hab_lt : b < a := Nat.lt_of_le_of_ne hab_cmp (Ne.symm hab_eq)

      -- 層A：原始素因子 q の存在
      obtain ⟨q, hq_prime, hq_dvd_c, hq_ne_c, hq_dvd_pow, hq_ndiv_diff⟩ :=
        exists_primitive_prime_factor_d3 hab hb hab_lt hc h_eq

      -- 層A下界：完全3乗仮定から v_q ≥ 3
      have h_lower : 3 ≤ padicValNat q (a ^ 3 - b ^ 3) := by
        -- a^3 が n乗のとき、v_q(a^3) = 3 * v_q(a)
        -- a^3 | (a^3 - b^3) ⟹ v_q(a^3) ≤ v_q(a^3 - b^3)
        -- 完全3乗 c = a^3 + b^3 の仮定から下界が導ける
        -- （詳細は Zsigmondy層A本体で）
        sorry  -- 層A下界補題

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
