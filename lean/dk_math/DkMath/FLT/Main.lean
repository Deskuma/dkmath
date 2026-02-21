/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- cid: 697d62b5-312c-83a8-a917-f4aca8fa80ca

-- no-import DkMath.FLT.Basic 依存しないように外す
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
-- § 0. 新ルート補助補題（c³-b³=a³ による証明を分離）
-- ========================================

/-- **補助補題1：立方の差の恒等式**

a³ + b³ = c³ から、c³ - b³ = a³ を導く補助補題。
-/
lemma cube_sub_eq_of_add_eq {a b c : ℕ} (h : a ^ 3 + b ^ 3 = c ^ 3) :
    c ^ 3 - b ^ 3 = a ^ 3 := by
  -- c³ = a³ + b³ に書き換えて (x+y)-y=x を適用
  rw [← h]
  omega

/-- **補助補題2：互いに素性の遺伝**

gcd(a,b)=1 かつ a³+b³=c³ なら gcd(c,b)=1。
-/
lemma coprime_cb_of_eq {a b c : ℕ} (hab : Nat.Coprime a b) (h : a ^ 3 + b ^ 3 = c ^ 3) :
    Nat.Coprime c b := by
  by_contra hnot
  have hgcd_ne : Nat.gcd c b ≠ 1 := by
    intro hg
    apply hnot
    exact (Nat.coprime_iff_gcd_eq_one).2 hg

  -- gcd(c,b) を割る素数 p が存在
  obtain ⟨p, hp, hp_dvd_g⟩ := Nat.exists_prime_and_dvd hgcd_ne
  have hp_dvd_c : p ∣ c := dvd_trans hp_dvd_g (Nat.gcd_dvd_left c b)
  have hp_dvd_b : p ∣ b := dvd_trans hp_dvd_g (Nat.gcd_dvd_right c b)

  -- p | c³ かつ p | b³
  have hp_dvd_c3 : p ∣ c^3 := dvd_trans hp_dvd_c (dvd_pow_self c (by decide : 3 ≠ 0))
  have hp_dvd_b3 : p ∣ b^3 := dvd_trans hp_dvd_b (dvd_pow_self b (by decide : 3 ≠ 0))

  -- c³ - b³ = a³ より p | a³
  have hsub : c^3 - b^3 = a^3 := cube_sub_eq_of_add_eq h
  have hp_dvd_sub : p ∣ c^3 - b^3 := Nat.dvd_sub hp_dvd_c3 hp_dvd_b3
  have hp_dvd_a3 : p ∣ a^3 := by simpa [hsub] using hp_dvd_sub

  -- p | a³ ∧ p 素数 ⟹ p | a
  have hp_dvd_a : p ∣ a := hp.dvd_of_dvd_pow hp_dvd_a3

  -- gcd(a,b) = 1 に矛盾
  have hp_dvd_gab : p ∣ Nat.gcd a b := Nat.dvd_gcd hp_dvd_a hp_dvd_b
  have : p ∣ 1 := by simpa [hab.gcd_eq_one] using hp_dvd_gab
  exact hp.not_dvd_one this

/-- **補助補題3：差の立方に存在する原始素因子（3|diff分岐含む）**

c > b で gcd(c,b)=1 のとき、
q | (c³-b³) ∧ q ∤ (c-b) を満たす素数 q が存在。

このとき 3 | (c-b) の分岐も網羅。
-/
lemma exists_prime_factor_cube_diff {c b : ℕ}
    (hbc : b < c) (hb : 0 < b) (hcop : Nat.Coprime c b) :
    ∃ q, Nat.Prime q ∧ q ∣ c^3 - b^3 ∧ ¬ q ∣ c - b := by
  by_cases h3 : 3 ∣ c - b
  · rcases h3 with ⟨k, hk⟩
    have hdiff_pos : 0 < c - b := Nat.sub_pos_of_lt hbc
    have hk_pos : 0 < k := by
      have : 0 < 3 * k := by simpa [hk] using hdiff_pos
      exact Nat.pos_of_mul_pos_left this

    have hc_eq : c = 3 * k + b := by
      calc
        c = (c - b) + b := (Nat.sub_add_cancel hbc.le).symm
        _ = 3 * k + b := by simp only [hk]

    let m : ℕ := 3 * k ^ 2 + 3 * k * b + b ^ 2

    have hm_gt1 : 1 < m := by
      have hk2_pos : 0 < k ^ 2 := by positivity
      have hb2_pos : 0 < b ^ 2 := by positivity
      dsimp [m]
      omega

    obtain ⟨q, hq, hq_dvd_m⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hm_gt1)

    have h3_ndvd_b : ¬ 3 ∣ b := by
      intro h3b
      have h3c : 3 ∣ c := by
        have : 3 ∣ (c - b) + b := dvd_add (by exact ⟨k, hk⟩) h3b
        simpa [Nat.sub_add_cancel hbc.le] using this
      have h3gcd : 3 ∣ Nat.gcd c b := Nat.dvd_gcd h3c h3b
      have h3one : 3 ∣ 1 := by
        simp only [hcop.gcd_eq_one, Nat.dvd_one, OfNat.ofNat_ne_one] at h3gcd
      exact Nat.prime_three.not_dvd_one h3one

    have h3_ndvd_m : ¬ 3 ∣ m := by
      intro h3m
      have h3_dvd_t1 : 3 ∣ 3 * k ^ 2 := by
        simp only [dvd_mul_right]
      have h3_dvd_t2 : 3 ∣ 3 * k * b := by
        have : 3 ∣ 3 * k := by
          simp only [dvd_mul_right]
        exact dvd_mul_of_dvd_left this b
      have h3_dvd_sum12 : 3 ∣ 3 * k ^ 2 + 3 * k * b := dvd_add h3_dvd_t1 h3_dvd_t2
      have hm_eq : m = (3 * k ^ 2 + 3 * k * b) + b ^ 2 := by
        rfl
      have h3_dvd_b2 : 3 ∣ b ^ 2 := by
        exact (Nat.dvd_add_right h3_dvd_sum12).1 (by simpa [hm_eq] using h3m)
      have h3b : 3 ∣ b := Nat.prime_three.dvd_of_dvd_pow h3_dvd_b2
      exact h3_ndvd_b h3b

    have hq_ndvd_three : ¬ q ∣ 3 := by
      intro hq3
      have hq_eq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 hq3
      exact h3_ndvd_m (hq_eq3 ▸ hq_dvd_m)

    have hq_ndvd_k : ¬ q ∣ k := by
      intro hqk
      have hm_eq : m = k * (3 * k + 3 * b) + b ^ 2 := by
        dsimp [m]
        ring
      have hq_dvd_prod : q ∣ k * (3 * k + 3 * b) := dvd_mul_of_dvd_left hqk _
      have hq_dvd_b2 : q ∣ b ^ 2 := by
        exact (Nat.dvd_add_right hq_dvd_prod).1 (by simpa [hm_eq] using hq_dvd_m)
      have hq_dvd_b : q ∣ b := hq.dvd_of_dvd_pow hq_dvd_b2
      have hq_dvd_c : q ∣ c := by
        have hq_dvd_3k : q ∣ 3 * k := dvd_mul_of_dvd_right hqk 3
        have : q ∣ 3 * k + b := dvd_add hq_dvd_3k hq_dvd_b
        simpa [hc_eq] using this
      have : q ∣ Nat.gcd c b := Nat.dvd_gcd hq_dvd_c hq_dvd_b
      have : q ∣ 1 := by simpa [hcop.gcd_eq_one] using this
      exact hq.not_dvd_one this

    have hq_ndvd_diff : ¬ q ∣ c - b := by
      intro hqd
      have hq_dvd_3k : q ∣ 3 * k := by simpa [hk] using hqd
      rcases hq.dvd_mul.mp hq_dvd_3k with hq3 | hqk
      · exact hq_ndvd_three hq3
      · exact hq_ndvd_k hqk

    have hS0 : S0_nat c b = 3 * m := by
      unfold S0_nat
      dsimp [m]
      rw [hc_eq]
      ring
    have hq_dvd_S0 : q ∣ S0_nat c b := by
      have : q ∣ 3 * m := dvd_mul_of_dvd_right hq_dvd_m 3
      simpa [hS0] using this

    have hdiff : c ^ 3 - b ^ 3 = (c - b) * (c ^ 2 + c * b + b ^ 2) := by
      have h_pow : b ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left hbc.le 3
      zify [hbc, h_pow]
      ring_nf
    have hfact : c ^ 3 - b ^ 3 = (c - b) * S0_nat c b := by
      simpa [S0_nat] using hdiff
    have hq_dvd_diff : q ∣ c ^ 3 - b ^ 3 := by
      rw [hfact]
      exact dvd_mul_of_dvd_right hq_dvd_S0 (c - b)

    exact ⟨q, hq, hq_dvd_diff, hq_ndvd_diff⟩

  · exact exists_primitive_prime_factor_prime Nat.prime_three
      (by norm_num : 3 ≤ 3) hbc hb hcop h3

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

  have hcop_cb : Nat.Coprime c b := coprime_cb_of_eq hab h_eq
  have hbc : b < c := by
    by_contra hbc_not
    have hcb : c ≤ b := Nat.not_lt.mp hbc_not
    have hc3_le : c ^ 3 ≤ b ^ 3 := Nat.pow_le_pow_left hcb 3
    have hsum_le : a ^ 3 + b ^ 3 ≤ b ^ 3 := by simpa [h_eq] using hc3_le
    have ha3_pos : 0 < a ^ 3 := by positivity
    omega

  obtain ⟨q, hq_prime, hq_dvd_diff, hq_ndiv_diff⟩ :=
    exists_prime_factor_cube_diff hbc hb hcop_cb

  have hsub : c ^ 3 - b ^ 3 = a ^ 3 := cube_sub_eq_of_add_eq h_eq
  have hq_dvd_a3 : q ∣ a ^ 3 := by simpa [hsub] using hq_dvd_diff
  have hq_dvd_a : q ∣ a := hq_prime.dvd_of_dvd_pow hq_dvd_a3

  have h_lower_a3 : 3 ≤ padicValNat q (a ^ 3) :=
    padicValNat_lower_bound_of_dvd_d3 ha hq_prime hq_dvd_a
  have h_lower : 3 ≤ padicValNat q (c ^ 3 - b ^ 3) := by
    simpa [hsub] using h_lower_a3

  have h_upper : padicValNat q (c ^ 3 - b ^ 3) ≤ 1 :=
    padicValNat_upper_bound_d3 hbc hc hb hcop_cb hq_prime hq_dvd_diff hq_ndiv_diff

  have : (3 : ℕ) ≤ 1 := le_trans h_lower h_upper
  omega

end DkMath.FLT
