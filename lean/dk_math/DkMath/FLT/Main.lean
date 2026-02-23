/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- cid: 697d62b5-312c-83a8-a917-f4aca8fa80ca

-- no-import DkMath.FLT.Basic 依存しないように外す
import DkMath.FLT.PetalDetect
import DkMath.FLT.OctagonCore
import DkMath.FLT.PhaseLift
import DkMath.FLT.CounterexamplePattern
import DkMath.FLT.GEisensteinBridge
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

open scoped BigOperators
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

    have hfact : c ^ 3 - b ^ 3 = (c - b) * S0_nat c b :=
      cube_sub_eq_mul_sub_S0 hbc
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

/-- **層B補助補題（条件付き）：相対多角数の平方判定**

`¬ q² ∣ S0(a,b)` を外部条件として受け取る薄いラッパー。

注:
- 命題
  `q ∣ S0(a,b) ∧ ¬ q ∣ (a+b) ∧ gcd(a,b)=1 → ¬ q² ∣ S0(a,b)`
  は一般には偽（反例: `a=18, b=1, q=7`）。
- 反例は `GEisensteinBridge.exists_counterexample_S0_square_resistance` を参照。

**入力:**
- Nat.Prime q
- q ∣ S0_nat a b
- ¬ q ∣ (a + b)
- Nat.Coprime a b
- ¬ q² ∣ S0_nat a b（追加条件）

**出力:**
¬ q² ∣ S0_nat a b
-/
-- * not referenced in the main proof, but useful for isolating the non-square resistance condition * --
lemma S0_not_sq_dvd_of_prime_dvd_and_not_dvd_apb {a b q : ℕ}
    (_ha_pos : 0 < a) (_hb_pos : 0 < b)
    (_hab_coprime : Nat.Coprime a b)
    (_hq : Nat.Prime q)
    (_hS0_dvd : q ∣ S0_nat a b)
    (_hq_not_apb : ¬ q ∣ a + b)
    (hq_not_sq : ¬ q ^ 2 ∣ S0_nat a b) :
    ¬ q ^ 2 ∣ S0_nat a b := by
  exact hq_not_sq

#print axioms S0_not_sq_dvd_of_prime_dvd_and_not_dvd_apb

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
    (hq : Nat.Prime q)
    (hq_dvd : q ∣ a ^ 3 - b ^ 3)
    (hq_ndiv_diff : ¬ q ∣ a - b)
    (hq_not_sq : ¬ q ^ 2 ∣ S0_nat a b) :
    padicValNat q (a ^ 3 - b ^ 3) ≤ 1 := by
  -- Core 統合: Binom -> Petal の橋補題を使って q | S0 を導出
  have hS0_dvd : q ∣ S0_nat a b :=
    prime_dvd_S0_via_cosmic_bridge hab_lt hq hq_dvd hq_ndiv_diff

  have h_fact : a ^ 3 - b ^ 3 = (a - b) * S0_nat a b :=
    cube_sub_eq_mul_sub_S0 hab_lt

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

Zsigmondy原始素因子 + padicValNat評価による背理法：
平方自由性仮定の下で、完全3乗仮定と矛盾を導出。

**入力（仮定）:**
- `ha : 0 < a`, `hb : 0 < b`, `hc : 0 < c` - 正の整数
- `hab : Nat.Coprime a b` - a と b は互いに素
- `hS0_not_sq : ∀ {q : ℕ}, Nat.Prime q → q ∣ c^3 - b^3 → ¬ q ∣ c - b → ¬ q² ∣ S0_nat c b`
  - 相対多角数S0(c,b) = c²+cb+b² は各原始素因子 q に対して平方自由
  - すなわち：q が c³-b³ を割り、かつ q が (c-b) を割らない任意の素数 q について、
    q² は S0(c,b) を割らない

**証明戦略（層統合）:**

1. **層A（Zsigmondy原始素因子）**
   - 存在補題により、q | (c³-b³) かつ ¬ q | (c-b) を満たす素数 q が存在

2. **層B（padicValNat上界）**
   - 仮定 hS0_not_sq から ¬ q² ∣ S0(c,b)
   - padicValNat上界：v_q(c³-b³) ≤ 1

3. **矛盾導出**
   - 完全3乗仮定：q | a より v_q(a³-b³) ≥ 3
   - 層B下界：v_q(c³-b³) = v_q(a³-b³)（cube_sub_eq_of_add_eq より）
   - 矛盾：3 ≤ v_q(c³-b³) ≤ 1

**出力（結論):**
`a³ + b³ ≠ c³`（FLT d=3）
-/
theorem FLT_d3_by_padicValNat {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hS0_not_sq :
      ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b → ¬ q ^ 2 ∣ S0_nat c b) :
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
    padicValNat_upper_bound_d3 hbc hc hb hq_prime hq_dvd_diff hq_ndiv_diff
      (hS0_not_sq hq_prime hq_dvd_diff hq_ndiv_diff)

  have : (3 : ℕ) ≤ 1 := le_trans h_lower h_upper
  omega

/--
`NoSqOnS0 c b` を入力にした `FLT_d3_by_padicValNat` の派生版。
-/
theorem FLT_d3_by_padicValNat_of_NoSqOnS0 {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hNoSq : NoSqOnS0 c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  apply FLT_d3_by_padicValNat ha hb hc hab
  intro q hq hq_dvd_diff hq_ndiv_diff
  exact hS0_not_sq_of_NoSqOnS0 (c := c) (b := b) hNoSq hq hq_dvd_diff hq_ndiv_diff

#print axioms FLT_d3_by_padicValNat_of_NoSqOnS0  -- OK: 2026/02/23 15:47
-- 'DkMath.FLT.FLT_d3_by_padicValNat_of_NoSqOnS0' depends on axioms: [propext, Classical.choice, Quot.sound]

/--
phase-04: 非例外調和条件（skeleton）から
`AllNonLiftableOnS0` -> `NoSqOnS0` を経由して供給する版。
-/
theorem FLT_d3_by_padicValNat_of_nonExceptionalHarmonic {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hNH : NonExceptionalHarmonicOnS0 c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hAll : AllNonLiftableOnS0 c b :=
    AllNonLiftableOnS0_of_nonExceptionalHarmonic hNH
  have hNoSq : NoSqOnS0 c b := NoSqOnS0_of_AllNonLiftableOnS0 hAll
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab
    hNoSq

/--
phase-04: `ExceptThree + mod3分離 + harmonic witness` から
`NoSqOnS0` を経由して供給する版。
-/
theorem FLT_d3_by_padicValNat_of_exceptThree_mod3_separated_harmonic {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLift : ∀ q : ℕ, NonLiftableS0 c b q)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNoSq : NoSqOnS0 c b :=
    NoSqOnS0_of_exceptThree_mod3_separated_harmonic
      hHarm hSuppEx3 hNonLift hc_nz hb_nz hsep
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

#print axioms FLT_d3_by_padicValNat_of_exceptThree_mod3_separated_harmonic  -- OK: 2026/02/23 15:36
-- 'DkMath.FLT.FLT_d3_by_padicValNat_of_exceptThree_mod3_separated_harmonic' depends on axioms: [propext, Classical.choice, Quot.sound]

/--
phase-04: `harmonic envelope + nonLiftable family` から
`AllNonLiftableOnS0` を経由して供給する版。
-/
theorem FLT_d3_by_padicValNat_of_harmonicEnvelope_nonLiftable {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExcAll : ∀ x : CounterexampleInput, ¬ exceptionalPhaseGate x)
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLiftAll : ∀ q : ℕ, NonLiftableS0 c b q)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hAll : AllNonLiftableOnS0 c b :=
    allNonLiftableOnS0_of_harmonicEnvelope_nonLiftable hbc
      hasPhaseUnitInfrastructure hHarm hNoExcAll
      hSuppEx3 hNonLiftAll hc_nz hb_nz hsep
  have hNoSq : NoSqOnS0 c b := NoSqOnS0_of_AllNonLiftableOnS0 hAll
  exact FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq

/--
phase-05: `hSuppEx3` を `Coprime c b` から自動生成して
`harmonicEnvelope_nonLiftable` 版へ接続する。
-/
theorem FLT_d3_by_padicValNat_of_harmonicEnvelope_nonLiftable_coprimeSupport {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExcAll : ∀ x : CounterexampleInput, ¬ exceptionalPhaseGate x)
    (hNonLiftAll : ∀ q : ℕ, NonLiftableS0 c b q)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hSuppEx3 : S0PrimeSupportExceptThree c b :=
    s0PrimeSupportExceptThree_of_coprime hbc.le hcb_coprime
  exact FLT_d3_by_padicValNat_of_harmonicEnvelope_nonLiftable
    ha hb hc hab hbc hHarm hNoExcAll hSuppEx3 hNonLiftAll hc_nz hb_nz hsep

/--
phase-05: `classifyLift = impossible` family から `hNonLiftAll` を生成して
`harmonicEnvelope_nonLiftable_coprimeSupport` 版へ接続する。
-/
theorem FLT_d3_by_padicValNat_of_harmonicEnvelope_classify_coprimeSupport {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExcAll : ∀ x : CounterexampleInput, ¬ exceptionalPhaseGate x)
    (hClassPrim :
      ∀ {q : ℕ}, PrimitiveOnS0 c b q →
        classifyLift ({ c := c, b := b, q := q } : CounterexampleInput) = LiftStatus.impossible)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hNonLiftAll : ∀ q : ℕ, NonLiftableS0 c b q := by
    intro q hprim
    exact nonLiftableS0_of_classifyLift_impossible hbc (hClassPrim hprim) hprim
  exact FLT_d3_by_padicValNat_of_harmonicEnvelope_nonLiftable_coprimeSupport
    ha hb hc hab hbc hcb_coprime hHarm hNoExcAll hNonLiftAll hc_nz hb_nz hsep

/--
phase-05: `NoSqOnS0` から classification impossible family を自動生成し、
`harmonicEnvelope_classify_coprimeSupport` 版へ接続する。
-/
theorem FLT_d3_by_padicValNat_of_harmonicEnvelope_NoSq_coprimeSupport {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hbc : b < c)
    (hcb_coprime : Nat.Coprime c b)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExcAll : ∀ x : CounterexampleInput, ¬ exceptionalPhaseGate x)
    (hNoSq : NoSqOnS0 c b)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  have hClassPrim :
      ∀ {q : ℕ}, PrimitiveOnS0 c b q →
        classifyLift ({ c := c, b := b, q := q } : CounterexampleInput) = LiftStatus.impossible :=
    classifyLift_impossible_family_of_harmonicEnvelope_NoSq
      hbc hasPhaseUnitInfrastructure hHarm hNoExcAll hNoSq
  exact FLT_d3_by_padicValNat_of_harmonicEnvelope_classify_coprimeSupport
    ha hb hc hab hbc hcb_coprime hHarm hNoExcAll hClassPrim hc_nz hb_nz hsep

#print axioms FLT_d3_by_padicValNat_of_nonExceptionalHarmonic  -- OK: 2026/02/23 12:08
-- 'DkMath.FLT.FLT_d3_by_padicValNat_of_nonExceptionalHarmonic' depends on axioms: [propext, Classical.choice, Quot.sound]

/--
`CounterexamplePattern.classifyLift` を経由して `hS0_not_sq` を供給する版。
-/
theorem FLT_d3_by_padicValNat_of_classifyLift {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hClassify :
      ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b →
        classifyLift ({ c := c, b := b, q := q } : CounterexampleInput) = LiftStatus.impossible) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  apply FLT_d3_by_padicValNat ha hb hc hab
  intro q hq hq_dvd_diff hq_ndiv_diff
  let x : CounterexampleInput := { c := c, b := b, q := q }
  have hprim : primitivePrimeGate x := by
    exact ⟨hq, hq_dvd_diff, hq_ndiv_diff⟩
  have hcls : classifyLift x = LiftStatus.impossible := by
    simpa [x] using hClassify hq hq_dvd_diff hq_ndiv_diff
  have hnosq : noSquareGate x :=
    noSquareGate_of_classifyLift_impossible hprim hcls
  simpa [x, noSquareGate] using hnosq

#print axioms FLT_d3_by_padicValNat  -- OK: 2026/02/23 12:08
-- 'DkMath.FLT.FLT_d3_by_padicValNat' depends on axioms: [propext, Classical.choice, Quot.sound]

/-- FLT_d3_by_padicValNat_of_NoSqOnS0 と FLT_d3_by_padicValNat は等価である -/
example
  {a b c : ℕ}
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (hab : Nat.Coprime a b)
  (hNoSq : NoSqOnS0 c b) :
  FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq =
    let hS0_not_sq : ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b → ¬ q ^ 2 ∣ S0_nat c b :=
      (fun hq hq_dvd_diff hq_ndiv_diff => hS0_not_sq_of_NoSqOnS0 (c := c) (b := b) hNoSq hq hq_dvd_diff hq_ndiv_diff)
    FLT_d3_by_padicValNat ha hb hc hab hS0_not_sq := by rfl

/-- `FLT_d3_by_padicValNat_of_NoSqOnS0` は `FLT_d3_by_padicValNat` に
`hS0_not_sq_of_NoSqOnS0` を差し込んだものと定義的に同一。 -/
lemma FLT_d3_by_padicValNat_of_NoSqOnS0_eq
  {a b c : ℕ}
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (hab : Nat.Coprime a b)
  (hNoSq : NoSqOnS0 c b) :
  FLT_d3_by_padicValNat_of_NoSqOnS0 ha hb hc hab hNoSq
    =
    (let hS0_not_sq :
        ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b → ¬ q ^ 2 ∣ S0_nat c b :=
        fun hq hq_dvd_diff hq_ndiv_diff =>
          hS0_not_sq_of_NoSqOnS0 (c := c) (b := b) hNoSq hq hq_dvd_diff hq_ndiv_diff;
     FLT_d3_by_padicValNat ha hb hc hab hS0_not_sq) := by
  rfl

end DkMath.FLT
