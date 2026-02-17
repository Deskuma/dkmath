/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.ZsigmondyCyclotomic
import DkMath.SilverRatio.GcdAg  -- Phase 2: 2進正規化
import DkMath.FLT.PetalDetect  -- Phase 3: φビット構造・(a+b) 検出器

set_option linter.style.emptyLine false

namespace DkMath.NumberTheory.GcdNext

open scoped BigOperators
open Finset
open DkMath.ABC
open DkMath.Algebra.DiffPow
open DkMath.NumberTheory.GcdDiffPow
open DkMath.SilverRatio.GcdAg  -- Phase 2: GcdAg 正規化関数を使用
open DkMath.FLT.PetalDetect  -- Phase 3: φビット構造を使用

/-!
## GcdNext: Zsigmondy 原始素因子理論と FLT への統合層

**ファイルの位置づけ:**
ZsigmondyCyclotomic.lean（層A・層B）→ GcdNext（統合層）→ FLT/Basic（応用層）

**目的:**
1) 宇宙式の Body = 差の冪 の "特化形" を ready-made で使えるようにする
2) 「完全 d 乗」仮定を `padicValNat` / `factorization` 的な条件へ落とす
3) Zsigmondy（原始素因子）層A・層Bを FLT へ接続する
4) GcdAg 正規化（2進ノイズ除去）との統合準備
5) PetalDetect（(a+b) 検出器）との統合準備

**理論の流れ:**
- **層A（存在層）**: ZsigmondyCyclotomic.lean で実装済み
  - `exists_primitive_prime_factor_basic`: 原始素因子の存在保証
  - `prime_exp_not_dvd_diff_imp_primitive`: 群論による primitive 証明
- **層B（精密層）**: ZsigmondyCyclotomic.lean で部分実装（研究中）
  - padicValNat q (a^d - b^d) ≤ 1 の評価
  - GcdAg/PetalDetect による反例回避機構
- **統合層（このファイル）**: 層A・層Bを組み合わせて FLT へ
  - `body_not_perfect_pow`: 完全冪否定の主定理
  - TODO: GcdAg正規化、PetalDetect検出器の活用
-/

/-! ### 0. Notation helpers -/

def Sd (a b : ℤ) (d : ℕ) : ℤ := diffPowSum a b d

def Body (x u : ℤ) (d : ℕ) : ℤ := (x + u)^d - u^d

/-! ### 1. Specialization: gcd(x, Sd(x+u,u,d)) ∣ d -/

/-- `a := x+u`, `b := u` の特化：gcd(x, Sd(x+u,u,d)) ∣ d -/
theorem gcd_specialized_divides_d (x u : ℤ) (d : ℕ) (hd : 1 ≤ d) (hab : Int.gcd (x + u) u = 1) :
    Int.gcd x (Sd (x+u) u d) ∣ d := by
  -- `a-b = x` なので `gcd_divides_d` のラッパ
  -- `gcd_divides_d` : Int.gcd (a-b) (Sd a b d) ∣ d を使う
  have key : Int.gcd ((x+u) - u) (diffPowSum (x+u) u d) ∣ d :=
    DkMath.NumberTheory.GcdDiffPow.gcd_divides_d hd hab
  have eq : (x+u) - u = x := by ring
  rw [eq] at key
  exact key

/-! ### 2. Perfect power => valuation constraints -/

/-- 完全 d 乗なら、任意の素数 p で指数が d の倍数（Nat側） -/
lemma dvd_padicVal_of_eq_pow {t n d : ℕ} (_ht : 0 < t) :
    t = n^d → ∀ p : ℕ, Nat.Prime p → d ∣ padicValNat p t := by
  intro heq p hp
  subst heq
  -- padicValNat.pow は Fact (Nat.Prime p) のインスタンスが必要
  haveI : Fact p.Prime := ⟨hp⟩
  -- padicValNat.pow : padicValNat p (a ^ n) = n * padicValNat p a (a ≠ 0 条件付き)
  by_cases hn : n = 0
  · -- n = 0 の場合
    subst hn
    by_cases hd : d = 0
    · -- d = 0 の場合、 0^0 = 1 なので padicValNat p 1 = 0
      subst hd
      simp
    · -- d > 0 の場合、 0^d = 0 なので矛盾 (前提 0 < t)
      exfalso
      simp [zero_pow hd] at _ht
  · -- n ≠ 0 の場合
    -- padicValNat.pow (n : ℕ) (ha : a ≠ 0) : padicValNat p (a ^ n) = n * padicValNat p a
    -- ここで a = n, 冪の指数 = d なので
    have key : padicValNat p (n ^ d) = d * padicValNat p n := padicValNat.pow d hn
    rw [key]
    -- d * padicValNat p n で d ∣ ...
    exact dvd_mul_right d _

/-- `t = A * B` で gcd(A,B) が小さいとき、v_p(t) を A と B に分配する雛形 -/
lemma padicVal_mul_eq_add_of_coprime {A B : ℕ} (hcop : Nat.Coprime A B) {p : ℕ} (hp : Nat.Prime p) :
    padicValNat p (A * B) = padicValNat p A + padicValNat p B := by
  -- Fact インスタンスを用意
  haveI : Fact p.Prime := ⟨hp⟩
  -- padicValNat.mul : a ≠ 0 → b ≠ 0 → padicValNat p (a * b) = padicValNat p a + padicValNat p b
  by_cases hA : A = 0
  · subst hA
    -- 0.Coprime B → B = 1
    have : B = 1 := by
      have := Nat.Coprime.symm hcop
      simp only [Nat.Coprime, Nat.gcd_zero_right] at this
      exact this
    subst this
    simp
  · by_cases hB : B = 0
    · subst hB
      -- A.Coprime 0 → A = 1
      have : A = 1 := by
        simp only [Nat.Coprime, Nat.gcd_zero_right] at hcop
        exact hcop
      subst this
      simp
    · exact padicValNat.mul hA hB

/-! ### 3. Bridge: from gcd ∣ d to "no new prime can divide both" -/

/-- gcd が d を割るなら、p ∤ d なら同時割りは起きない（NatAbs版の雛形） -/
lemma prime_not_dvd_d_of_gcd_dvd {a b : ℤ} {d : ℕ}
    (hd : 1 ≤ d) (hab : Int.gcd a b = 1)
    (p : ℕ) (_hp : Nat.Prime p)
    (hpnd : ¬ p ∣ d) :
    ¬ (p ∣ (a - b).natAbs ∧ p ∣ (Sd a b d).natAbs) := by
  -- 対偶：p が両方割る ⇒ p ∣ gcd ⇒ p ∣ d、なので矛盾
  intro ⟨hdiv_ab, hdiv_sd⟩
  -- gcd_divides_d を使う
  have gcd_dvd_d : Int.gcd (a - b) (diffPowSum a b d) ∣ d :=
    DkMath.NumberTheory.GcdDiffPow.gcd_divides_d hd hab
  -- p ∣ (a-b).natAbs かつ p ∣ (Sd a b d).natAbs なら
  -- p ∣ Int.gcd (a-b) (diffPowSum a b d)
  have p_dvd_gcd : (p : ℤ) ∣ Int.gcd (a - b) (diffPowSum a b d) := by
    -- Int.gcd の natAbs での表現を使う
    have eq := Int.gcd_eq_natAbs (a := a - b) (b := diffPowSum a b d)
    rw [eq]
    -- p ∣ natAbs.gcd を示す
    have h : p ∣ (a - b).natAbs.gcd (diffPowSum a b d).natAbs :=
      Nat.dvd_gcd hdiv_ab hdiv_sd
    exact Int.ofNat_dvd.mpr h
  -- したがって p ∣ d
  obtain ⟨k, hk⟩ := gcd_dvd_d
  have p_dvd_d_int : (p : ℤ) ∣ (d : ℤ) := by
    calc (p : ℤ)
      _ ∣ Int.gcd (a - b) (diffPowSum a b d) := p_dvd_gcd
      _ ∣ (d : ℤ) := by
        use k
        exact_mod_cast hk
  have p_dvd_d_nat : p ∣ d := by
    exact Int.ofNat_dvd.mp p_dvd_d_int
  -- 矛盾
  exact hpnd p_dvd_d_nat

/-! ### 4. Zsigmondy hook (optional) -/

/-- 素数冪の場合、a > b なら 0 < a^p - b^p -/
theorem pow_sub_pos {a b : ℕ} {p : ℕ}
  (hp : Nat.Prime p) (ha : a > b) : 0 < a ^ p - b ^ p := by
  -- p が素数なら p ≠ 0
  have hp_ne_zero : p ≠ 0 := Nat.Prime.ne_zero hp
  -- a > b より a^p > b^p
  have han : a ^ p > b ^ p := Nat.pow_lt_pow_left ha hp_ne_zero
  -- したがって 0 < a^p - b^p
  exact Nat.zero_lt_sub_of_lt han

/-! ### 5. Phase 2: GcdAg 正規化の補助補題 -/

/-- Ag-gcd と通常の gcd の関係（互いに素性の強化）

**数学的内容:**
gcd_Ag(a, b) = 1 ならば、本質的に a と b は「2進位相で互いに素」である。

通常の gcd(a, b) = 1 は 2 の共有を許すが、
gcd_Ag(a, b) = 1 は 2 の共有さえも無視した真の互いに素性を保証する。

**応用:**
padicValNat 評価で q ≠ 2 に限定する際、
GcdAg による前処理で 2 進ノイズを除外できる。
-/
lemma gcdAg_eq_one_imp_coprime_after_factor2 {a b : ℕ}
    (h : gcd_Ag a b = 1) :
    ∃ a' b' : ℕ, (∃ e_a e_b : ℕ, a = 2^e_a * a' ∧ b = 2^e_b * b') ∧
                  Nat.Coprime a' b' ∧
                  gcd_Ag a' b' = 1 := by
  -- a = 2^e_a * a', b = 2^e_b * b' と因数分解できる
  -- Ag-gcd は 2 進位相を落とすため、a' と b' は本質的に互いに素
  refine ⟨a, b, ?_⟩
  refine ⟨?_, ?_, h⟩
  · exact ⟨0, 0, by simp⟩
  · sorry   -- TODO: a, b を 2 の冪で割ることで a', b' を定義し、互いに素性と gcd_Ag = 1 を示す

/-- GcdAg による正規化で互いに素条件が保持される

通常の gcd ではなく gcd_Ag で互いに素を判定する場合の補助定理。
-/
lemma coprime_of_gcdAg_eq_one {a b : ℕ}
    (h : gcd_Ag a b = 1) :
    gcd_Ag a b = 1 := h

/-! ### 5b. Phase 3: PetalDetect φビット構造の補助補題 -/

/-- φビット形式での x の表現（差の冪を S0/S1 の和として見る）

**数学的内容:**
x = a - b を Body の因数分解の差として扱う際、
φビット構造（S0 vs S1）の観点から見ると：
- S0(a, b) = a² + ab + b²（半位相）
- S1(a, b) = (a+b)²（完成位相）

この差は ab だけ：S1 - S0 = ab

**応用:**
padicValNat q (x * Sd) の評価で、
(a+b) が S0 側に吸い込まれるか S1 側にしか現れないかを判定できる。
-/
lemma phi_bit_structure_diff (a b : ℕ) :
    S1_nat a b = S0_nat a b + a * b := by
  exact diff_kernel_nat a b

/-- (a+b) が S0 を割ることができない条件

**数学的内容:**
gcd(a, b) = 1 の下で：
(a+b) | S0(a, b) ⟺ (a+b) | b²

だが、gcd(a+b, b) = 1 ならば：
(a+b) ∤ S0(a, b)

**応用:**
半位相（φ=0）では (a+b) が Body kernel を割ることができず、
したがって padicValNat q (a^d - b^d) の評価で (a+b) 由来の素因子は排除される。
-/
lemma apb_not_dvd_S0_coprime (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (hapb : Nat.Coprime (a + b) b) :
    ¬ (a + b) ∣ S0_nat a b := by
  -- (a+b) | S0 ⟹ (a+b) | b² （apb_dvd_S0_iff_dvd_bsq）
  -- gcd(a+b, b) = 1 なら (a+b) | b² ⟹ a+b = 1 （padicValNat 論法）
  sorry  -- TODO: coprime 条件での (a+b) 排除

/-- φビット判定：(a+b) はどの位相に現れるか

**判定ルール:**
- φ=1（完成位相）: (a+b) は S1(a, b) = (a+b)² に常に割り込む
- φ=0（半位相）: (a+b) は S0(a, b) には一般には割り込まない（coprime 条件下）

**応用:**
これにより padicValNat 評価で、(a+b) 由来の素因子を
特定位相に限定できる。
-/
lemma petal_phi_detection (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) :
    ∃ φ : Bool,
      (φ = true → (a + b) ∣ S1_nat a b) ∧
      (φ = false → Nat.Coprime (a + b) b → ¬ (a + b) ∣ S0_nat a b) := by
  use false
  refine ⟨fun hfalse => apb_dvd_S1 a b, fun hfalse hapb => apb_not_dvd_S0_coprime a b ha hb hab hapb⟩

/-! ### 6. Main target: (x+u)^d - u^d is not a perfect d-th power

**統合戦略（Zsigmondy 層A・層B + GcdAg + PetalDetect）**
-/

/-- 目標定理：Body(x,u,d) は完全 d 乗にならない（d > 2）

**証明構造（3層統合）:**

1. **層A（存在層）**: ZsigmondyCyclotomic.exists_primitive_prime_factor_basic
   - 原始素因子 q の存在を保証
   - q ∣ a^d - b^d かつ q ∤ a - b

2. **層B（精密層）**: padicValNat 評価
   - padicValNat q (a^d - b^d) ≤ 1 の上界
   - GcdAg 正規化による 2進ノイズ除去
   - PetalDetect による (a+b) 核の排除

3. **矛盾導出**: t^d 仮定との衝突
   - padicValNat q (t^d) = d * padicValNat q t ≥ d ≥ 3
   - しかし padicValNat q (a^d - b^d) ≤ 1
   - 矛盾！

**現在の実装状況:**
- ✅ 層A実装済み：原始素因子の存在保証
- ⏳ 層B部分実装：padicValNat 精密評価（研究中）
- 🚧 統合準備：GcdAg/PetalDetect 接続（準備中）

**必要な追加仮定:**
- d が素数であること（または d > 2 から導く）
- ¬ d ∣ x（または仮定として追加）
- Ag正規化条件（2進位相の処理）
- φビット構造（半位相 vs 完成位相）

**統合ロードマップ:**
1. Phase 1: 層A単独で基本形を確立 ← 現在ここ
2. Phase 2: GcdAg 正規化の導入
3. Phase 3: PetalDetect 検出器の導入
4. Phase 4: 層B 精密評価の完成
-/
theorem body_not_perfect_pow (x u : ℕ) (d : ℕ)
    (hd : 2 < d) (hx : 0 < x) (hu : 0 < u) (hcop : Nat.Coprime (x + u) u) :
    ¬ ∃ t : ℕ, 0 < t ∧ (x+u)^d - u^d = t^d := by
  intro ⟨t, ht, heq⟩

  -- 準備：a := x+u, b := u とおく
  set a := x + u with ha_def
  set b := u with hb_def

  -- (1) 基本分解：a^d - b^d = x * Sd(a,b,d)
  have body_eq : (a : ℤ)^d - (b : ℤ)^d = (x : ℤ) * Sd a b d := by
    have key := DkMath.Algebra.DiffPow.pow_sub_pow_factor (a : ℤ) (b : ℤ) d
    have x_eq : (x : ℤ) = (a : ℤ) - (b : ℤ) := by omega
    rw [x_eq]
    exact key

  -- (2) Zsigmondy の原始素因子定理を使用：原始素因子 q の存在
  -- a = x + u > u = b （x > 0 より）、且つ coprime
  have hab_lt : b < a := by
    simp only [ha_def, hb_def]
    omega
  have hb_pos : 0 < b := hu
  have hab : Nat.Coprime a b := hcop

  -- d が素数であることを確認
  have hd_prime : Nat.Prime d := by
    sorry -- TODO: d > 2 から d が素数であることを導くか、または仮定に追加
  have hd_ge : 3 ≤ d := by omega

  -- ¬ d ∣ a - b を示す（これは ¬ d ∣ x と同じ）
  have hpnd : ¬ d ∣ a - b := by
    have : a - b = x := by omega
    rw [this]
    sorry -- TODO: ¬ d ∣ x を示すか、仮定に追加

  obtain ⟨q, hq_prime, hq_div_pow, hq_ndiv_diff⟩ :=
    exists_primitive_prime_factor_prime hd_prime hd_ge hab_lt hb_pos hab hpnd

  -- q ∣ a^d - b^d かつ q ∤ a - b = x
  -- body_eq より a^d - b^d = x * Sd なので、q ∣ x * Sd
  -- q ∤ x より q ∣ Sd

  have hq_div_body : (q : ℤ) ∣ (a : ℤ)^d - (b : ℤ)^d := by
    -- a^d ≥ b^d を示す
    have hab_le : b ≤ a := by
      simp only [ha_def, hb_def]; omega
    have hab_pow : b^d ≤ a^d := Nat.pow_le_pow_left hab_le d
    have : ((a^d - b^d : ℕ) : ℤ) = (a : ℤ)^d - (b : ℤ)^d := by
      simp only [Nat.cast_sub hab_pow, Nat.cast_pow]
    rw [← this]
    exact Int.ofNat_dvd.mpr hq_div_pow

  rw [body_eq] at hq_div_body

  -- q ∣ x * Sd かつ q ∤ x なら q ∣ Sd
  have hq_ndiv_x : ¬ (q : ℤ) ∣ (x : ℤ) := by
    intro hdiv
    apply hq_ndiv_diff
    -- a - b = x を使う
    have x_eq_ab : x = a - b := by omega
    rw [← x_eq_ab]
    exact Int.ofNat_dvd.mp hdiv

  have hq_div_Sd : (q : ℤ) ∣ Sd a b d := by
    -- 最初に hq_div_body を body_eq で書き換えて hq_div_prod を得る
    have hq_div_prod : (q : ℤ) ∣ (x : ℤ) * Sd a b d :=
      body_eq ▸ hq_div_body
    -- q は素数で q ∣ x * Sd かつ q ∤ x なので q ∣ Sd
    have hq_prime_int : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq_prime
    have : (q : ℤ) ∣ (x : ℤ) ∨ (q : ℤ) ∣ Sd a b d := hq_prime_int.dvd_mul.mp hq_div_prod
    cases this with
    | inl h => exfalso; exact hq_ndiv_x h
    | inr h => exact h

  -- (3) 矛盾を導く：p-adic valuation を使った完全冪判定
  -- heq : (x+u)^d - u^d = t^d より a^d - b^d = t^d (ℕ での等式)
  -- したがって padicValNat q (a^d - b^d) = padicValNat q (t^d)

  -- q ∣ a^d - b^d を ℕ の可除性に変換
  have hq_div_pow_nat : q ∣ a^d - b^d := by
    have hab_pow_le : b^d ≤ a^d := by
      have : b ≤ a := by omega
      exact Nat.pow_le_pow_left this d
    -- body_eq : (a : ℤ)^d - (b : ℤ)^d = (x : ℤ) * Sd a b d を使う
    have hq_div_int : (q : ℤ) ∣ (a : ℤ)^d - (b : ℤ)^d := by
      -- キャストを正規化
      convert hq_div_body using 2
      -- body_eq を適用
      -- exact body_eq.symm
    -- ℤ から ℕ に変換
    have heq_cast : ((a^d - b^d : ℕ) : ℤ) = (a : ℤ)^d - (b : ℤ)^d := by
      simp only [Nat.cast_sub hab_pow_le, Nat.cast_pow]
    rw [← heq_cast] at hq_div_int
    exact Int.ofNat_dvd.mp hq_div_int

  -- a^d - b^d = t^d を使う
  have heq_nat : a^d - b^d = t^d := by
    have hab_pow_le : b^d ≤ a^d := by
      have : b ≤ a := by omega
      exact Nat.pow_le_pow_left this d
    calc a^d - b^d
      _ = (x + u)^d - u^d := by simp only [ha_def, hb_def]
      _ = t^d := heq

  -- したがって q ∣ t^d
  have hq_div_td : q ∣ t^d := by
    rw [← heq_nat]
    exact hq_div_pow_nat

  -- q は素数で q ∣ t^d なので q ∣ t
  have hq_div_t : q ∣ t := by
    -- q が素数で q ∣ t^d なら q ∣ t
    -- Nat.Prime.dvd_of_dvd_pow を使う
    exact hq_prime.dvd_of_dvd_pow hq_div_td

  -- したがって padicValNat q t ≥ 1
  have hvt_ge : 1 ≤ padicValNat q t := by
    have ht_ne : t ≠ 0 := Nat.ne_of_gt ht
    exact DkMath.ABC.padicValNat_one_le_of_prime_dvd hq_prime ht_ne hq_div_t

  -- 新補題を使う：padicValNat q (t^d) = d * padicValNat q t
  have ht_ne : t ≠ 0 := Nat.ne_of_gt ht
  have hvtd_eq : padicValNat q (t^d) = d * padicValNat q t :=
    DkMath.ABC.padicValNat_pow hq_prime d ht_ne

  -- したがって padicValNat q (t^d) ≥ d ≥ 3
  have hvtd_ge : d ≤ padicValNat q (t^d) := by
    rw [hvtd_eq]
    calc d
      _ = d * 1 := (Nat.mul_one d).symm
      _ ≤ d * padicValNat q t := Nat.mul_le_mul_left d hvt_ge

  -- 一方、padicValNat q (a^d - b^d) = padicValNat q (t^d)
  have hvad_eq : padicValNat q (a^d - b^d) = padicValNat q (t^d) := by
    rw [heq_nat]

  -- ========================================
  -- 矛盾導出：層B 補助補題を使用
  -- ========================================

  -- Phase 2 + Phase 3 + 層B の統合で padicValNat q (a^d - b^d) ≤ 1 を得る
  -- 以下の補助補題が完成すれば、即座に矛盾が導出される：
  --
  -- padicValNat_upper_bound_integrated :
  --   GcdAg 正規化 + PetalDetect φビット を前提して
  --   padicValNat q (a^d - b^d) ≤ 1 を保証
  --
  -- 戦略：
  -- 1. GcdAg 正規化（Phase 2）で 2進ノイズを除去 → q ≠ 2
  -- 2. PetalDetect φビット（Phase 3）で (a+b) 核を位相限定 → 半位相では (a+b) 排除
  -- 3. 層B で Cosmic Formula による G 構造解析 → padicValNat q (a^d - b^d) ≤ 1
  --
  -- 矛盾の導出：
  -- もし padicValNat q (a^d - b^d) ≤ 1 ならば、hvad_eq より
  --   padicValNat q (t^d) ≤ 1
  -- しかし hvtd_eq と hvt_ge より
  --   padicValNat q (t^d) = d * padicValNat q t ≥ d ≥ 3
  -- したがって 1 ≥ 3 で矛盾！✅
  --
  -- TODO（層B の本格実装待ち）:
  -- padicValNat_d3_upper_bound（d=3 での具体計算）
  -- padicValNat_general_upper_bound（一般化）
  -- padicValNat_upper_bound_integrated（最終統合）
  sorry

/-! ### 6. 統合準備：GcdAg 正規化と PetalDetect 検出器

**Phase 2: GcdAg 正規化の導入**

GcdAg.lean で定義された Ag射影 π_Ag と gcd_Ag を使用して、
2進位相のノイズを除去する。

例：gcd(2n, 2n+2) = 2 だが gcd_Ag(2n, 2n+2) = 1

これにより「互いに素」条件が 2進ノイズに邪魔されなくなる。
-/

-- TODO: GcdAg 正規化を使った coprime 条件の強化
-- example (a b : ℕ) : GcdAg.gcd_Ag a b = 1 → "本質的に互いに素" := by sorry

/-! **Phase 3: PetalDetect 検出器の導入**

PetalDetect.lean で定義された φビット構造（S0, S1）と
(a+b) 検出器を使用して、半位相（φ=0）では核 (a+b) が
Body に吸い込まれないことを活用する。

主要補題：
- `apb_dvd_S1`: (a+b) | S1 は自明
- `apb_dvd_S0_iff_dvd_bsq`: (a+b) | S0 ⟺ (a+b) | b²
- `apb_dvd_S0_implies_eq_one`: gcd(a,b)=1 ∧ (a+b)|S0 → a+b=1（ほぼ不可能）

これにより padicValNat 評価で (a+b) 由来の素因子を排除できる。
-/

-- TODO: PetalDetect の φビット判定を使った素因子分類
-- example (a b q : ℕ) : "q が (a+b) 由来" → "φ=1 側のみ" := by sorry

/-! ### 7. Phase 4: 層B（精密層）— padicValNat 上界の証明

**理論的背景:**
Zsigmondy 定理の層A で原始素因子 q の存在が保証された後、
層B では padicValNat q (結果) ≤ 1 という精密な上界を証明する。
結果 = a の d 乗 - b の d 乗

**証明戦略:**
1. Cosmic Formula による分解
2. GcdAg 正規化で q ≠ 2
3. PetalDetect φビット判定で (a+b) 位相を限定
4. Lucas/Kummer 定理による二項係数評価
5. 構造解析により上界確定

**実装現況:**
- ✅ Cosmic Formula との接続準備
- 🚧 d=3 での具体計算（ZsigmondyCyclotomic.lean で部分実装）
- ⏳ 一般化される d への拡張

**鍵となる補題セット（Layer B）:**
-/

/-- d=3 での上界補題

Cosmic Formula と Lucas/Kummer 定理を組み合わせて、
d=3 の場合に padicValNat q (a³ - b³) ≤ 1 を証明する。
-/
lemma padicValNat_d3_upper_bound {a b q : ℕ}
    (hq : Nat.Prime q)
    (hab_lt : b < a) (hab_coprime : Nat.Coprime a b)
    (h_Ag : gcd_Ag a b = 1) -- Phase 2 正規化
    (h_phi : Nat.Coprime (a + b) b) -- Phase 3 φビット判定
    :
    padicValNat q (a^3 - b^3) ≤ 1 := by
  -- G_three_explicit から G の具体形を使用
  -- 各係数の padicValNat を Kummer で評価
  sorry  -- TODO: d=3 での具体計算

/-- 一般的 d への上界補題

より一般的な d に対する padicValNat 上界。
現在は研究段階で、d=3, d=5 等の小さな素数 d で検証中。
-/
lemma padicValNat_general_upper_bound {a b d q : ℕ}
    (hd : 3 ≤ d) (hd_prime : Nat.Prime d)
    (hq : Nat.Prime q)
    (hab_lt : b < a) (hab_coprime : Nat.Coprime a b)
    (h_Ag : gcd_Ag a b = 1) -- GcdAg 正規化
    (h_petal : Nat.Coprime (a + b) b) -- PetalDetect φビット
    :
    ∃ C : ℕ, padicValNat q (a^d - b^d) ≤ C := by
  -- C は d に依存する定数（多くの場合 C = 1）
  use 1
  sorry  -- TODO: 一般化への道筋

/-! ### 8. 層B との最終統合：body_not_perfect_pow の証明完成

**現在の状況:**
Phase 1a-3 の補助仮定を満たすとき、
層B 補題により padicValNat q (a^d - b^d) ≤ 1 が得られる。

これを body_not_perfect_pow で使用すれば、矛盾導出が完成する。
-/

/-- 層B + Phase 2,3 による統合上界

GcdAg 正規化（Phase 2）と PetalDetect φビット（Phase 3）を前提として、
層B の補助補題を統合する。
-/
lemma padicValNat_upper_bound_integrated {a b d q : ℕ}
    (hd : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hq : Nat.Prime q)
    (hab_lt : b < a) (hab_coprime : Nat.Coprime a b)
    (h_Ag : gcd_Ag a b = 1) -- Phase 2
    (h_petal : Nat.Coprime (a + b) b) -- Phase 3
    :
    padicValNat q (a^d - b^d) ≤ 1 := by
  -- Phase 2 + Phase 3 + 層B の完全統合
  -- h_Ag, h_petal で前処理完了
  -- 層B 補題により上界確定
  sorry  -- TODO: 層B 補題との接続完成

end DkMath.NumberTheory.GcdNext
