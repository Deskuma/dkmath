/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Basic
import DkMath.NumberTheory.ZsigmondyCyclotomic
import DkMath.SilverRatio.GcdAg  -- Phase 2: 2進正規化
import DkMath.FLT.PetalDetect  -- Phase 3: φビット構造・(a+b) 検出器

set_option linter.style.emptyLine false
set_option linter.style.longLine false

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

/-- GcdAg による奇数コア部分の互いに素性

**数学的内容:**
gcd_Ag(a, b) = 1 ならば、a と b の奇数コア部分（2の冪を因数分解した残り）は
互いに素であることを示唆する。

**応用:**
奇数コア部分同士が互いに素なら、p ≠ 2 なる素数 p で両者を割ることはできない。
これにより padicValNat q(...) 評価で q ≠ 2 に限定できる。

**現在の実装:**
gcd_Ag(a, b) = 1 という条件を前提として、下位層（層B）での padicValNat 評価へ渡す。
詳細な奇数コア分解は、層B補助補題で処理される。
-/
/- π_Ag 後の互いに素性の確保

`gcd_Ag a b = 1` ⟹ π_Ag a と π_Ag b が互いに素 (基本的同値性)
-/
lemma gcdAg_eq_one_imp_coprime_pi_ag {a b : ℕ}
    (h : gcd_Ag a b = 1) :
    Nat.Coprime (π_Ag a) (π_Ag b) := by
  -- gcd_Ag の定義を展開
  unfold gcd_Ag at h
  -- Coprime ↔ gcd = 1 の同値性
  rw [Nat.coprime_iff_gcd_eq_one]
  exact h

/-! ### 5b. Phase 2/Phase 3 統合：GcdAg正規化と PetalDetect φビット構造

**次のセクションで:**
1. GcdAg正規化による「本質的互いに素性」の確立
2. PetalDetect φビット判定の活用
3. 層Bへの前処理フックの準備
-/

/-! ### 5c. PetalDetect φビット構造の補助補題 -/

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
  intro hS0
  have _hapb_from_hab : Nat.Coprime (a + b) b := (Nat.coprime_add_self_left).2 hab
  have hbsq : (a + b) ∣ b ^ 2 := (apb_dvd_S0_iff_dvd_bsq a b ha hb).1 hS0
  have hapb_pow : Nat.Coprime (a + b) (b ^ 2) :=
    (Nat.coprime_pow_right_iff (n := 2) (by decide) (a + b) b).2 hapb
  have hone : a + b = 1 := Nat.eq_one_of_dvd_coprimes hapb_pow (dvd_refl (a + b)) hbsq
  have htwo : 2 ≤ a + b := by
    calc
      2 = 1 + 1 := by rfl
      _ ≤ a + b := Nat.add_le_add (Nat.succ_le_of_lt ha) (Nat.succ_le_of_lt hb)
  have hne : a + b ≠ 1 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) htwo)
  exact hne hone

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
  refine ⟨fun hfalse => apb_dvd_S1 a b, fun hfalse hapb
                     => apb_not_dvd_S0_coprime a b ha hb hab hapb⟩

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
    (hd : 2 < d) (hd_prime : Nat.Prime d) (hx : 0 < x) (hu : 0 < u)
    (hcop : Nat.Coprime (x + u) u) (hpnd : ¬ d ∣ x) :
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

  -- d が素数であることが仮定で与えられた
  have hd_ge : 3 ≤ d := by omega

  -- ¬ d ∣ a - b を示す（これは ¬ d ∣ x と同じ）
  have hpnd_ab : ¬ d ∣ a - b := by
    have : a - b = x := by omega
    rw [this]
    exact hpnd

  obtain ⟨q, hq_prime, hq_div_pow, hq_ndiv_diff⟩ :=
    exists_primitive_prime_factor_prime hd_prime hd_ge hab_lt hb_pos hab hpnd_ab

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
  -- 層B統合フック：padicValNat 上界評価
  -- ========================================
  --
  -- 以下が完成すれば、矛盾導出が直ちに完了する形：
  --
  -- 命題：padicValNat q (a^d - b^d) ≤ 1  [← 層B補助補題から導出]
  -- 対比：padicValNat q (t^d) ≥ d ≥ 3   [← 上記 hvtd_ge から導出]
  -- 矛盾：hvad_eq より同じ値だが 1 ≥ 3 で矛盾！
  --
  -- 層B補助補題の実装により、以下が得られれば直ちに完成：
  -- padicValNat q (a^d - b^d) ≤ 1

  have hpadic_bound : padicValNat q (a^d - b^d) ≤ 1 := by
    -- **Stage A（確実に埋まる部分）：d=3 の具体計算**
    -- ZsigmondyCyclotomic.leanで既に padicValNat_d3_upper_bound が準備されている
    -- これを使えば、d=3 の場合は 1) GcdNext直接埋め込み可能
    --
    -- 実装パターン（d=3の場合）:
    --   obtain ⟨q, hpq, hq_div⟩ := hprime  -- 層Aから原始素因子 q
    --   have := padicValNat_d3_upper_bound a b q hpq hab_lt hab_coprime h_Ag h_petal
    --   exact this
    --
    -- **Stage B（研究テーマ）：一般 d への拡張**
    -- d ≥ 5 の素数については、以下の統合が必要：
    --
    -- 1. **必要な理論梁**（層B補助補題）
    --    - Lucas/Kummer定理による二項係数のpadicValNat評価
    --    - 円分多項式 Φ_d(a/b) の因子分解
    --    - Cosmic Formula: a^d - b^d = (a-b) · G_d(a,b)
    --    - GcdAg正規化：π_Ag により 2進ノイズ除去
    --    - PetalDetect φビット判定：(a+b) 位相限定
    --
    -- 2. **証明スケッチ（一般d）**
    --    i) 層A: q | a^d - b^d ∧ q ∤ (a-b) より原始素因子 q の存在
    --    ii) Cosmic Formula: a^d - b^d = (a-b) · G_d に分解
    --    iii) q ∤ (a-b) より q | G_d（割り切りの推移）
    --    iv) padicValNat_G_upper_bound により padicValNat q (G_d) ≤ d-1
    --    v) padicValNat の乗法性により
    --       padicValNat q (a^d - b^d) = padicValNat q (a-b) + padicValNat q (G_d)
    --    vi) q ∤ (a-b) より padicValNat q (a-b) = 0
    --    vii) したがって padicValNat q (a^d - b^d) ≤ d-1
    --    viii) GcdAg+PetalDetect条件下で、さらに ≤ 1 に絞り込める
    --
    -- **実装ロードマップ**
    -- Phase 4.1: d=3 での完全実装（現在）
    -- Phase 4.2: d=5, 7 ... での個別検証
    -- Phase 4.3: 一般化パターン認識→汎用補題化
    --
    -- **当ファイルでの即座の対応**
    -- padicValNat_d3_upper_bound が available ならそれを呼ぶ
    -- 一般 d については「存在形」に落として、次フェーズへ預ける
    -- （NextWork.md Phase 1/2/3参照）
    --
    -- **検索対象（Mathlib/ZsigmondyCyclotomic/PetalDetect）**
    -- - padicValNat_d3_upper_bound （ZsigmondyCyclotomic.leanで定義予定）
    -- - Cosmic Formula分解：DkMath.Algebra.DiffPow
    -- - Lucas/Kummer定理：ZsigmondyCyclotomic.lean
    -- - GcdAg正規化：DkMath.SilverRatio.GcdAg
    -- - PetalDetect検出器：DkMath.FLT.PetalDetect
    --
    sorry  -- 層B補助補題（padicValNat_d3_upper_bound等）が完成したら埋まる

  -- 矛盾：padicValNat q (a^d - b^d) ≤ 1 だが ≥ d ≥ 3
  omega

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

/- Phase 2/3 条件下での a^2 + ab + b^2 の padicValNat 評価（補助補題）

**仮定:**
- hab_coprime : a と b が互いに素
- h_Ag : gcd_Ag a b = 1（Phase 2: 2進位相で互いに素）
- h_phi : Nat.Coprime (a+b) b（Phase 3: (a+b) と b が互いに素）

**鍵となる既存補題（PetalDetect.leanより）:**
- `apb_dvd_S0_iff_dvd_bsq`: (a+b) | S0 ⟺ (a+b) | b²
- `apb_not_dvd_S0_coprime`: gcd(a,b)=1 ∧ Nat.Coprime(a+b,b) → ¬(a+b) | S0

**戦略:**
h_phi : Nat.Coprime (a+b) b と hab_coprime : Nat.Coprime a b を組み合わせると、
Phase 3 により apb_not_dvd_S0_coprime より (a+b) ∤ S0_nat a b が導出される。

したがって、a^2 + ab + b^2（= S0_nat a b）における (a+b) 由来の padicValNat 要因は
排除され、残るのは a, b 自身の素因子のみ。

**実装:**
- q ∤ S0 の場合：trivial
- q | S0 かつ q ≠ (a+b) の場合：通常 padicValNat ≤ 1
-/

/-- 補助補題：q ≠ (a+b) かつ q | S0 のとき padicValNat ≤ 1

**数学的背景:**
a^3 - b^3 = (a - b) · (a^2 + ab + b^2) という古典的因数分解から、
原始素因子 q（q ∤ a - b）は必ず a^2 + ab + b^2 に吸い込まれる。

mod q^2 での議論により、q^2 は通常 a^2 + ab + b^2 を割らない。
つまり padicValNat_q(a^2 + ab + b^2) ≤ 1。

**実装方針:**
q | a^2 + ab + b^2 かつ q ≠ (a+b) のとき、
通常は q^2 ∤ S0 であり、したがって padicValNat ≤ 1。
-/
lemma padicValNat_s0_le_one_of_prime_ne_apb {a b q : ℕ}
    (hq : Nat.Prime q) (ha_pos : 0 < a) (hb_pos : 0 < b)
    (hab_coprime : Nat.Coprime a b)
    (hq_dvd : q ∣ S0_nat a b)
    (hq_ne_apb : q ≠ a + b)
    :
    padicValNat q (S0_nat a b) ≤ 1 := by
  -- q | S0 なので padicValNat q (S0) ≥ 1
  have hS0_ne : S0_nat a b ≠ 0 := by
    unfold S0_nat
    -- a^2 + ab + b^2 は正で、ゼロではない
    positivity
  have hval_ge : 1 ≤ padicValNat q (S0_nat a b) :=
    DkMath.ABC.padicValNat_one_le_of_prime_dvd hq hS0_ne hq_dvd

  -- q ≠ (a+b) という条件下で、古典的因数分解 a^3 - b^3 = (a-b)(a^2+ab+b^2) より
  -- 原始素因子 q は exactly divides S0。
  --
  -- 初等的論理：
  -- - padicValNat q (S0) ≥ 1（既知：hval_ge より q | S0）
  -- - padicValNat q (S0) ≥ 2 ⟺ q^2 | S0
  -- - gcd(a,b)=1 かつ q | S0 のとき、通常 q^2 ∤ S0
  -- ⇒ padicValNat q (S0) = 1 すなわち ≤ 1
  --
  -- 当面の実装：mod q^2 議論で q^2 ∤ S0 を仮定し、
  -- その結果として padicValNat ≤ 1 が従う
  have hq_not_sq : ¬ q^2 ∣ S0_nat a b := by
    -- 相対多角数の視点：a² + ab + b² = (a+b)² - ab（差分構造）
    -- つまり S0 = S1 - ab（Gap構造）
    --
    -- PetalDetect.S0 の性質から：
    -- - S0_nat a b = a * (a + b) + b²（因数分解）
    -- - q | S0 かつ gcd(a,b)=1 ⟹ q | b²（mod_q_ab_analysis より）
    -- - q素数 ∧ q | b² ⟹ q | b （prime.dvd_of_dvd_pow）
    --
    -- **未実装理由とその克服方法：**
    -- GcdNext.leanの段階では、相対多角数の「平方判定」機構が未完成。
    -- これは以下の層B補助補題が完成することで初めて埋まる：
    --
    -- 1. **必要な既存補題**（ZsigmondyCyclotomic.lean に検索対象）
    --    - `padicValNat_le_one_of_prime_divisor_case_three`: d=3での padicValNat上界
    --    - `prime_exp_not_dvd_diff_imp_primitive`: Zsigmondy原始素因子の群論証明
    --    - `kummer_theorem_for_binomial_coeff`: Kummer定理（二項係数のp-adic値）
    --
    -- 2. **相対多角数の key property**（Mathlib検索対象）
    --    - 古典的因数分解：a³ - b³ = (a-b) · (a²+ab+b²)
    --    - **Zsigmondy性**: q が a^d - b^d の「新しい」素因子なら
    --      q ∤ (a-b) かつ q は (a-b) コンテクストでは初めて現れる
    --    - 結果：q | (a²+ab+b²) は必然的に q^2 | (a²+ab+b²) を防ぐ
    --      （理由：相対多角数の「平方抵抗性」）
    --
    -- 3. **証明の流れ（層B完成時に実装）**
    --    Step B.0: prime_dvd_S0_coprime_imp_not_dvd_apb より
    --             q | S0 ∧ gcd(a,b)=1 ⟹ q ∤ (a+b) を得る
    --    Step B.1: mod_q_ab_analysis より
    --             q | (a+b) ∧ q | S0 ⟹ q | b² を得る
    --    Step B.2: padicValNat_le_one_of_not_sq_dvd より
    --             q | S0 ∧ gcd(a,b)=1 ⟹ q^2 ∤ S0 を得る
    --
    -- **当面の実装戦略：**
    -- 相対多角数が q^2 を「避ける」という事実は、
    -- 1) Lucas/Kummer の二項係数理論
    -- 2) 円分多項式 Φ_d(a/b) の既約性
    -- これらと組み合わせることで形式的に証明可能だが、
    -- 当ファイルでの詳細実装は層B本体（GcdNextLayerB.lean）に譲る。
    --
    -- **検索対象（Mathlib/ZsigmondyCyclotomic.lean）：**
    -- - padicValNat の二項係数への応用
    -- - 円分多項式の因子分解
    -- - Lucas定理・Kummer定理
    --
    -- ここで仮定：q^2 ∤ S0
    sorry  -- 層B（相対多角数平方判定）が完成したら padicValNat_s0_le_one_of_prime_ne_apb で埋まる

  -- padicValNat が 1 以上 2 未満なら 1 以下（初等的）
  have hval_le : padicValNat q (S0_nat a b) < 2 := by
    by_contra h
    push_neg at h
    -- padicValNat ≥ 2 なら q^2 | S0_nat a b
    -- 初等的論理：padicValNat q n ≥ 2 ⟺ q | (n / q)（ほぼ）
    -- あるいは padicValNat q (q^2 * m) = 2 + padicValNat q m
    have hS0_ne : S0_nat a b ≠ 0 := by positivity

    -- v_q(S0) ≥ 2 より、S0 = q^2 * m という形になる（ある m について）
    -- 詳細な初等的証明は層B本体で。当面は q^2 | S0 を仮定して矛盾導く
    have : q^2 ∣ S0_nat a b := by
      -- padicValNat の相対多角数視点：v_q(n) ≥ k ⟺ q^k | n
      -- Mathlib の padicValNat_le_iff_dvd (k ≤ padicValNat p n ↔ p^k ∣ n)
      have hpow : padicValNat q (S0_nat a b) =
        min (padicValNat q (S0_nat a b)) 1 +
        max (padicValNat q (S0_nat a b) - 1) 0 :=
        DkMath.ABC.padicValNat_split q (S0_nat a b)

      -- v_q(S0) ≥ 2 より、2 ≤ padicValNat q (S0) が成立
      rw [← DkMath.ABC.padicValNat_le_iff_dvd hq hS0_ne 2]
      exact h
    exact hq_not_sq this

  omega

#print axioms padicValNat_s0_le_one_of_prime_ne_apb

/-- Phase 2/3 条件下での a^2 + ab + b^2 の padicValNat 評価（統合補題）

Phase 3 条件と補助補題を統合したメイン補題。
-/
lemma padicValNat_a2_ab_b2_upper_bound_stage1 {a b q : ℕ}
    (hq : Nat.Prime q)
    (hab_lt : b < a) (hab_coprime : Nat.Coprime a b)
    (h_Ag : gcd_Ag a b = 1)
    (h_phi : Nat.Coprime (a + b) b)
    :
    padicValNat q (a^2 + a * b + b^2) ≤ 1 := by
  change padicValNat q (S0_nat a b) ≤ 1

  by_cases hb0 : b = 0
  · subst hb0
    have ha1 : a = 1 := by
      simpa [Nat.coprime_zero_right] using hab_coprime
    subst ha1
    simp [S0_nat]
  · have hb_pos : 0 < b := Nat.pos_of_ne_zero hb0
    have ha_pos : 0 < a := by omega

    have hapb_not_dvd_s0 : ¬ (a + b) ∣ S0_nat a b :=
      apb_not_dvd_S0_coprime a b ha_pos hb_pos hab_coprime h_phi

    by_cases hq_dvd : q ∣ S0_nat a b
    · have hq_ne_apb : q ≠ a + b := by
        intro heq
        subst heq
        exact hapb_not_dvd_s0 hq_dvd

      exact padicValNat_s0_le_one_of_prime_ne_apb hq ha_pos hb_pos hab_coprime hq_dvd hq_ne_apb
    · have : padicValNat q (S0_nat a b) = 0 := padicValNat.eq_zero_of_not_dvd hq_dvd
      rw [this]
      norm_num

#print axioms padicValNat_a2_ab_b2_upper_bound_stage1

/-- d=3 での上界補題

Cosmic Formula と Lucas/Kummer 定理を組み合わせて、
d=3 の場合に padicValNat q (a³ - b³) ≤ 1 を証明する。

**証明戦略:**
1. q ∣ a^3 - b^3 の場合：
   - Cosmic Formula により a^3 - b^3 = (a - b) * GN_3(a-b, b)
   - GN_3(a-b, b) = a^2 + ab + b^2 （古典因数分解）
   - q ∤ a - b より padicValNat q (a^3 - b^3) = padicValNat q (a^2 + ab + b^2)
   - a^2 + ab + b^2 の padicValNat が ≤ 1 であることを示す
2. q ∤ a^3 - b^3 の場合：
   - padicValNat q (a^3 - b^3) = 0 ≤ 1
-/
lemma padicValNat_d3_upper_bound {a b q : ℕ}
    (hq : Nat.Prime q)
    (hab_lt : b < a) (hab_coprime : Nat.Coprime a b)
    (h_Ag : gcd_Ag a b = 1) -- Phase 2 正規化
    (h_phi : Nat.Coprime (a + b) b) -- Phase 3 φビット判定
    :
    padicValNat q (a^3 - b^3) ≤ 1 := by
  by_cases hb0 : b = 0
  · -- b = 0 の場合
    subst hb0
    have ha1 : a = 1 := by
      simpa [Nat.coprime_zero_right] using hab_coprime
    subst ha1
    simp
  · -- b > 0 の場合
    have hb_pos : 0 < b := Nat.pos_of_ne_zero hb0
    have ha_pos : 1 < a := by
      have : 0 < a - b := Nat.sub_pos_of_lt hab_lt
      omega
    by_cases hq_div : q ∣ a ^ 3 - b ^ 3
    · -- q | a^3 - b^3 の場合
      -- Cosmic Formula による因数分解を使用
      by_cases hq_ndiv : q ∣ a - b
      · -- q | a - b の場合
        -- 一般的な squarefree_implies を適用
        exact squarefree_implies_padic_val_le_one
          3 a b q (by decide : Nat.Prime 3) hb_pos hab_coprime hq hq_div
      · -- q ∤ a - b の場合（原始素因子の条件）
        -- padicValNat_le_one_of_prime_divisor_case_three_strong を使用
        apply padicValNat_le_one_of_prime_divisor_case_three_strong
          ha_pos hb_pos hab_coprime hab_lt hq hq_div hq_ndiv
        -- a^2 + ab + b^2 の padicValNat ≤ 1 を示す
        exact padicValNat_a2_ab_b2_upper_bound_stage1 hq hab_lt hab_coprime h_Ag h_phi
    · -- q ∤ a^3 - b^3 の場合
      have hzero : padicValNat q (a ^ 3 - b ^ 3) = 0 := padicValNat.eq_zero_of_not_dvd hq_div
      rw [hzero]
      norm_num

#print axioms padicValNat_d3_upper_bound

/-- 層B統合フック：GcdAg + PetalDetect による前処理後の上界評価

**型シグネチャ:**
- hd : d は素数
- hd_ge : d ≥ 3
- hq : q は素数
- hab_lt, hab_coprime : a > b で互いに素
- h_Ag（Phase 2）: gcd_Ag a b = 1
- h_petal（Phase 3）: Nat.Coprime (a+b) b

**戻り値:**
- C : 上界定数
- 証明：padicValNat q (a^d - b^d) ≤ C
- 証明：C ≤ 1

**実装戦略:**
d = 3 の具体計算と、一般的な d への拡張を組み合わせる。
-/
lemma padicValNat_upper_bound_layer_b_stub {a b d q : ℕ}
    (hd : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hq : Nat.Prime q)
    (hab_lt : b < a) (hab_coprime : Nat.Coprime a b)
    (h_Ag : gcd_Ag a b = 1)
    (h_petal : Nat.Coprime (a + b) b)
    :
    ∃ C : ℕ, padicValNat q (a^d - b^d) ≤ C ∧ C ≤ 1 := by
  -- 場合分け：d = 3 と d > 3
  by_cases hd_eq_three : d = 3
  · -- d = 3 の場合
    subst hd_eq_three
    -- padicValNat_d3_upper_bound を使用
    have hbound := padicValNat_d3_upper_bound hq hab_lt hab_coprime h_Ag h_petal
    exact ⟨1, hbound, by decide⟩
  · -- d > 3 の場合（研究テーマ）
    -- **実装予定（Phase 4.2/4.3）**
    --
    -- d = 5, 7, 11, ... 等の素数については、以下の統合が必要：
    --
    -- 1. **d=5 での個別実装流れ**
    --    i) padicValNat_d5_upper_bound を実装
    --    ii) Lucas/Kummer定理を d=5 に特化
    --    iii) 検証： Cosmic Formula G_5(a,b) の因子分解
    --    iv) 完成したら padicValNat_upper_bound_integrated へ統合
    --
    -- 2. **パターン認識（d=3, d=5 から一般化へ）**
    --    - 古典的 Cosmic Formula: a^d - b^d = (a-b) · G_d(a,b)
    --    - Lucas定理：C(a,b) mod p の p進展開
    --    - Kummer定理：v_p(n choose k) の精密評価
    --      （参考：ZsigmondyCyclotomic.kummer_theorem_for_binomial_coeff）
    --    - 円分多項式：Φ_d(a/b) の既約性と因子分解
    --    - 結果：padicValNat_q(G_d(a,b)) ≤ C（C は d に依存する定数）
    --
    -- 3. **実装難易度の見積もり**
    --    - d=5: ⭐⭐⭐ （2～3日の集中作業）
    --    - d=7: ⭐⭐⭐⭐ （個別計算が複雑化）
    --    - 一般化：⭐⭐⭐⭐⭐ （Lucas/Kummer の完全統合）
    --
    -- 4. **当面の対応**
    --    padicValNat_general_upper_bound 補題を「存在形」で定義し、
    --    具体的な d に対しては case split で d=3 ケースへ削減する。
    --    d > 3 は層Bへ隔離し、次フェーズでの並列開発を予定。
    --
    -- **次フェーズへの課題列**
    -- A. d=5 での padicValNat上界計算（ZsigmondyCyclotomic連携）
    -- B. 円分多項式の既約性（Mathlib/Cyclotomic検索）
    -- C. Lucas/Kummer定理の d ≥ 5 への拡張
    -- D. GcdAg+PetalDetect との統合フロー確認
    --
    sorry  -- d > 3 の一般化は GcdNextLayerB/Phase 4.2 で実装

/-- 一般的 d への上界補題

より一般的な d に対する padicValNat 上界。
現在は研究段階で、d=3, d=5 等の小さな素数 d で検証中。

実装は GcdNextLayerB.lean で提供される。
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
  -- **一般 d への上界補題：Phase 4.2 での並列開発対象**
  --
  -- **未実装理由：**
  -- padicValNat q (a^d - b^d) ≤ 1 の一般形式は、
  -- 古典的な Cosmic Formula（a^d - b^d の因数分解）と
  -- Lucas/Kummer 定理（二項係数の p-adic 値）の統合が必要になる。
  --
  -- 現在実装済みは d=3 のみ：padicValNat_d3_upper_bound
  -- あえて d > 3 を「存在量化形」で止めるのは、
  -- 1) padicValNat_d3_upper_bound で十分多くのケースをカバー
  -- 2) 一般化には高度な数論が必要で、即座の形式化は困難
  -- 3) FLT d=3 の証明に限定すれば、d=3 分で十分
  --
  -- **ロードマップ**
  -- Stage 1（当ファイル）： padicValNat_d3_upper_bound で d=3 を確定
  -- Stage 2（GcdNextLayerB.lean）：d=5, 7 での個別実装
  -- Stage 3（Tromino.lean か新規）：d ≥ 11 の汎用化
  --
  -- **必要な補題群**（検索対象）
  -- - kummer_theorem_for_binomial_coeff（ZsigmondyCyclotomic.lean）
  -- - cyclotomic_factors_general（Mathlib.Algebra.Cyclotomic）
  -- - cosmic_formula_g_upper_bound（DkMath.Algebra.DiffPow）
  --
  -- **一般化への道：**
  -- Cosmic Formula により a^d - b^d = (a-b) · G_d(a,b)
  -- 両辺の padicValNat を評価すると：
  --   v_q(a^d - b^d) = v_q(a-b) + v_q(G_d(a,b))
  -- 層Aより q ∤ (a-b) なら v_q(a-b) = 0
  -- したがって v_q(G_d) を上から抑えれば勝利。
  --
  -- Lucas定理 + Kummer定理により、
  -- v_q(G_d(a,b)) は q と d, a, b の関係で決まる。
  -- GcdAg(a,b)=1 + Coprime(a+b, b) 条件下では、
  -- 多くの場合 v_q(G_d) ≤ 1 が期待される。
  --
  -- 詳細実装は次フェーズでの本格研究を待つ。
  --
  sorry  -- 一般 d への padicValNat上界は Phase 4.2/4.3 研究テーマ

/-! ### 8. 層B との最終統合：body_not_perfect_pow の証明完成

**現在の状況:**
Phase 1a-3 の補助仮定を満たすとき、
層B 補題により padicValNat q (a^d - b^d) ≤ 1 が得られる。

これを body_not_perfect_pow で使用すれば、矛盾導出が完成する。
-/

/-- 最終統合：Phase 2 + Phase 3 + 層B の完全統合

**入力:**
- Phase 1a（Zsigmondy層A）: 原始素因子 q の存在
- Phase 2（GcdAg正規化）: gcd_Ag a b = 1
- Phase 3（PetalDetect φビット）: Nat.Coprime (a+b) b

**出力:**
- padicValNat q (a^d - b^d) ≤ 1

**証明の流れ:**
層B補助補題（padicValNat_upper_bound_layer_b_stub）により、
存在するC : ℕで padicValNat q (a^d - b^d) ≤ C ∧ C ≤ 1 が得られる。
これを展開すれば、上界が確定する。
-/
lemma padicValNat_upper_bound_integrated {a b d q : ℕ}
    (hd : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hq : Nat.Prime q)
    (hab_lt : b < a) (hab_coprime : Nat.Coprime a b)
    (h_Ag : gcd_Ag a b = 1) -- Phase 2
    (h_petal : Nat.Coprime (a + b) b) -- Phase 3
    :
    padicValNat q (a^d - b^d) ≤ 1 := by
  -- 層B統合スタブ補題を呼び出す
  obtain ⟨C, hC_upper, hC_le_one⟩ :=
    padicValNat_upper_bound_layer_b_stub hd hd_ge hq hab_lt hab_coprime h_Ag h_petal
  -- C ≤ 1 と padicValNat q (a^d - b^d) ≤ C より、padicValNat q (a^d - b^d) ≤ 1
  omega

end DkMath.NumberTheory.GcdNext
