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
  - 再利用される基礎補題群を提供
  - 研究中の一般 d 統合 (`body_not_perfect_pow` など) は `GcdNextResearch` へ移動
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


/-! ### 6. Research Notes Moved -/

/-
研究中の一般 d 向け統合ブロック（`body_not_perfect_pow`、層Bスタブ等）は
`DkMath.NumberTheory.GcdNextResearch` に移動。
本ファイルは、他モジュールで再利用される基礎補題群のみを保持する。
-/
end DkMath.NumberTheory.GcdNext
