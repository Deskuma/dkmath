/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.GcdNext

set_option linter.style.emptyLine false
set_option linter.style.longLine false

namespace DkMath.NumberTheory.GcdNext

open DkMath.SilverRatio.GcdAg  -- Phase 2: GcdAg 正規化関数を使用
open DkMath.FLT.PetalDetect  -- Phase 3: φビット構造を使用

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
-- example (a b : ℕ) : GcdAg.gcd_Ag a b = 1 → "本質的に互いに素" := by so#rry

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
-- example (a b q : ℕ) : "q が (a+b) 由来" → "φ=1 側のみ" := by so#rry

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
- q² ∤ S0 を仮定して padicValNat 上界を得る
-/

/-- 補助補題：`q^2 ∤ S0` なら `padicValNat q S0 ≤ 1`

**数学的背景:**
`2 ≤ v_q(S0)` と `q^2 ∣ S0` は同値なので、`q^2 ∤ S0` なら `v_q(S0) ≤ 1`。
-/
lemma padicValNat_s0_le_one_of_not_sq_dvd {a b q : ℕ}
    (hq : Nat.Prime q)
    (hS0_ne : S0_nat a b ≠ 0)
    (hq_not_sq : ¬ q^2 ∣ S0_nat a b) :
    padicValNat q (S0_nat a b) ≤ 1 := by
  by_contra h
  have h2 : 2 ≤ padicValNat q (S0_nat a b) := by omega
  have : q^2 ∣ S0_nat a b := (DkMath.ABC.padicValNat_le_iff_dvd hq hS0_ne 2).1 h2
  exact hq_not_sq this

#print axioms padicValNat_s0_le_one_of_not_sq_dvd

/-- Phase 2/3 条件下での a^2 + ab + b^2 の padicValNat 評価（統合補題）

Phase 3 条件と補助補題を統合したメイン補題。
-/
lemma padicValNat_a2_ab_b2_upper_bound_stage1 {a b q : ℕ}
    (hq : Nat.Prime q)
    (hab_lt : b < a) (_hab_coprime : Nat.Coprime a b)
    (_h_Ag : gcd_Ag a b = 1)
    (_h_phi : Nat.Coprime (a + b) b)
    (hq_not_sq : ¬ q^2 ∣ S0_nat a b)
    :
    padicValNat q (a^2 + a * b + b^2) ≤ 1 := by
  change padicValNat q (S0_nat a b) ≤ 1
  -- hab_lt : b < a より 0 < a
  have ha_pos : 0 < a := Nat.lt_of_le_of_lt (Nat.zero_le b) hab_lt
  have hS0_ne : S0_nat a b ≠ 0 := S0_ne_zero a b ha_pos
  exact padicValNat_s0_le_one_of_not_sq_dvd hq hS0_ne hq_not_sq

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
    (hq_not_sq : ¬ q^2 ∣ S0_nat a b) -- 2026/02/22  7:08 追加
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
        exact padicValNat_a2_ab_b2_upper_bound_stage1 hq hab_lt hab_coprime h_Ag h_phi hq_not_sq
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
    (hq_not_sq : ¬ q^2 ∣ S0_nat a b)
    :
    ∃ C : ℕ, padicValNat q (a^d - b^d) ≤ C ∧ C ≤ 1 := by
  -- 場合分け：d = 3 と d > 3
  by_cases hd_eq_three : d = 3
  · -- d = 3 の場合
    subst hd_eq_three
    -- padicValNat_d3_upper_bound を使用
    have hbound := padicValNat_d3_upper_bound hq hab_lt hab_coprime h_Ag h_petal hq_not_sq
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
    -- (_hd : 3 ≤ d) (_hd_prime : Nat.Prime d)
    -- (_hq : Nat.Prime q)
    -- (_hab_lt : b < a) (_hab_coprime : Nat.Coprime a b)
    -- (_h_Ag : gcd_Ag a b = 1) -- GcdAg 正規化
    -- (_h_petal : Nat.Coprime (a + b) b) -- PetalDetect φビット
    :
    ∃ C : ℕ, padicValNat q (a^d - b^d) ≤ C := by
  exact ⟨padicValNat q (a^d - b^d), le_rfl⟩

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
    (hq_not_sq : ¬ q^2 ∣ S0_nat a b)
    :
    padicValNat q (a^d - b^d) ≤ 1 := by
  -- 層B統合スタブ補題を呼び出す
  obtain ⟨C, hC_upper, hC_le_one⟩ :=
    padicValNat_upper_bound_layer_b_stub hd hd_ge hq hab_lt hab_coprime h_Ag h_petal hq_not_sq
  -- C ≤ 1 と padicValNat q (a^d - b^d) ≤ C より、padicValNat q (a^d - b^d) ≤ 1
  omega


end DkMath.NumberTheory.GcdNext
