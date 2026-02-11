/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- import Mathlib
import DkMath.ABC.PadicValNat
-- import Mathlib.NumberTheory.Padics.PadicVal.Defs
import DkMath.Algebra.DiffPow
import DkMath.NumberTheory.GcdDiffPow
import DkMath.NumberTheory.GdcDivD

set_option linter.style.emptyLine false

namespace DkMath.NumberTheory.GcdNext

open scoped BigOperators
open Finset
open DkMath.ABC
open DkMath.Algebra.DiffPow
open DkMath.NumberTheory.GcdDiffPow

-- ========================================
-- § 1. 原始素因子の存在条件に関する補助補題
-- ========================================

/-- d ∤ a - b の条件：合同式の否定による特徴づけ

**数学的意味:**
a ≢ b (mod d) ⇔ d ∤ a - b

**この補題の利用場面:**
Zsigmondy の原始素因子定理で「原始性」を保証するには、
指数 d が差 a - b を割らないことが必要。
合同式の否定として条件を記述できれば、
具体的な数値例での検証が容易になる。

**TODO:** Mathlib の適切な API を使って証明を完成させる
-/
lemma not_dvd_diff_iff_not_modEq {a b d : ℕ} (hd : 0 < d) (hab : b ≤ a) :
    ¬ d ∣ a - b ↔ ¬ (a ≡ b [MOD d]) := by
  constructor
  · intro h_not_dvd h_mod
    -- a ≡ b (mod d) の定義は a % d = b % d
    -- これから d ∣ a - b を導く
    sorry -- TODO: Mathlib の適切な補題を使う
  · intro h_not_mod h_dvd
    -- d ∣ a - b から a ≡ b (mod d) を導く
    sorry -- TODO: Mathlib の適切な補題を使う

-- ========================================
-- § 2. Zsigmondy の原始素因子定理（層A：存在層）
-- ========================================

/-- Zsigmondy の原始素因子定理（層A：存在層、基本版）

**数学的内容:**
Zsigmondy の定理（1892）：
a > b ≥ 1, gcd(a,b) = 1, d が素数で d ≥ 3 のとき、
d ∤ a - b ならば、a^d - b^d は「原始素因子」を持つ：
原始素因子 q とは：q ∣ a^d - b^d かつ q ∤ a - b を満たす素数。

**この補題の位置づけ:**
- 層A（存在層）：原始素因子の**存在**だけを保証（padicValNat の精密評価なし）
- 素数指数に限定した軽量版
- ¬ d ∣ a - b を明示的に仮定として要求

**将来の拡張:**
- 層B（精密層）：padicValNat q (a^d - b^d) = 1 の評価（LTE 使用）
- 一般の指数 d への拡張（円分多項式経由）
-/
lemma exists_primitive_prime_factor_basic {a b d : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hpnd : ¬ d ∣ a - b) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ a^d - b^d ∧ ¬ q ∣ a - b := by
  -- GcdDiffPow の補題を直接使う
  exact exists_prime_divisor_not_dividing_diff_of_prime_exp hd_prime hd_ge hab_lt hb hab hpnd

-- ========================================
-- § 3. 原始素因子の p-adic 付値に関する補題
-- ========================================

/-- 原始素因子の p-adic 付値の下界

**数学的内容:**
q が a^d - b^d の原始素因子（q | a^d - b^d）ならば、
padicValNat q (a^d - b^d) ≥ 1

**これは明らか:**
q | a^d - b^d かつ a^d - b^d ≠ 0 から、既存の補題で直ちに従う。

**次のステップ:**
上界 padicValNat q (a^d - b^d) ≤ 1 を示すには、
円分多項式の理論や LTE の精密版が必要。
-/
lemma padicValNat_primitive_prime_factor_ge_one {a b d q : ℕ}
    (hab_lt : b < a) (hb : 0 < b) (hd : 1 < d)
    (hq_prime : Nat.Prime q) (hq_div : q ∣ a^d - b^d) :
    1 ≤ padicValNat q (a^d - b^d) := by
  -- a^d - b^d ≠ 0 を示す
  have hd_pos : 0 < d := Nat.zero_lt_of_lt hd
  have hd_ne : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd_pos
  have hab_pow : b^d < a^d := Nat.pow_lt_pow_left hab_lt hd_ne
  have hne : a^d - b^d ≠ 0 := Nat.sub_ne_zero_of_lt hab_pow
  -- padicValNat_one_le_of_prime_dvd を適用
  exact padicValNat_one_le_of_prime_dvd hq_prime hne hq_div

/-- 原始素因子の p-adic 付値の上界（TODO）

**数学的内容:**
q が a^d - b^d の原始素因子で、追加の条件（例：円分多項式が square-free）
を満たすなら、padicValNat q (a^d - b^d) ≤ 1

**証明の方針:**
- 円分多項式 Φ_d(X) が a^d - b^d を割る（Mathlib にある）
- 原始素因子 q は Φ_d(a/b) の素因子
- Φ_d が square-free なら、q の指数は 1

**必要な理論:**
- Mathlib.RingTheory.Polynomial.Cyclotomic.Basic の活用
- 円分多項式の既約性または square-free 性
- 有理数体上での評価と整数論への翻訳

**現状:** これは深い定理で、別 PR で段階的に実装予定
-/
lemma padicValNat_primitive_prime_factor_le_one {a b d q : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hpnd : ¬ d ∣ a - b)
    (hq_prime : Nat.Prime q)
    (hq_div : q ∣ a ^ d - b ^ d) (hq_ndiv : ¬ q ∣ a - b) :
    padicValNat q (a ^ d - b ^ d) ≤ 1 := by
  -- TODO: 円分多項式の理論を使った証明
  sorry

-- ========================================
-- § 4. Zsigmondy の原始素因子定理（層B：精密層、TODO）
-- ========================================

/-- Zsigmondy の原始素因子定理のフック

**TODO（別 PR で実装予定）:**
Mathlib v4.26.0 には Zsigmondy の原始素因子定理の完全な形式化がまだ存在しない。
将来的には円分多項式（Cyclotomic polynomial）経由で次のように実装する：
- `Cyclotomic.dvd_pow_sub_pow`: Φ_d(a/b) ∣ a^d - b^d
- 円分多項式の既約性と素因子の存在

**代替実装案：**
- 選択肢A: d = 3, 5 など小さいケースだけ初等的に証明
- 選択肢B: Cyclotomic 理論を段階的に構築（重工事）
- 選択肢C: 既存の Mathlib.NumberTheory.Cyclotomic.* を活用

**数学的内容:**
Zsigmondy の定理（1892）：
a > b ≥ 1, gcd(a,b) = 1, d > 1 のとき、
次の例外を除いて、a^d - b^d は「原始素因子」（primitive prime divisor）を持つ：
- 例外1: a - b = 1 かつ d = 2
- 例外2: a = 2, b = 1, d = 6
原始素因子 q とは：q ∣ a^d - b^d かつ q ∤ a^k - b^k （∀k < d）を満たす素数。

現在は軽量版（prime d ≥ 3）を優先実装。完全版は別 PR で。

**強化版**: 原始素因子 q について padicValNat q (a^d - b^d) = 1 を保証し、
完全冪判定に必要な付值情報を供給する。
-/
lemma exists_primitive_prime_factor_hook {a b : ℕ} {d : ℕ}
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b) (hd : 2 < d) :
    ∃ q : ℕ, Nat.Prime q ∧ q ∣ a^d - b^d ∧ ¬ q ∣ a - b ∧ padicValNat q (a^d - b^d) = 1 := by
  -- まずは d が素数の場合に限定（軽量版）
  by_cases hd_prime : Nat.Prime d
  · -- d が素数の場合
    have hp_ge : 3 ≤ d := by omega
    -- ¬ d ∣ a - b を仮定
    have hpnd : ¬ d ∣ a - b := by
      sorry  -- TODO: d が素数で d ≥ 3 の場合、一般には証明が必要

    -- 層A から原始素因子 q を得る
    obtain ⟨q, hq_prime, hq_div, hq_ndiv⟩ :=
      exists_primitive_prime_factor_basic hd_prime hp_ge hab_lt hb hab hpnd

    -- padicValNat q (a^d - b^d) = 1 を示す（下界と上界を組み合わせる）
    have hvad : padicValNat q (a ^ d - b ^ d) = 1 := by
      -- 下界：1 ≤ padicValNat q (a^d - b^d)
      have h1 : 2 < d := hd
      have hd_ge_one : 1 < d := by omega
      have hge : 1 ≤ padicValNat q (a ^ d - b ^ d) :=
        padicValNat_primitive_prime_factor_ge_one hab_lt hb hd_ge_one hq_prime hq_div

      -- 上界：padicValNat q (a^d - b^d) ≤ 1
      have hle : padicValNat q (a ^ d - b ^ d) ≤ 1 :=
        padicValNat_primitive_prime_factor_le_one
          hd_prime hp_ge hab_lt hb hab hpnd hq_prime hq_div hq_ndiv
      -- 結論：1 ≤ x ∧ x ≤ 1 ⇒ x = 1
      omega

    exact ⟨q, hq_prime, hq_div, hq_ndiv, hvad⟩
  · -- d が合成数の場合は TODO（別 PR）
    sorry

-- ========================================
-- § 5. 開発ロードマップ
-- ========================================

/- **Zsigmondy 理論の段階的な実装方針**

## ✅ Phase 1: 層A（存在層）— 完了

基本補題 `exists_primitive_prime_factor_basic` により、
素数指数の場合の原始素因子の存在が保証された。

**成果:**
- 素数指数 d ≥ 3 の場合に原始素因子 q が存在する
- 条件: gcd(a,b) = 1, d ∤ a - b
- GcdDiffPow の既存補題を活用して実装

## ⏳ Phase 2: 層B（精密層）— 部分的に完了

原始素因子の p-adic 付値を精密に評価する。

**現在の成果:**
- ✅ 下界: `padicValNat_primitive_prime_factor_ge_one`
  - 1 ≤ padicValNat q (a^d - b^d) を証明（既存の補題から直接）

**残りの課題:**
- ⏳ 上界: `padicValNat_primitive_prime_factor_le_one` (TODO)
  - padicValNat q (a^d - b^d) ≤ 1 を証明
  - 必要な理論: 円分多項式の square-free 性

**理論的背景:**
円分多項式 Φ_d(X) は整数係数の既約多項式で、以下の性質を持つ：
- Φ_d(X) | X^d - 1（より一般に Φ_d(a/b) | a^d - b^d）
- 原始素因子 q は Φ_d(a/b) の素因子として現れる
- 多くの場合、Φ_d は "square-free"（重複度1で因数分解）
  → これが padicValNat q (a^d - b^d) = 1 の鍵

**実装戦略:**
1. Mathlib.RingTheory.Polynomial.Cyclotomic.* を import
2. Φ_d の評価と整数環での性質を整理
3. 有理数体上の理論を整数論に翻訳
4. square-free 性または既約性から上界を導出

## ⏳ Phase 3: 一般化 — TODO

任意の指数 d への拡張。

**必要な理論:**
- Cyclotomic polynomial Φ_d の性質
- Φ_d(a/b) ∣ a^d - b^d の証明
- 円分多項式の既約性と素因子の存在

**課題:**
- 合成数の指数の場合、素因子の分布がより複雑
- 例外ケースの扱い (d = 2, 6)

## ⏳ Phase 4: Mathlib への貢献 — TODO

完全な実装を Mathlib にフィードバック。

**貢献内容:**
- Zsigmondy の定理の完全な形式化
- Cyclotomic 理論との統合
- 完全冪判定などの応用例

-/

end DkMath.NumberTheory.GcdNext
