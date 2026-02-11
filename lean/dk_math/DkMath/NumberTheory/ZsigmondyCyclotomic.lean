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
-- § 3. Zsigmondy の原始素因子定理（層B：精密層、TODO）
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

    -- exists_prime_divisor_not_dividing_diff_of_prime_exp から q を得る
    obtain ⟨q, hq_prime, hq_div, hq_ndiv⟩ :=
      exists_prime_divisor_not_dividing_diff_of_prime_exp hd_prime hp_ge hab_lt hb hab hpnd

    -- padicValNat q (a^d - b^d) = 1 を示す（LTE が必要）
    have hvad : padicValNat q (a^d - b^d) = 1 := by
      sorry  -- TODO: Lifting the Exponent Lemma を使った精密評価が必要

    exact ⟨q, hq_prime, hq_div, hq_ndiv, hvad⟩
  · -- d が合成数の場合は TODO（別 PR）
    sorry

-- ========================================
-- § 4. 開発ロードマップ
-- ========================================

/- **Zsigmondy 理論の段階的な実装方針**

## ✅ Phase 1: 層A（存在層）— 完了

基本補題 `exists_primitive_prime_factor_basic` により、
素数指数の場合の原始素因子の存在が保証された。

**成果:**
- 素数指数 d ≥ 3 の場合に原始素因子 q が存在する
- 条件: gcd(a,b) = 1, d ∤ a - b
- GcdDiffPow の既存補題を活用して実装

## ⏳ Phase 2: 層B（精密層）— TODO

原始素因子の p-adic 付値を精密に評価する。

**必要な理論:**
- Lifting the Exponent Lemma (LTE)
- または Cyclotomic polynomial の性質

**目標:**
- padicValNat q (a^d - b^d) = 1 を証明
- 完全冪判定への応用を可能にする

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
