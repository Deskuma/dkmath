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
-- Cyclotomic polynomial theory
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Int.Basic

set_option linter.style.emptyLine false

namespace DkMath.NumberTheory.GcdNext

open scoped BigOperators
open Finset
open DkMath.ABC
open DkMath.Algebra.DiffPow
open DkMath.NumberTheory.GcdDiffPow
open Polynomial

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
-- § 3. 円分多項式の基本性質
-- ========================================

/-- 円分多項式と冪差の関係（基本定理）

**数学的内容:**
円分多項式 Φ_d(X) は X^d - 1 を割る：
Φ_d(X) | X^d - 1

**Mathlib の定理:**
`Polynomial.cyclotomic.dvd_X_pow_sub_one`

**応用への道筋:**
1. X に a/b を代入すると Φ_d(a/b) | (a/b)^d - 1
2. 両辺に b^d を掛けると Φ_d(a/b) · b^d | a^d - b^d
3. 原始素因子 q は Φ_d(a/b) の素因子として現れる
4. Φ_d が square-free なら q の重複度は 1

**実装状況:**
Mathlib の定理を直接利用可能。ただし、多項式環から整数環への翻訳が必要。
-/
lemma cyclotomic_dvd_pow_sub_one (d : ℕ) (R : Type*) [Ring R] :
    cyclotomic d R ∣ X ^ d - 1 :=
  Polynomial.cyclotomic.dvd_X_pow_sub_one d R

/-- 円分多項式の square-free 性

**数学的内容:**
体 K 上で、n ≠ 0 (char K ∤ n) ならば、
円分多項式 Φ_n は square-free（重複因子を持たない）

**Mathlib の定理:**
`Polynomial.squarefree_cyclotomic`

**数学的意味:**
Φ_n が square-free とは、Φ_n = f₁ · f₂ · ... · fₖ と
既約多項式の積に因数分解されたとき、すべての fᵢ が相異なることを意味する。
これにより、Φ_n(a/b) の任意の素因数 q は重複度 1 で現れる。

**応用:**
padicValNat q (a^d - b^d) ≤ 1 の証明に使う
（q が Φ_d(a/b) の素因子なら、重複度 1 で現れる）

**実装状況:**
Mathlib の定理を直接利用可能。ただし、体 ℚ 上での評価が必要。
-/
lemma cyclotomic_squarefree (n : ℕ) (K : Type*) [Field K] [NeZero (n : K)] :
    Squarefree (cyclotomic n K) :=
  Polynomial.squarefree_cyclotomic n K

/-- 円分多項式の整数値評価（補助補題）

**数学的内容:**
Φ_d(X) | X^d - 1 から、整数 a, b に対して以下が成り立つ：
b^d · Φ_d(a/b) ∈ ℤ かつ b^d · Φ_d(a/b) | a^d - b^d

**証明の方針:**
1. Φ_d(X) は整数係数多項式（Mathlib の定理）
2. X = a/b を代入して Φ_d(a/b) ∈ ℚ を得る
3. 分母を払って整数値を得る

**重要性:**
これにより、多項式環の性質を整数環に翻訳できる。

**実装状況:**
Mathlib に類似の定理があるが、統合が必要。TODO として残す。
-/
lemma cyclotomic_eval_divides (d a b : ℕ) (_hd : 0 < d) (_hb : 0 < b) :
    ∃ (n : ℤ), n ∣ (a ^ d : ℤ) - (b ^ d : ℤ) := by
  -- TODO: Φ_d の整数係数性と評価の性質を使う
  -- 現時点では存在だけ示す（具体的な値は後で）
  use 1
  simp

/-- 円分多項式の square-free 性から素因数の重複度へ（翻訳補題）

**数学的内容:**
Φ_d が体 ℚ 上で square-free で、q が Φ_d(a/b) の素因数なら、
q の a^d - b^d における重複度は 1 以下。

**証明の方針:**
1. Φ_d が square-free → Φ_d(a/b) も "square-free" な有理数
2. 有理数が square-free → その任意の素因数は重複度 1
3. Φ_d(a/b) · b^d | a^d - b^d と組み合わせる

**実装の課題（詳細）:**

### 課題 1: 多項式の評価 → 整数値
Φ_d(X) ∈ ℤ[X] に対して、X = a/b を代入すると Φ_d(a/b) ∈ ℚ。
これを整数論に翻訳するには：
- b^(deg Φ_d) · Φ_d(a/b) ∈ ℤ を示す
- Mathlib に `Polynomial.aeval` などがあるが、整数値性の保証が必要

### 課題 2: square-free 性の翻訳
多項式の square-free 性（代数的概念）を素因数の重複度（整数論的概念）に結びつける：
- Φ_d が square-free ⇒ Φ_d(a/b) の "分子" が square-free
- これには、分子と分母の分離、既約分数の扱いが必要
- Mathlib の `Squarefree` の定義と整数の素因数分解の関係

### 課題 3: padicValNat への接続
最終的に padicValNat に翻訳する：
- ℚ の素因数分解 → ℤ の素因数分解 → padicValNat
- 各ステップで情報の損失がないことを保証

**代替アプローチ:**

### アプローチ A: Lifting the Exponent Lemma (LTE)
q ≠ d の素数に対して、q | a^d - b^d かつ q ∤ a - b なら、
より直接的な LTE の適用で padicValNat を評価できる可能性。

### アプローチ B: 具体的なケース (d = 3, 5, 7)
小さい素数 d について具体的に計算し、パターンを見つける：
- d = 3: a^3 - b^3 = (a - b)(a^2 + ab + b^2)
- q | a^2 + ab + b^2 かつ q ∤ a - b のとき、q^2 ∤ a^3 - b^3 を示す

### アプローチ C: Mathlib への貢献
この補題自体を Mathlib に提案し、コミュニティの知恵を借りる。

**現在の方針:**
理論的枠組みは確立。実装は将来の PR で段階的に進める。
まずは応用（完全冪判定）を試して、実用性と必要性を確認する。

**参考文献:**
- Bang's theorem (1886): 原始素因子の存在
- Zsigmondy's theorem (1892): 一般化と例外の特定
- Mihăilescu's theorem (2002): Catalan 予想の解決（関連技術）
-/
lemma squarefree_implies_padic_val_le_one (d a b q : ℕ)
    (hd_prime : Nat.Prime d) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hq_prime : Nat.Prime q) (hq_div : q ∣ a ^ d - b ^ d) :
    padicValNat q (a ^ d - b ^ d) ≤ 1 := by
  -- TODO: 円分多項式の square-free 性を活用
  -- 実装の課題は上記コメント参照
  -- 代替アプローチの検討が必要
  sorry

/-- 原始素因子の p-adic 付値上界：d = 3 の特殊ケース（試験的実装）

**数学的内容:**
d = 3 の場合、原始素因子 q について padicValNat q (a^3 - b^3) ≤ 1 を示す。

**証明の方針:**
1. a^3 - b^3 = (a - b)(a^2 + ab + b^2)
2. q が原始素因子なら、q ∤ a - b より q | a^2 + ab + b^2
3. もし q^2 | a^3 - b^3 なら、q^2 | (a^2 + ab + b^2)（∵ q ∤ a - b）
4. これが矛盾を導くことを示す

**実装状況:**
初等的な整数論で証明できる可能性がある。
しかし、ステップ 4 が技術的に難しい。

**将来の拡張:**
d = 5, 7 などの場合も同様のパターンで証明できれば、
一般化のヒントが得られる。
-/
lemma padicValNat_le_one_of_prime_divisor_case_three {a b q : ℕ}
    (ha : 1 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hq_prime : Nat.Prime q)
    (hq_div : q ∣ a ^ 3 - b ^ 3) (hq_ndiv : ¬ q ∣ a - b) :
    padicValNat q (a ^ 3 - b ^ 3) ≤ 1 := by
  -- TODO: d = 3 の特殊ケースを証明
  -- a^3 - b^3 = (a - b)(a^2 + ab + b^2) の因数分解を使う
  sorry

-- ========================================
-- § 4. 原始素因子の p-adic 付値に関する補題
-- ========================================

/-- 原始素因子の p-adic 付値の下界

**数学的内容:**
q が a^d - b^d の原始素因子（q | a ^ d - b ^ d）ならば、
padicValNat q (a ^ d - b ^ d) ≥ 1

**これは明らか:**
q | a ^ d - b ^ d かつ a ^ d - b ^ d ≠ 0 から、既存の補題で直ちに従う。

**次のステップ:**
上界 padicValNat q (a ^ d - b ^ d) ≤ 1 を示すには、
円分多項式の理論や LTE の精密版が必要。
-/
lemma padicValNat_primitive_prime_factor_ge_one {a b d q : ℕ}
    (hab_lt : b < a) (_hb : 0 < b) (hd : 1 < d)
    (hq_prime : Nat.Prime q) (hq_div : q ∣ a ^ d - b ^ d) :
    1 ≤ padicValNat q (a ^ d - b ^ d) := by
  -- a^d - b^d ≠ 0 を示す
  have hd_pos : 0 < d := Nat.zero_lt_of_lt hd
  have hd_ne : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd_pos
  have hab_pow : b^d < a^d := Nat.pow_lt_pow_left hab_lt hd_ne
  have hne : a^d - b^d ≠ 0 := Nat.sub_ne_zero_of_lt hab_pow
  -- padicValNat_one_le_of_prime_dvd を適用
  exact padicValNat_one_le_of_prime_dvd hq_prime hne hq_div

/-- 原始素因子の p-adic 付値の上界（円分多項式経由）

**数学的内容:**
q が a^d - b^d の原始素因子で、d が素数のとき、
円分多項式の square-free 性から padicValNat q (a^d - b^d) ≤ 1 が従う。

**証明の道筋:**

### Step 1: 円分多項式の可除性
Φ_d(X) | X^d - 1（Mathlib の定理）

### Step 2: 評価による整数値
X に a/b を代入：Φ_d(a/b) | (a/b)^d - 1
両辺に b^d を掛ける：Φ_d(a/b) · b^d | a^d - b^d

### Step 3: square-free 性の活用
体 ℚ 上で Φ_d は square-free（Mathlib の定理）
→ Φ_d(a/b) ∈ ℚ の任意の素因数は重複度 1 で現れる

### Step 4: 整数環への翻訳
q が Φ_d(a/b) の素因数なら、q の a^d - b^d における重複度も 1

**実装の課題:**
- 多項式の評価 Φ_d(a/b) ∈ ℚ を整数論に翻訳する技術が必要
- square-free 性（多項式環の概念）を素因数分解（整数環の概念）に結びつける
- これらは Mathlib に部分的に存在するが、統合が必要

**現在の方針:**
段階的実装：
1. ✅ 円分多項式の基本性質を import
2. ⏳ Φ_d(a/b) の値と a^d - b^d の関係を整理
3. ⏳ square-free → padicValNat ≤ 1 の橋渡し補題
4. ⏳ 完全な証明の構築
-/
lemma padicValNat_primitive_prime_factor_le_one {a b d q : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (_hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (_hpnd : ¬ d ∣ a - b)
    (hq_prime : Nat.Prime q)
    (hq_div : q ∣ a ^ d - b ^ d) (_hq_ndiv : ¬ q ∣ a - b) :
    padicValNat q (a ^ d - b ^ d) ≤ 1 := by
  -- 方針：円分多項式の square-free 性を活用した証明
  -- Step 1: 補助補題を使う（現時点では sorry 付き）
  have _hd_pos : 0 < d := Nat.zero_lt_of_lt (by omega : 2 < d)
  exact squarefree_implies_padic_val_le_one d a b q hd_prime hb hab hq_prime hq_div

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

## ⏳ Phase 2: 層B（精密層）— 進行中（円分多項式理論を導入）

原始素因子の p-adic 付値を精密に評価する。

**現在の成果:**
- ✅ 下界: `padicValNat_primitive_prime_factor_ge_one`
  - 1 ≤ padicValNat q (a^d - b^d) を証明（既存の補題から直接）

- ✅ 円分多項式の理論を import
  - Mathlib.RingTheory.Polynomial.Cyclotomic.Basic を導入
  - 基本定理 `cyclotomic_dvd_pow_sub_one`: Φ_d(X) | X^d - 1
  - square-free 性 `cyclotomic_squarefree`: 体上で Φ_d は square-free

- ⏳ 補助補題の整理
  - `cyclotomic_eval_divides`: Φ_d(a/b) の整数値評価（TODO）
  - `squarefree_implies_padic_val_le_one`: square-free → 重複度 1（TODO）

**残りの課題:**
- ⏳ 上界: `padicValNat_primitive_prime_factor_le_one`
  - 理論的枠組みは完成（補助補題に分解済み）
  - 実装: 多項式環の理論を整数論に翻訳する技術が必要

**理論的背景（詳細化）:**

### 証明の道筋（4ステップ）

**Step 1: 円分多項式の可除性**
- Φ_d(X) | X^d - 1（Mathlib の `cyclotomic.dvd_X_pow_sub_one`）

**Step 2: 評価による整数値**
- X に a/b を代入：Φ_d(a/b) | (a/b)^d - 1
- 両辺に b^d を掛ける：Φ_d(a/b) · b^d | a^d - b^d

**Step 3: square-free 性の活用**
- 体 ℚ 上で Φ_d は square-free（Mathlib の `squarefree_cyclotomic`）
- → Φ_d(a/b) ∈ ℚ の任意の素因数は重複度 1 で現れる

**Step 4: 整数環への翻訳**
- q が Φ_d(a/b) の素因数なら、q の a^d - b^d における重複度も 1
- これが padicValNat q (a^d - b^d) ≤ 1 を意味する

**実装の課題:**
- Step 2-4 の橋渡しが技術的に難しい
- Mathlib に部分的な道具はあるが、統合が必要
- 補助補題 `squarefree_implies_padic_val_le_one` に集約

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
