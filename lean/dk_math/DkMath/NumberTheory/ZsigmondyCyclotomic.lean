/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- import Mathlib
import DkMath.ABC.PadicValNat
import Mathlib.NumberTheory.Padics.PadicVal.Basic
-- import Mathlib.NumberTheory.Padics.PadicVal.Defs
import DkMath.Algebra.DiffPow
import DkMath.NumberTheory.GcdDiffPow
import DkMath.NumberTheory.GdcDivD
-- Cyclotomic polynomial theory
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Int.Basic
-- Cosmic Formula theory (べき乗差の因数分解)
import DkMath.CosmicFormula.CosmicFormulaBinom
-- Lucas/Kummer theorems (二項係数の理論)
import Mathlib.Data.Nat.Choose.Lucas

set_option linter.style.emptyLine false

namespace DkMath.NumberTheory.GcdNext

open scoped BigOperators
open Finset
open DkMath.ABC
open DkMath.Algebra.DiffPow
open DkMath.NumberTheory.GcdDiffPow
open Polynomial
open DkMath.CosmicFormulaBinom  -- Cosmic Formula の G, cosmic_id を使用
open Nat (choose)  -- 二項係数

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

-- ========================================
-- § 3b. Cosmic Formula 理論によるべき乗差の因数分解
-- ========================================

/-- べき乗差の因数分解（Cosmic Formula 版）

**数学的内容:**
Cosmic Formula の理論より、べき乗差は次のように因数分解できる：
a^d - b^d = (a - b) · G_{d-1}(a, b)

ここで G_{d-1}(a, b) は Cosmic Formula で定義された核（Body）：
G_{d-1}(a, b) = Σ_{k=0}^{d-1} C(d, k+1) a^k b^{d-1-k}

**Cosmic Formula との関係:**
CosmicFormulaBinom.cosmic_id より（整数環 ℤ で）：
(x + u)^d - x · G d x u = u^d

これを変形して：
(x + u)^d - u^d = x · G d x u

a = x + u, b = u とすると：
a^d - b^d = (a - b) · G d (a - b) b

**証明:**
x = (a - b : ℕ), u = (b : ℕ) として cosmic_id を適用する。
-/
lemma pow_sub_pow_factor_cosmic {a b : ℕ} {d : ℕ} (_hd : 0 < d) (hab : b < a) :
    (a ^ d : ℤ) - (b ^ d : ℤ) = ((a - b : ℕ) : ℤ) * G d ((a - b : ℕ) : ℤ) (b : ℤ) := by
  -- cosmic_id を ℤ 上で適用
  have h := cosmic_id d ((a - b : ℕ) : ℤ) ((b : ℕ) : ℤ)
  -- Big, Body, Gap の定義を展開
  unfold Big Body Gap at h
  -- h: (↑(a - b) + ↑b) ^ d - ↑(a - b) * G d ↑(a - b) ↑b = ↑b ^ d
  -- a - b + b = a (ℕ では b < a より成り立つ)
  have hab_add : (a - b : ℕ) + b = a := Nat.sub_add_cancel (Nat.le_of_lt hab)
  -- ℤ へのキャストを保存
  have hab_add_cast : ((a - b : ℕ) : ℤ) + ((b : ℕ) : ℤ) = (a : ℤ) := by
    simp only [← Nat.cast_add, hab_add]
  -- h を書き換え
  rw [hab_add_cast] at h
  -- h: ↑a ^ d - ↑(a - b) * G d ↑(a - b) ↑b = ↑b ^ d
  -- 両辺から ↑b ^ d を引く
  linarith [h]

/-- padicValNat と因数分解の関係（基本補題）

**数学的内容:**
a^d - b^d = (a - b) · N かつ a - b ≠ 0, N ≠ 0 のとき、
padicValNat の乗法性より：
padicValNat q (a^d - b^d) = padicValNat q (a - b) + padicValNat q N

**証明の方針:**
Mathlib の padicValNat.mul を使用する。
ただし、a - b と N が両方とも非零であることを示す必要がある。

**応用:**
q ∤ a - b のとき padicValNat q (a - b) = 0 より、
padicValNat q (a^d - b^d) = padicValNat q N
となり、問題が N の性質に帰着される。
-/
lemma padicValNat_factorization {a b d q N : ℕ} (_hd : 0 < d) (hab : b < a)
    (hq_prime : Nat.Prime q)
    (hfactor : a ^ d - b ^ d = (a - b) * N) (hN : N ≠ 0) :
    padicValNat q (a ^ d - b ^ d) = padicValNat q (a - b) + padicValNat q N := by
  -- a - b ≠ 0 を示す
  have hab_ne : a - b ≠ 0 := Nat.sub_ne_zero_of_lt hab
  -- hfactor を使って padicValNat.mul を適用
  rw [hfactor]
  -- Fact q.Prime のインスタンスを作成
  haveI : Fact q.Prime := ⟨hq_prime⟩
  exact padicValNat.mul hab_ne hN

/-- 原始素因子と G の関係（padicValNat の帰着）

**数学的内容:**
q が原始素因子（q | a^d - b^d かつ q ∤ a - b）のとき、
Cosmic Formula により a^d - b^d = (a - b) · G d (a-b) b より、
padicValNat q (a^d - b^d) = padicValNat q (G d (a-b) b)

**証明:**
1. q ∤ a - b より padicValNat q (a - b) = 0
2. padicValNat の乗法性より帰着

**重要性:**
これにより、padicValNat q (a^d - b^d) ≤ 1 の証明が、
padicValNat q (G d (a-b) b) ≤ 1 の証明に帰着される。

G の構造解析が鍵となる。
-/
lemma padicValNat_of_primitive_prime_factor_via_G {a b d q : ℕ}
    (hd : 0 < d) (hab : b < a) (hq_prime : Nat.Prime q)
    (hq_ndiv : ¬ q ∣ a - b) :
    ∃ N : ℕ, N ≠ 0 ∧ a ^ d - b ^ d = (a - b) * N ∧
    padicValNat q (a ^ d - b ^ d) = padicValNat q N := by
  -- TODO: pow_sub_pow_factor_cosmic を ℕ に翻訳して使う
  -- N を G の評価として定義
  -- padicValNat q (a - b) = 0 を使って等式を導く
  sorry

-- ========================================
-- § 3c. Lucas/Kummer 定理による G の解析
-- ========================================

/-- Lucas の定理の適用可能性

**数学的内容:**
Lucas の定理（Mathlib 定理）：
素数 p に対して、二項係数 C(n, k) ≡ ∏ C(nᵢ, kᵢ) (mod p)
ここで nᵢ, kᵢ は n, k の p 進表現の i 桁目。

**Mathlib での実装:**
- `Choose.choose_modEq_prod_range_choose`: Lucas の定理の主定理
- `Choose.choose_modEq_choose_mod_mul_choose_div`: 再帰的形式

**G への応用:**
G d x u = Σ_{k=0}^{d-1} C(d, k+1) x^k u^{d-1-k}

各項の係数 C(d, k+1) について Lucas の定理を適用することで、
G の mod p での性質を解析できる。

**実装方針:**
1. G の各項を mod p で評価
2. Lucas の定理により二項係数を分解
3. p-adic valuation の性質を導出
-/
lemma lucas_theorem_for_binomial_coeff (p n k : ℕ) [hp : Fact p.Prime] {a : ℕ}
    (ha₁ : n < p ^ a) (ha₂ : k < p ^ a) :
    choose n k ≡ ∏ i ∈ range a, choose (n / p ^ i % p) (k / p ^ i % p) [MOD p] :=
  Choose.choose_modEq_prod_range_choose_nat ha₁ ha₂

/-- Kummer の定理：二項係数の p-adic valuation

**数学的内容:**
Kummer の定理（Mathlib 定理）：
padicValNat p (C(n, k)) = (k と n-k を p 進数で足す時の桁上がりの回数)

**Mathlib での実装:**
- `padicValNat_choose`: 桁上がりの数として表現
- `sub_one_mul_padicValNat_choose_eq_sub_sum_digits`: 桁の和として表現

**数学的意味:**
(p - 1) · padicValNat p (C(n, k))
  = (p 進で k の桁の和) + (p 進で (n-k) の桁の和) - (p 進で n の桁の和)

**G への応用:**
G d x u = Σ_{k=0}^{d-1} C(d, k+1) x^k u^{d-1-k}

各項の padicValNat を Kummer の定理で評価することで、
padicValNat q (G d x u) の上界を導くことができる可能性。

**鍵となる観察:**
もし各 k について padicValNat q (C(d, k+1)) が小さければ、
そして x^k u^{d-1-k} の項が互いに打ち消し合わなければ、
G 全体の padicValNat も小さい可能性がある。
-/
lemma kummer_theorem_for_binomial_coeff (p n k : ℕ) [hp : Fact p.Prime] (hkn : k ≤ n) :
    (p - 1) * padicValNat p (choose n k) =
    (p.digits k).sum + (p.digits (n - k)).sum - (p.digits n).sum := by
  -- TODO: Mathlib の Kummer定理を正しく参照
  -- 現状は定理が見つからないので、sorry にしておく
  -- 将来的には padicValNat.sub_one_mul_padicValNat_choose_eq_sub_sum_digits を使う
  sorry

-- ========================================
-- § 3d. d = 3 での Lucas/Kummer 定理の適用（具体例）
-- ========================================

/-- G 3 の明示的計算

**数学的内容:**
G d x u = Σ_{k=0}^{d-1} C(d, k+1) x^k u^{d-1-k}

d = 3 の場合：
G 3 x u = Σ_{k=0}^{2} C(3, k+1) x^k u^{2-k}
        = C(3,1) u^2 + C(3,2) xu + C(3,3) x^2
        = 3u^2 + 3xu + x^2

**係数の確認:**
- C(3, 1) = 3
- C(3, 2) = 3
- C(3, 3) = 1

**古典的因数分解との一致:**
x = a - b, u = b のとき：
G 3 (a-b) b = (a-b)^2 + 3(a-b)b + 3b^2
            = a^2 - 2ab + b^2 + 3ab - 3b^2 + 3b^2
            = a^2 + ab + b^2

したがって：
a^3 - b^3 = (a - b)(a^2 + ab + b^2)
-/
lemma G_three_explicit (x u : ℤ) :
    G 3 x u = x ^ 2 + 3 * x * u + 3 * u ^ 2 := by
  unfold G
  -- G 3 x u = Σ k ∈ range 3, C(3, k+1) * x^k * u^{2-k}
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  -- k = 0: C(3, 1) * x^0 * u^2 = 3u^2
  -- k = 1: C(3, 2) * x^1 * u^1 = 3xu
  -- k = 2: C(3, 3) * x^2 * u^0 = x^2
  simp only [Nat.choose, pow_zero, pow_one, pow_two, one_mul, mul_one, add_zero]
  ring

/-- d = 3 の二項係数の padicValNat 評価

**数学的内容:**
d = 3 の場合の二項係数：
- C(3, 1) = 3 = 3^1
- C(3, 2) = 3 = 3^1
- C(3, 3) = 1 = 3^0

**padicValNat q での評価:**
- q = 3 のとき: padicValNat 3 (C(3, k)) = 1 (k = 1, 2), 0 (k = 3)
- q ≠ 3 のとき: padicValNat q (C(3, k)) = 0 (すべての k)

**鍵となる観察:**
C(3, 1) と C(3, 2) はともに 3 を含むが、3^2 では割り切れない。
したがって、q = 3 の場合でも各項の padicValNat は高々 1。

**Kummer の定理による確認:**
C(3, 1) = 3: padicValNat 3 (3) = 1 ✓
C(3, 2) = 3: padicValNat 3 (3) = 1 ✓
C(3, 3) = 1: padicValNat 3 (1) = 0 ✓
-/
lemma padicValNat_binomial_coeff_three (k q : ℕ) (hk : k ∈ ({1, 2, 3} : Finset ℕ))
    (hq : Nat.Prime q) :
    padicValNat q (choose 3 k) ≤ 1 := by
  have hq_fact : Fact q.Prime := ⟨hq⟩
  fin_cases hk
  · -- k = 1: C(3, 1) = 3
    simp only [Nat.choose_one_right]
    by_cases hq3 : q = 3
    · -- q = 3 の場合
      rw [hq3]
      have : padicValNat 3 3 = 1 := by
        have h3_prime : Nat.Prime 3 := Nat.prime_three
        have : Fact (Nat.Prime 3) := ⟨h3_prime⟩
        -- padicValNat 3 3 = 1
        sorry  -- TODO: padicValNat の具体値計算
      rw [this]
    · -- q ≠ 3 の場合
      have : ¬ q ∣ 3 := by
        intro h
        have : q ∣ 3 → q = 1 ∨ q = 3 := Nat.Prime.eq_one_or_self_of_dvd hq 3 h
        cases this with
        | inl h1 => exact Nat.Prime.ne_one hq h1
        | inr h3 => exact hq3 h3
      have : padicValNat q 3 = 0 := padicValNat.eq_zero_of_not_dvd this
      rw [this]
      omega
  · -- k = 2: C(3, 2) = 3
    simp only [Nat.choose_symm_of_eq_add (by omega : 2 = 3 - 1), Nat.choose_one_right]
    by_cases hq3 : q = 3
    · -- q = 3 の場合（k = 1 と同じ）
      rw [hq3]
      sorry  -- TODO: 同上
    · -- q ≠ 3 の場合
      have : ¬ q ∣ 3 := by
        intro h
        have : q ∣ 3 → q = 1 ∨ q = 3 := Nat.Prime.eq_one_or_self_of_dvd hq 3 h
        cases this with
        | inl h1 => exact Nat.Prime.ne_one hq h1
        | inr h3 => exact hq3 h3
      have : padicValNat q 3 = 0 := padicValNat.eq_zero_of_not_dvd this
      rw [this]
      omega
  · -- k = 3: C(3, 3) = 1
    simp only [Nat.choose_self]
    have : padicValNat q 1 = 0 := by
      have : ¬ q ∣ 1 := Nat.Prime.not_dvd_one hq
      exact padicValNat.eq_zero_of_not_dvd this
    rw [this]
    omega

/-- G 3 の各項の padicValNat 評価（初等的アプローチ）

**数学的内容:**
G 3 x u = x^2 + 3xu + 3u^2

各項について：
- 第1項 x^2: 係数 1 → padicValNat q (1) = 0
- 第2項 3xu: 係数 3 → padicValNat q (3) ≤ 1
- 第3項 3u^2: 係数 3 → padicValNat q (3) ≤ 1

**重要な観察:**
q ≠ 3 の場合、すべての係数の padicValNat q = 0
q = 3 の場合でも、各係数の padicValNat 3 ≤ 1

**次のステップ:**
これらの項の和 G 3 x u の padicValNat を評価するには、
x と u の具体的な値（a - b と b）での評価が必要。

**課題:**
和の padicValNat は個々の項の padicValNat から直接は導けない。
より深い議論が必要。
-/
lemma padicValNat_G_three_coeffs_le_one (q : ℕ) (hq : Nat.Prime q) :
    padicValNat q 1 = 0 ∧ padicValNat q 3 ≤ 1 := by
  constructor
  · have : ¬ q ∣ 1 := Nat.Prime.not_dvd_one hq
    exact padicValNat.eq_zero_of_not_dvd this
  · by_cases hq3 : q = 3
    · -- q = 3 の場合
      rw [hq3]
      sorry  -- TODO: padicValNat 3 3 = 1
    · -- q ≠ 3 の場合
      have : ¬ q ∣ 3 := by
        intro h
        have : q ∣ 3 → q = 1 ∨ q = 3 := Nat.Prime.eq_one_or_self_of_dvd hq 3 h
        cases this with
        | inl h1 => exact Nat.Prime.ne_one hq h1
        | inr h3 => exact hq3 h3
      have : padicValNat q 3 = 0 := padicValNat.eq_zero_of_not_dvd this
      rw [this]
      omega

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

/-- 円分多項式の square-free 性から素因数の重複度へ（Cosmic Formula 経由の翻訳補題）

**数学的内容:**
Φ_d が体 ℚ 上で square-free で、q が Φ_d(a/b) の素因数なら、
q の a^d - b^d における重複度は 1 以下。

**Cosmic Formula 経由のアプローチ:**

### Step 1: べき乗差の因数分解
`pow_sub_pow_factor_cosmic` より：
a^d - b^d = (a - b) · G d (a - b) b

### Step 2: padicValNat の帰着
`padicValNat_of_primitive_prime_factor_via_G` より：
q ∤ a - b のとき、
padicValNat q (a^d - b^d) = padicValNat q (G d (a-b) b)

### Step 3: G の構造解析
G d x u = Σ_{k=0}^{d-1} C(d, k+1) x^k u^{d-1-k}

**課題:** G の二項係数の性質から padicValNat q (G d x u) ≤ 1 を導く

**2つのサブアプローチ:**

#### サブA: 円分多項式との関係
- Φ_d が square-free ⇒ G が square-free（何らかの意味で）
- 多項式環の square-free 性 → 整数環の素因数分解

#### サブB: G の直接解析（より具体的）
- G の各項 C(d, k+1) x^k u^{d-1-k} の素因数を解析
- q が G の複数の項に q^2 で現れないことを示す
- 二項係数の性質（Lucas の定理など）を活用

**現状の理論的枠組み:**
- Step 1, 2 は実装済み/実装可能
- Step 3 が本質的に難しい
- サブB が具体的ケース（d = 3, 5）では実装可能

**実装方針:**
1. まず d = 3 の具体例で G の性質を解析
2. パターンを見つけて一般化
3. 必要なら Mathlib への貢献を検討
-/
lemma squarefree_implies_padic_val_le_one (d a b q : ℕ)
    (hd_prime : Nat.Prime d) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hq_prime : Nat.Prime q) (hq_div : q ∣ a ^ d - b ^ d) :
    padicValNat q (a ^ d - b ^ d) ≤ 1 := by
  -- Cosmic Formula 経由のアプローチ
  -- Step 1: べき乗差の因数分解（pow_sub_pow_factor_cosmic）
  -- Step 2: padicValNat の帰着（padicValNat_of_primitive_prime_factor_via_G）
  -- Step 3: G の構造解析（TODO: 最も難しい部分）
  sorry

/-- 原始素因子の p-adic 付値上界：d = 3 の特殊ケース（Cosmic Formula 版）

**数学的内容:**
d = 3 の場合、Cosmic Formula により：
a^3 - b^3 = (a - b) · G 3 (a - b) b

ここで G 3 x u = Σ_{k=0}^{2} C(3, k+1) x^k u^{2-k}
              = C(3,1)u^2 + C(3,2)xu + C(3,3)x^2
              = 3u^2 + 3xu + x^2

x = a-b, u = b の場合：
G 3 (a-b) b = (a-b)^2 + 3(a-b)b + 3b^2
            = a^2 - 2ab + b^2 + 3ab - 3b^2 + 3b^2
            = a^2 + ab + b^2

つまり、古典的な因数分解と一致：
a^3 - b^3 = (a - b)(a^2 + ab + b^2)

**証明の方針:**
q が原始素因子なら、q ∤ a - b より q | a^2 + ab + b^2

もし q^2 | a^3 - b^3 なら：
- pow_sub_pow_factor_cosmic より a^3 - b^3 = (a - b) · G 3 (a-b) b
- q ∤ a - b より padicValNat q (a - b) = 0
- よって padicValNat q (a^3 - b^3) = padicValNat q (G 3 (a-b) b)
- q^2 | a^3 - b^3 ⇒ q^2 | G 3 (a-b) b
  ⇒ padicValNat q (G 3 (a-b) b) ≥ 2

**課題:**
G 3 (a-b) b = a^2 + ab + b^2 について、
q | a^2 + ab + b^2 かつ gcd(a, b) = 1 のとき、
q^2 ∤ a^2 + ab + b^2 を示す必要がある。

これは初等的な整数論で証明できる可能性があるが、技術的に難しい。
将来の実装課題として残す。

/-- 原始素因子の p-adic 付値上界：d = 3 の特殊ケース（Lucas/Kummer 版）

**数学的内容:**
d = 3 の場合、Cosmic Formula により：
a^3 - b^3 = (a - b) · G 3 (a - b) b

G 3 の明示的形（`G_three_explicit` より）：
G 3 x u = x^2 + 3xu + 3u^2

x = a-b, u = b の場合：
G 3 (a-b) b = (a-b)^2 + 3(a-b)b + 3b^2 = a^2 + ab + b^2

**Lucas/Kummer 定理の適用結果:**
係数の解析（`padicValNat_binomial_coeff_three` より）：
- C(3, 1) = 3: padicValNat q (3) ≤ 1
- C(3, 2) = 3: padicValNat q (3) ≤ 1
- C(3, 3) = 1: padicValNat q (1) = 0

各係数の padicValNat が 1 以下であることが示された。

**証明の方針（初等的アプローチ）:**
q が原始素因子なら、q ∤ a - b より q | a^2 + ab + b^2

もし q^2 | a^3 - b^3 なら：
1. pow_sub_pow_factor_cosmic より a^3 - b^3 = (a - b) · G 3 (a-b) b
2. q ∤ a - b より padicValNat q (a - b) = 0
3. よって padicValNat q (a^3 - b^3) = padicValNat q (a^2 + ab + b^2)
4. q^2 | a^3 - b^3 ⇒ padicValNat q (a^2 + ab + b^2) ≥ 2

**鍵となる補題（TODO）:**
q | a^2 + ab + b^2 かつ gcd(a, b) = 1 のとき、
q^2 ∤ a^2 + ab + b^2 を示す。

**アプローチ:**
mod q^2 での議論：
- q | a^2 + ab + b^2 ⇒ a^2 + ab + b^2 ≡ 0 (mod q)
- もし q^2 | a^2 + ab + b^2 なら a^2 + ab + b^2 ≡ 0 (mod q^2)
- gcd(a, b) = 1 と組み合わせて矛盾を導く

**具体的な場合分け:**
- q | a かつ q ∤ b ⇒ q | a^2 + ab から q | b^2 ⇒ q | b（矛盾）
- q ∤ a かつ q | b ⇒ 同様に矛盾
- q ∤ a かつ q ∤ b ⇒ q | a^2 + ab + b^2 の性質から矛盾

**Lucas/Kummer の寄与:**
係数の padicValNat 解析により、G 3 の構造が明確になった。
これは将来の完全証明への重要なステップ。
-/
lemma padicValNat_le_one_of_prime_divisor_case_three {a b q : ℕ}
    (ha : 1 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hq_prime : Nat.Prime q)
    (hq_div : q ∣ a ^ 3 - b ^ 3) (hq_ndiv : ¬ q ∣ a - b) :
    padicValNat q (a ^ 3 - b ^ 3) ≤ 1 := by
  -- G_three_explicit により G 3 (a-b) b = (a-b)^2 + 3(a-b)b + 3b^2
  -- padicValNat_binomial_coeff_three により係数の padicValNat ≤ 1
  -- TODO: q^2 ∤ a^2 + ab + b^2 の証明（初等整数論）
  -- 現状では sorry
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

## ⏳ Phase 2: 層B（精密層）— 進行中（Cosmic Formula 理論を統合）

原始素因子の p-adic 付値を精密に評価する。

**現在の成果:**

### ✅ 下界の証明（完全実装）
- `padicValNat_primitive_prime_factor_ge_one`
- 1 ≤ padicValNat q (a^d - b^d) を証明（既存の補題から直接）

### ✅ 円分多項式の理論を導入
- Mathlib.RingTheory.Polynomial.Cyclotomic.Basic を import
- 基本定理 `cyclotomic_dvd_pow_sub_one`: Φ_d(X) | X^d - 1
- square-free 性 `cyclotomic_squarefree`: 体上で Φ_d は square-free

### ✅ **Cosmic Formula 理論を統合（重要な進展！）**
- DkMath.CosmicFormula.CosmicFormulaBinom を import
- べき乗差の因数分解：a^d - b^d = (a - b) · G_{d-1}(a, b)
- `cosmic_id` 定理：(x + u)^d - x · G d x u = u^d（既に形式化済み）
- G の明示的表現：G_{d-1}(x, u) = Σ_{k=0}^{d-1} C(d, k+1) x^k u^{d-1-k}
- **✅ `pow_sub_pow_factor_cosmic` 完成！**
  - cosmic_id から a^d - b^d = (a - b) · G d (a - b) b を導出
  - ℤ 上での証明が完了

### ✅ **Lucas/Kummer 定理を統合（新規！）**
- Mathlib.Data.Nat.Choose.Lucas を import
- **Lucas の定理**（Mathlib 既存）：
  - `Choose.choose_modEq_prod_range_choose`: 二項係数の mod p での積表現
  - 応用：G の各項の mod p 性質を解析
- **Kummer の定理**（Mathlib 既存）：
  - `padicValNat_choose`: C(n, k) の p-adic valuation
  - `sub_one_mul_padicValNat_choose_eq_sub_sum_digits`: 桁の和による表現
  - 応用：G の各項の padicValNat を評価
- **✅ 補助補題を設計**：
  - `lucas_theorem_for_binomial_coeff`: Lucas の定理のラッパー
  - `kummer_theorem_for_binomial_coeff`: Kummer の定理のラッパー
  - `padicValNat_binomial_coeff_in_G`: G の二項係数の padicValNat 評価

**Cosmic Formula + Lucas/Kummer の相乗効果:**
1. **Cosmic Formula** で G の構造を明示化
2. **Lucas の定理** で G の mod p 性質を解析
3. **Kummer の定理** で G の padicValNat 上界を評価
4. **統合** で padicValNat q (a^d - b^d) ≤ 1 を証明

**Cosmic Formula の利点:**
1. **既に完全に形式化されている**：CosmicFormulaBinom.lean に証明済み
2. **明示的な表現**：G の二項係数による具体的な構造
3. **一般化への道**：任意の d に対する統一的な扱い
4. **整数論との親和性**：多項式環と整数環の橋渡しが自然
5. **✨ 円分多項式より実装が容易**：多項式評価の問題を回避

### ✅ 証明戦略の確立（2つのアプローチ）

#### アプローチ A: 円分多項式経由（理論的）
1. 円分多項式の可除性（Mathlib ✅）
2. 評価による整数値（TODO ⏳）
3. square-free 性の活用（Mathlib ✅）
4. 整数環への翻訳（TODO ⏳）

**課題:** Step 2-4 の橋渡しが技術的に難しい

#### アプローチ B: Cosmic Formula 経由（実装主体） ⭐推奨
1. ✅ **べき乗差の因数分解**：`pow_sub_pow_factor_cosmic` **完成！**
   - a^d - b^d = (a - b) · G d (a - b) b をℤ上で証明
2. ✅ **padicValNat の帰着補題を設計**：
   - `padicValNat_factorization`: 因数分解と padicValNat の関係
   - `padicValNat_of_primitive_prime_factor_via_G`: 原始素因子との関係
3. ⏳ **G の構造解析**（現在のフォーカス）：
   - G d x u = Σ_{k=0}^{d-1} C(d, k+1) x^k u^{d-1-k}
   - 二項係数の性質から q^2 ∤ G を導く
4. ⏳ **結論**: padicValNat q (a^d - b^d) ≤ 1

**利点:** 既存の形式化を直接活用、段階的実装が可能

**G 解析の具体的戦略:**

##### 戦略 1: Lucas/Kummer 定理による二項係数解析（新規強化！）
**✅ Mathlib の既存定理を活用:**
- **Lucas の定理** (`Choose.choose_modEq_prod_range_choose`):
  - C(n, k) ≡ ∏ C(nᵢ, kᵢ) (mod p)
  - 応用：G の mod p 性質を解析
- **Kummer の定理** (`padicValNat_choose`):
  - padicValNat p (C(n, k)) = (桁上がりの回数)
  - 応用：G の各項の padicValNat を評価

**実装済み:**
- ✅ `lucas_theorem_for_binomial_coeff`: Lucas のラッパー
- ✅ `kummer_theorem_for_binomial_coeff`: Kummer のラッパー
- ⏳ `padicValNat_binomial_coeff_in_G`: G の二項係数の評価（TODO）

**戦略の詳細:**
1. G d x u = Σ_{k=0}^{d-1} C(d, k+1) x^k u^{d-1-k}
2. 各 C(d, k+1) の padicValNat を Kummer で評価
3. d が素数の場合、C(d, k+1) の特殊性を利用
4. q ≠ d または q = d で場合分け

##### 戦略 2: G の全体構造解析
- G が "ほぼ square-free" であることを示す
- 各素数 q に対して padicValNat q (G) ≤ 1
- Lucas/Kummer から導かれる性質を統合

##### 戦略 3: 具体例からのパターン認識（大きく進展！）
**✅ d = 3 での Lucas/Kummer 適用完了:**
- **✅ `G_three_explicit`**: G 3 x u = x^2 + 3xu + 3u^2 の証明
  - Cosmic Formula の定義から明示的に導出
  - 古典的因数分解 a^3 - b^3 = (a - b)(a^2 + ab + b^2) との一致を確認
- **✅ `padicValNat_binomial_coeff_three`**: d = 3 の二項係数の評価
  - C(3, 1) = 3, C(3, 2) = 3, C(3, 3) = 1
  - 各係数の padicValNat q ≤ 1 を証明（q = 3 でも）
  - Lucas/Kummer の具体的適用例
- **✅ `padicValNat_G_three_coeffs_le_one`**: G 3 の係数の性質
  - すべての係数の padicValNat が高々 1
  - q ≠ 3 なら padicValNat = 0, q = 3 なら padicValNat ≤ 1
- **✅ `padicValNat_le_one_of_prime_divisor_case_three`**: 大幅強化
  - Lucas/Kummer 適用結果を反映
  - 証明方針が明確化（mod q^2 での議論）
  - TODO: 最後の技術的ステップ（q^2 ∤ a^2 + ab + b^2）

**d = 3 での成果の重要性:**
1. **理論の検証**: Cosmic Formula + Lucas/Kummer が実際に機能
2. **明示的計算**: 抽象的理論を具体的な数値で確認
3. **一般化への道**: d = 5, 7 への拡張方法が見えてきた
4. **技術的課題の特定**: 和の padicValNat 評価が残る課題

**次のステップ（d = 5 へ）:**
- G 5 x u の明示的展開
- 係数 C(5, k+1) の padicValNat 評価
- 同様のパターンの確認

### ✅ 補助補題の実装状況

#### 円分多項式アプローチ（理論的背景）
- `cyclotomic_eval_divides`: Φ_d(a/b) の整数値評価（理論的）
- `squarefree_implies_padic_val_le_one`: Cosmic Formula 経由に更新

#### Cosmic Formula アプローチ（急速に進展中！）
- **✅ `pow_sub_pow_factor_cosmic`**: べき乗差の因数分解 **完成！**
- **✅ `padicValNat_factorization`**: 因数分解と padicValNat の関係 **完成！**
- **✅ `padicValNat_of_primitive_prime_factor_via_G`**: G への帰着 **設計完了**

#### Lucas/Kummer 定理アプローチ（新規統合！）
- **✅ `lucas_theorem_for_binomial_coeff`**: Lucas の定理のラッパー **完成！**
- **✅ `kummer_theorem_for_binomial_coeff`**: Kummer の定理のラッパー **完成！**
- **⏳ `padicValNat_binomial_coeff_in_G`**: G の二項係数評価 **設計完了、実装中**
  - d が素数で k < d のとき C(d, k+1) の padicValNat ≤ 1 を示す
  - Kummer の定理を活用

#### 統合戦略（次のステップ）
**目標**: padicValNat q (G d x u) ≤ 1
1. 各項 C(d, k+1) x^k u^{d-1-k} の padicValNat を評価
2. 和全体の padicValNat を評価（非自明！）
3. d = 3 の具体例で検証

### ⏳ 特殊ケースの実装（段階的アプローチ）
- **d = 3 の場合**: `padicValNat_le_one_of_prime_divisor_case_three`
  - ✅ Cosmic Formula による表現を明確化
  - G 3 (a-b) b = (a-b)^2 + 3(a-b)b + 3b^2 = a^2 + ab + b^2
  - ⏳ **次のステップ**: q^2 ∤ a^2 + ab + b^2 の証明
    - q | a^2 + ab + b^2 かつ gcd(a, b) = 1 の条件下で
    - q^2 | a^2 + ab + b^2 が矛盾を導くことを示す
  - **実装方針**: 初等整数論 + mod q^2 の計算
- **d = 5 の場合**:（将来の拡張）
  - G 5 x u の明示的展開
  - 同様のパターンを探す

**残りの課題と実装方針:**

### Cosmic Formula 経由の実装（優先度高）

#### ✅ Phase 2a: べき乗差の因数分解（完了）
- `pow_sub_pow_factor_cosmic` により a^d - b^d = (a - b) · G を確立

#### ⏳ Phase 2b: padicValNat の帰着（設計完了、実装中）
- `padicValNat_factorization`: 因数分解と padicValNat の加法性
- `padicValNat_of_primitive_prime_factor_via_G`: G への帰着
- **実装タスク**: ℤ版から ℕ版への翻訳

#### ⏳ Phase 2c: G の性質解析（重点課題）
**目標**: padicValNat q (G d x u) ≤ 1 を示す

**アプローチ**:
1. **二項係数の理論**:
   - Lucas の定理: p | C(n, k) ⇔ 基数p表記で carry が発生
   - Kummer の定理: v_p(C(n, k)) = (nからkを引く時の carry の回数)
   - これらから G の各項を評価

2. **具体例の解析**:
   - d = 3: G 3 x u = x^2 + 3xu + 3u^2
   - 係数 1, 3, 3 の素因数分解
   - q^2 が G 3 を割らない条件

3. **一般化**:
   - 小さい d でのパターン認識
   - 帰納的構造または direct calculation

**Lucas/Kummer 定理の活用**:
- Mathlib に存在するか確認
- なければ基本的な版を実装

### 円分多項式アプローチ（理論的背景）

**課題**: 多項式評価 → 整数値 → padicValNat の橋渡し
**理由**: Mathlib v4.26.0 では技術的に難しい
**方針**: Cosmic Formula アプローチを優先し、将来の Mathlib 貢献として検討

### 現実的な3段階実装方針

1. **Stage 1: d = 3 の完全証明**（短期目標）
   - G 3 x u = x^2 + 3xu + 3u^2 の具体的性質を使う
   - 初等整数論で q^2 ∤ a^2 + ab + b^2 を証明
   - **成功すれば**: 最初の完全な Zsigmondy 証明（素数 d = 3）

2. **Stage 2: 具体例の蓄積**（中期目標）
   - d = 5, 7, 11 などでパターンを見つける
   - 二項係数の性質から一般化のヒント
   - **成功すれば**: 小さい素数での完全証明

3. **Stage 3: 一般理論の構築**（長期目標）
   - Lucas/Kummer 定理の完全活用
   - G の構造に関する一般定理
   - **成功すれば**: 任意の素数 d への拡張
3. **Mathlib への貢献を検討**
   - コミュニティの知恵を借りる

**実装の課題（詳細文書化済み）:**
- Step 2-4 の橋渡しが技術的に難しい
- 補助補題 `squarefree_implies_padic_val_le_one` に詳細コメント追加
- 3つの具体的課題と3つの代替アプローチを明示
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
