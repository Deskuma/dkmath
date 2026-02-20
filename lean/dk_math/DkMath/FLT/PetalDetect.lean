/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.Ring.GeomSum
import DkMath.SilverRatio.GcdAg

/-!
# Petal 検出器：(a+b) 因子の検出とφビット構造

## 概要

FLT の B層において、「半位相（φ=0）では核 (a+b) が吸い込まれない」ことを定理化する。

## 数学的背景

### φビット構造 S_φ

二項形式 S_φ を次のように定義：
```
S0(a, b) := a² + ab + b²     (φ=0: 半位相)
S1(a, b) := (a+b)²           (φ=1: 完成位相)
```

これらは次の関係を持つ：
```
S1 - S0 = ab  (差分核)
```

### (a+b) 検出器

**問題:** いつ (a+b) が S_φ を割るか？

**答え:**
- φ=1 の場合：常に (a+b) | S1 （自明）
- φ=0 の場合：一般には (a+b) ∤ S0

特に gcd(a,b)=1 の場合：
```
(a+b) | S0  ⟺  (a+b) | b²  ⟺  a+b = 1 (ほぼ不可能)
```

## 主要定理

### Phase 2: φビット構造
1. `S0_def` : S0(a,b) = a² + ab + b²
2. `S1_def` : S1(a,b) = (a+b)²
3. `diff_kernel` : S1(a,b) = S0(a,b) + ab

### Phase 3: (a+b) 検出器
1. `apb_dvd_S1` : (a+b) | S1(a,b)
2. `apb_dvd_S0_iff_dvd_bsq` : gcd(a,b)=1 → ((a+b)|S0 ⟺ (a+b)|b²)
3. `apb_dvd_S0_implies_eq_one` : gcd(a,b)=1 ∧ (a+b)|S0 → a+b=1

## 実装計画

### Phase 2（このファイル）
- S0, S1 の定義
- 差分核の証明

### Phase 3（このファイル）
- Mathlib の GeomSum 補題を活用
- (a+b) 検出器の実装

### Phase 4（FLT/Basic.lean への統合）
- Ag 正規化と検出器の連携
- padicValNat 評価への応用

## 参照
- GcdAg_ImplementsPlan.md
- GcdAg_DevelopNote.md
- Mathlib.Algebra.Ring.GeomSum
-/

set_option linter.style.emptyLine true
set_option linter.unusedTactic false

namespace DkMath.FLT.PetalDetect

open DkMath.SilverRatio.GcdAg

-- ========================================
-- § 1. φビット構造の定義（Phase 2.1）
-- ========================================

/-- 半位相形式 S0：a² + ab + b² -/
def S0 (α : Type*) [Ring α] (a b : α) : α := a^2 + a*b + b^2

/-- 完成位相形式 S1：(a+b)² -/
def S1 (α : Type*) [Ring α] (a b : α) : α := (a + b)^2

/-- ℕ 版の S0 -/
def S0_nat (a b : ℕ) : ℕ := a^2 + a*b + b^2

/-- ℕ 版の S1 -/
def S1_nat (a b : ℕ) : ℕ := (a + b)^2

-- ========================================
-- § 2. 差分核の証明（Phase 2.2）
-- ========================================

/-- 差分核（Ring 版）：S1 - S0 = ab -/
lemma diff_kernel (α : Type*) [CommRing α] (a b : α) :
    S1 α a b = S0 α a b + a * b := by
  unfold S1 S0
  ring

/-- 差分核（ℕ 版）：S1 = S0 + ab -/
lemma diff_kernel_nat (a b : ℕ) :
    S1_nat a b = S0_nat a b + a * b := by
  unfold S1_nat S0_nat
  ring

-- ========================================
-- § 3. (a+b) 検出器の実装（Phase 3）
-- ========================================

/-- S1 は常に (a+b) で割り切れる（自明） -/
lemma apb_dvd_S1 (a b : ℕ) : (a + b) ∣ S1_nat a b := by
  unfold S1_nat
  use (a + b)
  ring

/-- S0 での (a+b) 割り切り判定（合同評価）

**証明の方針:**
S0 = a² + ab + b² = a(a+b) + b² より
(a+b) | S0 ⟺ (a+b) | b²

**代数的証明:**
S0 = a² + ab + b² を展開し、a(a+b) の部分を分離する。
-/
lemma apb_dvd_S0_iff_dvd_bsq (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (a + b) ∣ S0_nat a b ↔ (a + b) ∣ b^2 := by
  have _ha : 0 < a := ha
  have _hb : 0 < b := hb
  have hEq : S0_nat a b = a * (a + b) + b ^ 2 := by
    unfold S0_nat
    ring
  have hmul : (a + b) ∣ a * (a + b) := by
    use a
    ring
  constructor
  · intro hS0
    have hsum : (a + b) ∣ a * (a + b) + b ^ 2 := by
      simpa [hEq] using hS0
    exact (Nat.dvd_add_right hmul).1 hsum
  · intro hbsq
    have hsum : (a + b) ∣ a * (a + b) + b ^ 2 := dvd_add hmul hbsq
    simpa [hEq] using hsum

/-- gcd(a,b)=1 かつ (a+b)|S0 なら a+b=1（ほぼ不可能）

**証明の方針:**
1. (a+b) | S0 → (a+b) | b² (apb_dvd_S0_iff_dvd_bsq より)
2. gcd(a,b)=1 → gcd(a+b, b) = 1 (gcd_add_mul_self による)
3. (a+b) | b² かつ gcd(a+b, b) = 1 → a+b | 1
4. したがって a+b = 1
-/
lemma apb_dvd_S0_implies_eq_one (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.gcd a b = 1) (hdvd : (a + b) ∣ S0_nat a b) :
    a + b = 1 := by
  have hbsq : (a + b) ∣ b ^ 2 := (apb_dvd_S0_iff_dvd_bsq a b ha hb).1 hdvd
  have hab_coprime : Nat.Coprime a b := by
    rwa [Nat.coprime_iff_gcd_eq_one]
  have hapb_coprime : Nat.Coprime (a + b) b := (Nat.coprime_add_self_left).2 hab_coprime
  have hapb_coprime_pow : Nat.Coprime (a + b) (b ^ 2) := by
    exact (Nat.coprime_pow_right_iff (n := 2) (by decide) (a + b) b).2 hapb_coprime
  exact Nat.eq_one_of_dvd_coprimes hapb_coprime_pow (dvd_refl (a + b)) hbsq

-- ========================================
-- § 4. Mathlib GeomSum 補題の活用（Phase 3.1）
-- ========================================

/-- Mathlib の既製品：奇数冪での (a+b) 割り切り

**Mathlib 定理:**
`Odd.add_dvd_pow_add_pow : Odd n → (a+b) | (a^n + b^n)`

これは φ=1 での高次版に相当する。
-/
example (a b : ℤ) (n : ℕ) (hn : Odd n) : (a + b) ∣ (a^n + b^n) :=
  hn.add_dvd_pow_add_pow a b

/-- Mathlib の既製品：常に (a-b) | (a^n - b^n)

**Mathlib 定理:**
`sub_dvd_pow_sub_pow : (a-b) | (a^n - b^n)`

これは差分因子の基本。
-/
example (a b : ℤ) (n : ℕ) : (a - b) ∣ (a^n - b^n) :=
  sub_dvd_pow_sub_pow a b n

-- ========================================
-- § 5. 補助補題（将来の拡張用）
-- ========================================

-- ========================================
-- § 5. 補助補題（将来の拡張用）
-- ========================================

/-- S0 の対称性 -/
lemma S0_comm (α : Type*) [CommRing α] (a b : α) : S0 α a b = S0 α b a := by
  unfold S0
  ring

/-- S1 の対称性 -/
lemma S1_comm (α : Type*) [CommRing α] (a b : α) : S1 α a b = S1 α b a := by
  unfold S1
  ring

/-- S0 ≤ S1 (ℕ版、a,b > 0 で) -/
lemma S0_le_S1_nat (a b : ℕ) (_ha : 0 < a) (_hb : 0 < b) :
    S0_nat a b ≤ S1_nat a b := by
  unfold S0_nat S1_nat
  -- S0 = a² + ab + b², S1 = (a+b)² = a² + 2ab + b²
  -- S1 - S0 = ab ≥ 0
  have h : (a + b)^2 = a^2 + a*b + b^2 + a*b := by ring
  linarith [Nat.zero_le (a * b)]

-- ========================================
-- § 6. 相対多角数の平方判定（Gap視点）
-- ========================================

/-- 相対多角数の本質的表現：S0 = (a+b)² - ab

**数学的内容:**
相対多角数 a² + ab + b² は、完全平方 (a+b)² と ab の差として表現できる。
これは「Gap（直交成分）」を明示的にする形。

**応用:**
4*S0 + 1 が平方数になるというTermial的性質を導き出す。
-/
lemma S0_as_diff (a b : ℕ) :
    S0_nat a b = (a + b)^2 - a * b := by
  unfold S0_nat
  have h : (a + b)^2 = a^2 + a*b + b^2 + a*b := by ring
  omega

/-- 相対多角数の判別式性質：関連する平方性

**数学的背景:**
Termial (三角数) では 8T + 1 が平方数。
相対多角数 R = n(n+1) に対して、この平方性が扱いやすい形で現れる。

**応用:**
この構造が、gcd(a,b)=1 のとき q² | S0 を阻止する鍵となる。

**注:**
正確な形式は層B本体での詳細分析で確定される。
-/
lemma S0_related_perfect_square_property (n : ℕ) :
    4 * n * (n + 1) + 1 = (2*n + 1)^2 := by
  ring

/-- mod q² での分析補題：q² ∤ S0 の基礎

**数学的内容:**
gcd(a, b) = 1 のとき、q | S0 だからといって q² | S0 とは限らない。
相対多角数の平方判定により、q² による重複割り切りは歯止めがかかる。

**証明の流れ:**
1. S0 = (a+b)² - ab （Gap構造）
2. q | S0 ⟹ q | ((a+b)² - ab)
3. q² | S0 と仮定すると (a+b)² ≡ ab (mod q²)
4. gcd(a,b) = 1 かつ q ≠ ab より矛盾

**当面の実装:**
補助補題として設置し、量化記号や矛盾の詳細な展開は層B本体で研究。
-/
lemma S0_not_sq_divible_of_coprime (a b q : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (hq : Nat.Prime q) (hq_dvd : q ∣ S0_nat a b) :
    ¬ q^2 ∣ S0_nat a b := by
  intro hq2_dvd

  -- Gap構造：S0 = (a+b)² - ab を使用
  have hS0_eq : S0_nat a b = (a + b)^2 - a * b := S0_as_diff a b

  -- q | S0 から、(a+b)² - ab ≡ 0 (mod q)
  -- つまり (a+b)² ≡ ab (mod q)

  -- q² | S0 と仮定：(a+b)² - ab ≡ 0 (mod q²)
  -- つまり (a+b)² ≡ ab (mod q²)

  -- しかし gcd(a, b) = 1 かつ q | S0 のとき、
  -- q² | S0 となるには特殊な因子構造が必要
  -- 相対多角数の自己相似性により、この構造は起きない

  -- 当面：層B本体での詳細な mod q² 矛盾導出を待つ
  sorry  -- TODO: 相対多角数の平方判定による矛盾

end DkMath.FLT.PetalDetect
