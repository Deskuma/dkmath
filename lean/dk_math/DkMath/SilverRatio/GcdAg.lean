/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

/-!
# GCD-Ag 位相：2進ノイズを除去する射影 π_Ag と gcd_Ag

## 概要

FLT の B層（付値評価層）において、「2のせいで互いに素が言えない」問題を解決するため、
**Ag位相**（半位相）による正規化を導入する。

## 数学的背景

### 問題：偶数の連続では gcd≠1
通常の gcd では：
```
gcd(2n, 2n+2) = gcd(2n, 2) = 2
```
したがって「互いに素」とは言えない。

### 解決：Ag射影 π_Ag
2進位相を1段階落とす射影：
```
π_Ag(n) := n / 2  (整数除算)
```

これにより：
```
π_Ag(2n) = n
π_Ag(2n+1) = n
```

### Ag-正規化 gcd
```
gcd_Ag(a, b) := gcd(π_Ag(a), π_Ag(b))
```

これにより：
```
gcd_Ag(2n, 2n+2) = gcd(n, n+1) = 1
```

## 主要定理（Phase 1）

1. **Ag射影の基本性質**
   - `π_Ag_even : π_Ag(2k) = k`
   - `π_Ag_odd : π_Ag(2k+1) = k`

2. **Ag-gcd の位相不変性**
   - `gcd_Ag a (2k) = gcd_Ag a (2k+1)`

3. **メイン観測**
   - `gcd_even_add_two_eq_two : gcd(2n, 2n+2) = 2`
   - `gcdAg_even_add_two_eq_one : gcd_Ag(2n, 2n+2) = 1`

## 実装計画

### Phase 1（このファイル）
- Ag射影 π_Ag の定義
- gcd_Ag の定義
- 基本補題の証明

### Phase 2（別ファイルまたは拡張）
- φビット構造 S_φ との連携
- (a+b) 検出器への応用

## 参照
- GcdAg_ImplementsPlan.md
- GcdAg_DevelopNote.md
-/

set_option linter.style.emptyLine true
set_option linter.unusedTactic false

namespace DkMath.SilverRatio.GcdAg

-- ========================================
-- § 1. Ag射影の定義
-- ========================================

/-- Ag射影：2進位相を1段階落とす

**数学的意味:**
π_Ag(n) = ⌊n/2⌋

これにより、偶数と奇数の「半位相」を取得できる：
- π_Ag(2k) = k
- π_Ag(2k+1) = k
-/
def π_Ag (n : ℕ) : ℕ := n / 2

/-- Ag-正規化 gcd

**数学的意味:**
gcd_Ag(a, b) := gcd(π_Ag(a), π_Ag(b))

これにより、2進ノイズを除去した「本質的な」互いに素性を評価できる。
-/
def gcd_Ag (a b : ℕ) : ℕ := Nat.gcd (π_Ag a) (π_Ag b)

-- ========================================
-- § 2. Ag射影の基本性質（Phase 1.2）
-- ========================================

/-- Ag射影の偶数での振る舞い -/
lemma π_Ag_even (k : ℕ) : π_Ag (2 * k) = k := by
  unfold π_Ag
  simp [Nat.mul_div_cancel_left k (by omega : 0 < 2)]

/-- Ag射影の奇数での振る舞い -/
lemma π_Ag_odd (k : ℕ) : π_Ag (2 * k + 1) = k := by
  unfold π_Ag
  simp [Nat.add_div_of_dvd_right (by omega : 2 ∣ 2 * k)]

/-- Ag-gcd の位相不変性：偶奇を区別しない -/
lemma gcd_Ag_even_odd_eq (a k : ℕ) : gcd_Ag a (2 * k) = gcd_Ag a (2 * k + 1) := by
  unfold gcd_Ag
  rw [π_Ag_even, π_Ag_odd]

-- ========================================
-- § 3. メイン観測：偶数連続の gcd 評価（Phase 1.2）
-- ========================================

/-- 偶数と次の偶数の gcd は 2 -/
lemma gcd_even_add_two_eq_two (n : ℕ) : Nat.gcd (2 * n) (2 * n + 2) = 2 := by
  have hg2 : Nat.gcd (2 * n) (2 * n + 2) ∣ 2 := by
    have h :=
      Nat.dvd_sub
        (Nat.gcd_dvd_right (2 * n) (2 * n + 2))
        (Nat.gcd_dvd_left (2 * n) (2 * n + 2))
    have hsub : (2 * n + 2) - (2 * n) = 2 := by omega
    rw [hsub] at h
    exact h
  have h2n : 2 ∣ 2 * n := by
    exact dvd_mul_of_dvd_left (dvd_refl 2) n
  have h2n2 : 2 ∣ 2 * n + 2 := by
    exact Nat.dvd_add h2n (dvd_refl 2)
  have h2g : 2 ∣ Nat.gcd (2 * n) (2 * n + 2) := by
    exact Nat.dvd_gcd h2n h2n2
  exact Nat.dvd_antisymm hg2 h2g

/-- Ag-gcd では偶数連続が互いに素 -/
lemma gcdAg_even_add_two_eq_one (n : ℕ) : gcd_Ag (2 * n) (2 * n + 2) = 1 := by
  unfold gcd_Ag
  have hstep : 2 * n + 2 = 2 * (n + 1) := by omega
  rw [π_Ag_even, hstep, π_Ag_even]
  have hg1 : Nat.gcd n (n + 1) ∣ 1 := by
    have h :=
      Nat.dvd_sub
        (Nat.gcd_dvd_right n (n + 1))
        (Nat.gcd_dvd_left n (n + 1))
    have hsub : (n + 1) - n = 1 := by omega
    rw [hsub] at h
    exact h
  have hg2 : 1 ∣ Nat.gcd n (n + 1) := by
    exact Nat.one_dvd (Nat.gcd n (n + 1))
  exact Nat.dvd_antisymm hg1 hg2

-- ========================================
-- § 4. 補助補題（将来の拡張用）
-- ========================================

/-- Ag射影の単調性 -/
lemma π_Ag_le_self (n : ℕ) : π_Ag n ≤ n := by
  unfold π_Ag
  exact Nat.div_le_self n 2

/-- Ag射影の2倍で元に戻る（偶数の場合） -/
lemma two_mul_π_Ag_even (k : ℕ) : 2 * π_Ag (2 * k) = 2 * k := by
  rw [π_Ag_even]

/-- gcd_Ag の対称性 -/
lemma gcd_Ag_comm (a b : ℕ) : gcd_Ag a b = gcd_Ag b a := by
  unfold gcd_Ag
  exact Nat.gcd_comm (π_Ag a) (π_Ag b)

/-- Ag射影が正の場合、gcd_Ag は元の引数の最小値を超えない -/
lemma gcd_Ag_le_min (a b : ℕ) (ha : 0 < π_Ag a) (hb : 0 < π_Ag b) :
    gcd_Ag a b ≤ Nat.min a b := by
  unfold gcd_Ag
  have hleft : Nat.gcd (π_Ag a) (π_Ag b) ≤ a := by
    exact le_trans (Nat.gcd_le_left (π_Ag b) ha) (π_Ag_le_self a)
  have hright : Nat.gcd (π_Ag a) (π_Ag b) ≤ b := by
    exact le_trans (Nat.gcd_le_right (π_Ag a) hb) (π_Ag_le_self b)
  exact (Nat.le_min).2 ⟨hleft, hright⟩

end DkMath.SilverRatio.GcdAg
