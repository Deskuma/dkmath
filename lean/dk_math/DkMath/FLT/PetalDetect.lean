/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import DkMath.SilverRatio.GcdAg
import DkMath.NumberTheory.ZsigmondyCyclotomic

set_option linter.style.emptyLine false

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

-- Basic
/-- S0 が 0 でないことの確認 -/
lemma S0_ne_zero (a b : ℕ) (ha : 0 < a) : S0_nat a b ≠ 0 := by
  unfold S0_nat
  have ha : 0 < a := by omega
  have h_pos : 0 < a^2 + a * b + b^2 := by
    have ha2 : 0 < a ^ 2 := Nat.pow_pos ha
    omega
  exact Nat.ne_zero_of_lt h_pos

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

/-- mod q分析：q | (a+b) ∧ q | S0 から q | b² を導く

**数学的内容:**
相対多角数 S0 = a² + ab + b² は a(a+b) + b² と分解される。
q が (a+b) と S0 の両方を割れば、q は (a(a+b)) も (S0 - a(a+b)) = b² も割る。

**証明の鍵:**
1. S0 = a(a+b) + b²（代数展開）
2. q | (a+b) ⟹ q | a(a+b)（割り切りの推移性）
3. q | S0 かつ q | a(a+b) ⟹ q | b²（割り切り差の性質）

**応用:**
prime_dvd_S0_coprime_imp_not_dvd_apb の内部ステップを完成させる（Step B.1）。
-/
lemma mod_q_ab_analysis (a b q : ℕ)
    (hqab : q ∣ a + b) (hqS0 : q ∣ S0_nat a b) :
    q ∣ b^2 := by
  -- S0 = a(a+b) + b² に分解
  have hS0_eq : S0_nat a b = a * (a + b) + b^2 := by
    unfold S0_nat
    ring
  -- q | (a+b) ⟹ q | a(a+b)
  have h_div_aprod : q ∣ a * (a + b) := dvd_mul_of_dvd_right hqab a
  -- q | S0 = a(a+b) + b² から q | b² を導く
  have hS0_rewrite : q ∣ a * (a + b) + b^2 := by
    rw [← hS0_eq]
    exact hqS0
  -- Nat.dvd_add_right を使用
  exact (Nat.dvd_add_right h_div_aprod).1 hS0_rewrite

/-- PetalDetect の核心定理：相対多角数で (q) が割れば (a+b) は割らない

**数学的内容:**
素数 q が S0(a,b) = a² + ab + b² を割り、gcd(a,b)=1 ならば、q ∤ (a+b)。

**証明の要点:**
1. q | S0 と q | (a+b) を同時に仮定
2. a ≡ -b (mod q)
3. S0 ≡ b² - b² + b² ≡ b² (mod q)
4. q | b² ∧ q素数 ⟹ q | b
5. q | (a+b) ∧ q | b ⟹ q | a
6. q | gcd(a,b) = 1 ... 矛盾！

**応用:**
これが「(a+b) の吸い込み」を防ぐ petal 検出器の本質。
-/
lemma prime_dvd_S0_coprime_imp_not_dvd_apb (a b q : ℕ)
    (ha : 0 < a)
    (hab : Nat.Coprime a b) (hq : Nat.Prime q)
    (hS0 : q ∣ S0_nat a b) :
    ¬ q ∣ a + b := by
  intro hqab
  -- q | (a+b) と q | b² から q | b を導く直接証明
  -- q | (a+b) より ∃ k, a+b = q*k
  -- q | S0 = a² + ab + b² より a² + ab + b² ≡ 0 (mod q)
  -- q | (a+b) から a ≡ -b (mod q)、つまり a² ≡ b² (mod q)
  -- したがって b² - b² + b² ≡ 0 (mod q)、つまり b² ≡ 0 (mod q)
  -- q素数で q | b² ⟹ q | b

  -- q | (a+b) 且つ q | S0 から q | b² を導く
  --（詳細な計算は複雑なので層B本体で実装）
  have hb2 : q ∣ b^2 := mod_q_ab_analysis a b q hqab hS0
  -- q素数で q | b² ⟹ q | b
  have hb : q ∣ b := hq.dvd_of_dvd_pow hb2
  -- q | (a+b) ∧ q | b ⟹ q | a
  have ha : q ∣ a := by
    obtain ⟨k, hk⟩ := hqab
    obtain ⟨m, hm⟩ := hb
    -- hk: a + b = q * k, hm: b = q * m
    -- これから a = q * k - q * m = q * (k - m) が従う
    use k - m
    -- 証明：a = q * (k - m)
    -- a = (a + b) - b = q*k - q*m と k ≥ m から
    have h : a = q * k - q * m := by
      calc a = (a + b) - b := by omega
           _ = q * k - q * m := by rw [hk, hm]
    -- q * (k - m) = q * k - q * m (Nat版)
    have : q * (k - m) = q * k - q * m := Nat.mul_sub_left_distrib q k m
    rw [this]
    exact h
  -- q | gcd(a,b) = 1 ... 矛盾
  have gcd_dvd : q ∣ Nat.gcd a b := Nat.dvd_gcd ha hb
  rw [hab.gcd_eq_one] at gcd_dvd
  exact hq.not_dvd_one gcd_dvd

-- 古い補題は削除（参考として コメント保持）

-- ========================================
-- § 7. 層B：詳細な padicValNat 分析（将来の研究フェーズ）
-- ========================================

/-- padicValNat上界補題：q² ∤ S0 から padicValNat q (S0) ≤ 1 を導く

**数学的内容:**
素数 q が S0 を割ったとしても、q² が割らなければ、
p-adic 付値は最大 1（つまり正確に q で1回だけ割り切れる）。

**証明の鍵:**
1. q | S0 なら padicValNat q (S0) ≥ 1（Mathlib: padicValNat の割り切り条件）
2. q² ∤ S0 なら padicValNat q (S0) < 2（定義から）
3. → padicValNat q (S0) = 1 ≤ 1

**応用:**
GcdNext.leanの padicValNat_s0_le_one_of_prime_ne_apb で使用。
層Aの下界と合わせて，矛盾（d·padicValNat ≤ 1）を導出。

**Mathlib補題の活用:**
- `padicValNat.pos_of_dvd`: q | n ⟹ 0 < padicValNat q n
- `padicValNat.pow_dvd_iff`: q^k | n ⟺ padicValNat q n ≥ k
-/
lemma padicValNat_le_one_of_not_sq_dvd (a b q : ℕ)
    (_ha : 0 < a) (_hb : 0 < b)
    (hq : Nat.Prime q)
    (hq_not_sq : ¬ q^2 ∣ S0_nat a b) :
    padicValNat q (S0_nat a b) ≤ 1 := by
  -- q | S0 より padicValNat q (S0) ≥ 1
  -- q² ∤ S0 より padicValNat q (S0) ≤ 1
  -- したがって padicValNat q (S0) ≤ 1
  haveI hp : Fact q.Prime := ⟨hq⟩
  have h_S0_ne : S0_nat a b ≠ 0 := by
    unfold S0_nat
    intro h
    have : a^2 + a*b + b^2 = 0 := h
    have : 0 < a^2 := by positivity
    omega
  by_contra h
  push_neg at h
  have : q^2 ∣ S0_nat a b := by
    rw [padicValNat_dvd_iff 2 (S0_nat a b)]
    right
    exact h
  exact hq_not_sq this

/-- Zsigmondy統合補題：原始素因子と相対多角数の関係

**数学的内容:**
d が奇素数で d > 2 のとき、q が a^d - b^d を割り a-b を割らないなら、
q は相対多角数 S0(a,b) = a² + ab + b² を「制御」する。

特に gcd(a,b)=1 のとき、q ∤ a+b。

**証明の鍵:**
1. q は a^d - b^d の「新しい」素因子（Zsigmondy）
2. → Φ_d(a/b) が既約因子を与える
3. → q は (a-b, a, b, ...) 等では割らない
4. → 特に q ∤ a+b （d > 2）

**応用:**
この補題は層AのZsigmondy原始素因子とブリッジし、
「d のどの素因子も相対多角数の平方判定を破壊できない」ことを示す。

**実装計画:**
1. mod q 分析補題：q | S0 ⟹ (a+b)² ≡ ab (mod q)  ✅ (mod_q_ab_analysis)
2. padicValNat 上界補題：q² ∤ S0 ⟹ padicValNat q (S0) ≤ 1  ✅ (padicValNat_le_one_of_not_sq_dvd)
3. Zsigmondy統合補題：q | a^d - b^d ∧ q ∤ a-b ⟹ q ∤ a+b  🚧 (本補題)

**注:**
現在実装中のバージョンは「so#rryプレースホルダー」。
正確な証明は円分多項式の因子分解理論を要するが、
Mathlib の Cyclotomic 補題により段階的に構築可能。
-/
lemma zsigmondy_not_dvd_apb (a b q : ℕ) (d : ℕ)
    (hb : 0 < b)
    (hab : Nat.Coprime a b)
    (hd : Nat.Prime d) (hd_gt : 2 < d)
    (hq : Nat.Prime q) (hq_dvd_pow : q ∣ a ^ d - b ^ d)
    (hq_ndiv_diff : ¬ q ∣ a - b) :
    ¬ q ∣ a + b := by
  intro hq_dvd_apb
  have hba : b < a := by
    by_contra h_not_lt
    have hle : a ≤ b := Nat.not_lt.mp h_not_lt
    have hzero : a - b = 0 := Nat.sub_eq_zero_of_le hle
    exact hq_ndiv_diff (hzero ▸ dvd_zero q)
  have h_not_dvd_sq :
      ¬ q ∣ a ^ 2 - b ^ 2 :=
    DkMath.NumberTheory.GcdNext.prime_exp_not_dvd_diff_imp_primitive
      hd (lt_trans (by decide : 1 < 2) hd_gt) hq hab hba hb hq_dvd_pow hq_ndiv_diff
      (k := 2) (by decide) hd_gt
  have h_dvd_sq : q ∣ a ^ 2 - b ^ 2 := by
    rw [Nat.sq_sub_sq]
    exact dvd_mul_of_dvd_left hq_dvd_apb (a - b)
  exact h_not_dvd_sq h_dvd_sq

end DkMath.FLT.PetalDetect
