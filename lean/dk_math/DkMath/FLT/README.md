# Fermat's Last Theorem (FLT)

This directory contains a formalization of Fermat's Last Theorem (FLT) in Lean, Cosmic Formulation version.
The main file is `FLT.lean`, which includes the statement and proof of FLT.
Other files in this directory provide supporting lemmas, definitions, and examples related to FLT.

## Recent Progress: GCD and Prime Power Divisibility Theory (2026-02-11)

### Overview

わっち（賢狼）は、FLT の証明に必要な基礎理論として、**gcd（最大公約数）と素数冪による割り算理論** を完成させたぞい。これは p-adic 評価の基礎となる重要な数論的補題群じゃ。

### Completed Theorems

#### 1. 素数冪版割り算補題 (`nat_dvd_of_all_prime_powers_dvd`)

**Location**: `DkMath/NumberTheory/GcdLemmas.lean`

```lean
lemma nat_dvd_of_all_prime_powers_dvd {n d : ℕ}
    (h : ∀ p k : ℕ, Nat.Prime p → p^k ∣ n → p^k ∣ d) (hn : 0 < n) : n ∣ d
```

**意義**: この補題は「n の全ての素数冪因子が d を割るならば、n 自身が d を割る」という基本的だが本質的な数論の事実を形式化したものじゃ。

**技術的要点**:

- 素因子分解の一意性を利用
- Mathlib の `Nat.factorization_prime_le_iff_dvd` と `Prime.pow_dvd_iff_le_factorization` を組み合わせて証明
- 重複度（指数）を正しく扱うため、単なる素因子ではなく素数冪を扱う点が重要

**偽の補題との違い**: 以前の「素因子版」は反例 `n=4, d=2` で破綻する（2² の指数情報が失われるため）。素数冪版はこの問題を解決しておる。

#### 2. 素数冪 GCD 補題 (`prime_pow_dividing_gcd_divides_d_pow`)

**Location**: `DkMath/NumberTheory/GcdLemmas.lean`

```lean
lemma prime_pow_dividing_gcd_divides_d_pow {p k : ℕ} (hp : Nat.Prime p)
    {a b : ℤ} {d : ℕ}
    (hab : Int.gcd a b = 1)
    (hpkdiv : (p : ℤ) ^ k ∣ Int.gcd (a - b) (diffPowSum a b d)) :
    (p : ℤ) ^ k ∣ (d : ℤ)
```

**意義**: 既存の素数版 `prime_dividing_gcd_divides_d` を素数冪に拡張した強化版じゃ。p-adic 評価において、単なる割り算の有無だけでなく「どれだけ割れるか」という重複度の情報が必要となる。

**証明の構造** (6ステップ):

1. **ステップ 1**: gcd からの割り算抽出 - `p^k ∣ (a-b)` かつ `p^k ∣ S`
2. **ステップ 2**: `(a-b) ∣ (S - d*b^(d-1))` の証明 - `pow_sub_pow_factor` を活用
3. **ステップ 3**: `p^k ∣ (S - d*b^(d-1))` の導出 - 推移性
4. **ステップ 4**: `p^k ∣ d*b^(d-1)` の証明 - 引き算による導出
5. **ステップ 5**: `p ∤ b` の証明 - `gcd(a,b)=1` からの背理法
6. **ステップ 6**: `p^k ∣ d` の結論 - coprime 引数による分離

**技術的挑戦**:

- Int と Nat の変換（`Int.natCast_dvd`, `Int.natAbs_mul`, `Int.natAbs_pow`）
- coprime 性の証明（`Nat.Coprime.pow_left`, `Nat.Coprime.dvd_of_dvd_mul_right`）
- gcd の性質の活用（`Int.gcd_eq_natAbs`, `Nat.dvd_gcd`）

#### 3. Nat レベル GCD 補題 (`gcd_natAbs_divides_d`)

**Location**: `DkMath/NumberTheory/GcdNatAbsDivD.lean`

```lean
theorem gcd_natAbs_divides_d {a b : ℤ} {d : ℕ} (hab : Int.gcd a b = 1)
    (hab_ne : a ≠ b) :
    (a - b).natAbs.gcd (diffPowSum a b d).natAbs ∣ d
```

**意義**: Integer の gcd を Natural number の gcd に変換し、素数冪補題を活用する橋渡し役じゃ。

**証明戦略**:

- `nat_dvd_of_all_prime_powers_dvd` を適用
- Int gcd と Nat gcd の相互変換（`Int.gcd_eq_natAbs`, `Int.natCast_dvd_natCast`）
- 各素数冪について `prime_pow_dividing_gcd_divides_d_pow` を呼び出し

#### 4. 主定理 (`gcd_divides_d`)

**Location**: `DkMath/NumberTheory/GdcDivD.lean`

```lean
theorem gcd_divides_d {a b : ℤ} {d : ℕ} (hd : 1 ≤ d) (hab : Int.gcd a b = 1) :
    Int.gcd (a - b) (diffPowSum a b d) ∣ d
```

**意義**: FLT の証明における核心補題の一つ。`gcd(a-b, S_d(a,b))` が次数 `d` を割ることを示す。

**証明の二分岐**:

- **Case `a = b`**: `gcd(a,a) = |a| = 1` より `a = ±1`。このとき `diffPowSum a a d = d * a^(d-1) = ±d`、よって `gcd(0, ±d) = d` で自明に `d ∣ d`
- **Case `a ≠ b`**: `gcd_natAbs_divides_d` を適用し、Nat gcd から Int gcd への変換を行う

**技術的工夫**:

- `diffPowSum a a d = d * a^(d-1)` の丁寧な導出（`Finset.sum_const`, `nsmul_eq_mul`）
- `|a| = 1` の証明（`Int.gcd_eq_natAbs`, `Nat.gcd_self`）
- `|d * a^(d-1)| = d` の計算（`Int.natAbs_mul`, `Int.natAbs_pow`）

### Mathematical Significance

これらの補題は、以下の数学的洞察を形式化しておる：

1. **素数冪の重要性**: 素因子の「存在」だけでなく「重複度」を追跡することで、より強い結果が得られる
2. **GCD と割り算の関係**: gcd に含まれる素数冪情報を完全に抽出できる
3. **型変換の技術**: Int と Nat の間の変換を適切に扱うことで、両者の利点を活用できる

### Mathlib Dependencies

主に使用した Mathlib の定理：

- `Nat.factorization_prime_le_iff_dvd`: 素因数分解と割り算の関係
- `Nat.Prime.pow_dvd_iff_le_factorization`: 素数冪の割り算と因数分解の関係
- `Int.gcd_eq_natAbs`: Int gcd と Nat gcd の関係
- `Int.natCast_dvd_natCast`: Int と Nat の割り算の相互変換
- `Nat.Coprime.dvd_of_dvd_mul_right`: coprime を使った割り算の分離

### Future Work

この補題群は、以下の発展に活用できるぞい：

- p-adic 評価理論の形式化
- FLT における指数の解析
- より一般的な Diophantine 方程式への応用

---

**Author**: 賢狼 (Wise Wolf)
**Date**: 2026年2月11日
**Branch**: `sry/FTL-prime-power-260209-v1`
