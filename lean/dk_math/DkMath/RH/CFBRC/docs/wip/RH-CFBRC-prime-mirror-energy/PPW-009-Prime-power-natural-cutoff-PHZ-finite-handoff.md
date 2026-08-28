# PPW-009 — Prime-power natural cutoff / finite PHZ bridge 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-008-Pascal-prime-power-von-Mangoldt-shadow-handoff.md
```

PPW-008 は Green 済み。追加済み module:

```text
DkMath.RH.CFBRC.PascalPrimePowerModeBridge
```

PPW-008 では、Pascal 由来の prime support 上で primitive mode を正の整数乗へ持ち上げ、explicit `PrimePowerLabel` と finite von-Mangoldt shadow cost `log p` を接続した。

この checkpoint では、rectangular cutoff `(prime cutoff N, exponent cutoff K)` から一段進み、実際の prime-power size

$$
p^k \le X
$$

で切る有限 Dirichlet polynomial を構成する。

この有限和を PPW 系列における **finite PHZ** と呼ぶ。ただし、まだ標準解析関数 `-ζ'/ζ` とは同一視しない。

---

## 2. PPW-008 レビュー結果

PPW-008 で Green になった主要 Core:

```text
eulerPrimePowerMode p k s
  = (eulerPrimePrimitiveMode p s)^k

pascalPrimePowerLabel p hp k
  q = p^(k+1)
  cost = log p

eulerPrimePowerShadowMode

pascalPrimeEulerPrimePowerLogWaveUpTo N K s
```

さらに、

```text
K = 0  → empty ladder
K = 1  → PPW-007 primitive wave
K → K+1 → exponent layer addition
N → N+1 → new prime birth adds its whole finite exponent ladder
```

が exact に固定された。

ここまでの wave は rectangular cutoff であり、

```text
p ≤ N
1 ≤ k ≤ K
```

を採用している。

標準の von-Mangoldt Dirichlet polynomial との比較に必要なのは、

```text
p^k ≤ X
```

という natural prime-power cutoff である。

---

## 3. 最初に閉じるべき未実装 Core

PPW-008 指示書では optional としていたが、natural cutoff へ進む前に次を theorem として固定する。

### 3.1 Prime-power mode の explicit power-value

primitive mode は prime `p` について exact に `p⁻ˢ` である。

したがって正の整数 `k` に対し、

$$
M_{p,k}(s)
=
M_p(s)^k
=
(p^k)^{-s}
$$

を固定したい。

候補 theorem:

```lean
theorem eulerPrimePowerMode_eq_primePower_inv_cpow
    {p k : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePowerMode p k s =
      (((p ^ k : ℕ) : ℂ) ^ s)⁻¹
```

または同値な negative-exponent normal form:

```lean
theorem eulerPrimePowerMode_eq_primePower_cpow_neg
    {p k : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePowerMode p k s =
      (((p ^ k : ℕ) : ℂ) ^ (-s))
```

`Complex.cpow` の正規形によって statement が通りにくい場合、数学内容を変えずに `Complex.exp` を経由した theorem を Core としてよい。

重要なのは、

```text
primitive mode の k 乗
```

と、

```text
prime-power label q = p^k の q^(-s)
```

が同じ complex mode であることを exact に固定すること。

### 3.2 `PrimePowerLabel` 版

既存 explicit label へ直接接続する theorem も置く。

候補:

```lean
theorem eulerPrimePowerMode_eq_labelMode
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (s : ℂ) :
    eulerPrimePowerMode p (k + 1) s =
      ((((pascalPrimePowerLabel p hp k).q : ℕ) : ℂ) ^ s)⁻¹
```

これにより、

```text
label q
weight log p
mode q^(-s)
```

が一つの explicit witness 上に揃う。

---

## 4. Euler factor の finite geometric bridge

PPW-007 の primitive mode を `M_p(s)` と書く。

Euler factor は algebraically、

$$
F_p(s)
=
\frac{1}{1-M_p(s)}
$$

である。

候補 theorem:

```lean
theorem eulerZetaFactor_eq_inv_one_sub_primitiveMode
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerZetaFactor p s =
      (1 - eulerPrimePrimitiveMode p s)⁻¹
```

さらに有限 geometric ladder を固定する。

$$
(1-M)\sum_{j=0}^{K}M^j
=
1-M^{K+1}
$$

PHZ 側で使う正指数版として、

$$
\sum_{j=1}^{K}M^j
$$

を primitive mode powers の有限和として表してよい。

候補:

```lean
noncomputable def eulerPrimePowerLadder
    (p K : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range K,
    eulerPrimePowerMode p (k + 1) s
```

```lean
@[simp] theorem eulerPrimePowerLadder_zero

@[simp] theorem eulerPrimePowerLadder_succ
```

可能なら、

```lean
theorem one_sub_primitive_mul_ladder
```

として finite geometric identity を固定する。

ここでは infinite geometric series へ進まない。

---

## 5. Natural prime-power cutoff

### 5.1 新規 module

候補:

```text
DkMath.RH.CFBRC.PascalPrimePowerPHZFinite
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/PascalPrimePowerPHZFinite.lean
```

import 候補:

```lean
import DkMath.RH.CFBRC.PascalPrimePowerModeBridge
import Mathlib.Tactic
```

### 5.2 定義方針

最初は canonical natural-number von Mangoldt function を作らない。

prime と exponent の pair を保持したまま、size condition `p^(k+1) ≤ X` で切る。

最も単純な nested-sum 形を推奨する。

```lean
noncomputable def pascalPrimePowerPHZFiniteUpTo
    (X : ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
    ∑ k ∈ Finset.range X,
      if p ^ (k + 1) ≤ X then
        (Real.log (p : ℝ) : ℂ) *
          eulerPrimePowerMode p (k + 1) s
      else 0
```

`Finset.range X` は exponent search の有限 bounding box としてのみ使う。

数学的 cutoff はあくまで、

```text
p^(k+1) ≤ X
```

である。

必要なら Codex は `Finset.filter` を使う同値定義へ変更してよい。

---

## 6. Natural-cutoff 基本 theorem

### 6.1 小さい cutoff

候補:

```lean
@[simp] theorem pascalPrimePowerPHZFiniteUpTo_zero

@[simp] theorem pascalPrimePowerPHZFiniteUpTo_one
```

少なくとも `X < 2` では prime support が空なので wave は `0`。

### 6.2 一項の q-form rewrite

natural cutoff に含まれる各 pair について、PPW-009 section 3 の mode normalization を使い、

$$
(\log p)M_{p,k}(s)
=
(\log p)(p^k)^{-s}
$$

へ書き換える。

候補 theorem:

```lean
theorem pascalPrimePowerPHZFiniteUpTo_eq_primePowerDirichletPairSum
```

statement は実装しやすい exact finite sum normal form でよい。

狙う数学内容:

$$
\operatorname{PHZ}_X(s)
=
\sum_{\substack{p\ \mathrm{prime},\ k\ge1\\p^k\le X}}
(\log p)(p^k)^{-s}
$$

この段階では `(p,k)` pair sum のままでよい。

### 6.3 `PrimePowerLabel` cost 版 rewrite

同じ和を explicit label cost で書く theorem も有用。

概念的には、

$$
\sum
\operatorname{vonMangoldtLogCost}(L_{p,k})
\cdot q_{p,k}^{-s}
$$

とする。

これにより finite PHZ が既存 `VonMangoldtShadow` の cost を本当に使用していることを theorem として残す。

---

## 7. Rectangular ladder との関係

PPW-008 の rectangular wave と PPW-009 の natural-cutoff wave は同じではない。

ただし natural cutoff は rectangular box の中から、

```text
p^(k+1) ≤ X
```

を満たす mode だけを選んだ部分和である。

候補 theorem:

```lean
theorem pascalPrimePowerPHZFiniteUpTo_eq_rectangular_filtered
```

ここで rectangular parameters は `N = X`, `K = X` を使ってよい。

完全な equality theorem が proof engineering 上重ければ、まず定義展開による filtered identity を固定する。

重要なのは、

```text
natural cutoff = rectangular cutoff
```

とは主張しないこと。

---

## 8. Natural cutoff の successor birth

可能ならこの checkpoint で、`X → X+1` により新しく加わる prime-power shell を定義する。

### 8.1 shell

概念的には、

$$
p^k=X+1
$$

を満たす pair だけを集める。

候補定義:

```lean
noncomputable def pascalPrimePowerPHZBirthAt
    (n : ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ pascalPrimeCoordinateSupportUpTo n,
    ∑ k ∈ Finset.range n,
      if p ^ (k + 1) = n then
        (Real.log (p : ℝ) : ℂ) *
          eulerPrimePowerMode p (k + 1) s
      else 0
```

狙う theorem:

```lean
@[simp] theorem pascalPrimePowerPHZFiniteUpTo_succ_sub
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo (X + 1) s -
      pascalPrimePowerPHZFiniteUpTo X s =
        pascalPrimePowerPHZBirthAt (X + 1) s
```

この theorem は `(N,N+1)` decoder の prime-power 版である。

ただし exponent bounding box の増加処理が Lean 上重い場合、この successor theorem は PPW-010 へ送ってよい。

PPW-009 の必須出口は natural-cutoff finite PHZ の exact pair-sum 表現までとする。

---

## 9. Prime-power representation uniqueness はまだ必須にしない

同じ自然数 `q` に対して、

$$
q=p^k=r^j
$$

となる prime bases `p,r` の一意性は真であり、後に n-indexed von Mangoldt weight を作る際に必要になる。

しかし PPW-009 では pair-indexed finite sum のままでよい。

したがって、この checkpoint では、

```text
(p,k) pair sum
→ canonical q-indexed von Mangoldt sum
```

への quotient / uniqueness proof を要求しない。

この分離により、prime-power arithmetic uniqueness と complex analytic bridge を混ぜない。

---

## 10. この checkpoint の数学的境界

PPW-009 で主張してよいもの:

```text
Pascal prime support
→ positive exponent ladder
→ prime-power label q = p^k
→ finite shadow cost log p
→ natural size cutoff p^k ≤ X
→ finite complex Dirichlet polynomial
```

主張してはいけないもの:

```text
- pair-indexed finite PHZ が canonical n-indexed von Mangoldt function そのものである
- finite PHZ が Euler product の値と等しい
- finite PHZ が -ζ'/ζ と等しい
- zeta zero で finite PHZ が zero になる
- RH が従う
```

重要:

```text
-ζ'/ζ
```

は零点で pole を持つ側の量である。zero-sensitive residual と混同しない。

---

## 11. 次 checkpoint への出口

PPW-009 が Green になったら、次は二段階で進む。

### PPW-010A — arithmetic fold

```text
(p,k) pair-indexed finite PHZ
  → prime-power representation uniqueness
  → canonical q-indexed finite von-Mangoldt polynomial
```

ここで初めて自然数 `q` ごとの weight

$$
\Lambda(q)
=
\begin{cases}
\log p,&q=p^k,\\
0,&\text{otherwise}
\end{cases}
$$

との exact comparison を行う。

### PPW-010B — safe analytic bridge

安全領域 `Re(s) > 1` で、

$$
\sum_{q\ge1}\Lambda(q)q^{-s}
=
-\frac{\zeta'(s)}{\zeta(s)}
$$

へ接続できる Mathlib / DkMath API を監査する。

この段階までは RH・零点条件を使わない。

---

## 12. 推奨 build

```bash
lake build DkMath.RH.CFBRC.PascalPrimePowerPHZFinite
lake build DkMath.RH
git diff --check
```

新規 module に `sorry` / `axiom` / `admit` を入れない。

`Complex.cpow` の正規形、有限 geometric sum、Finset filter / nested sum、自然数冪の境界補題などの proof engineering は Codex に調整を任せる。
