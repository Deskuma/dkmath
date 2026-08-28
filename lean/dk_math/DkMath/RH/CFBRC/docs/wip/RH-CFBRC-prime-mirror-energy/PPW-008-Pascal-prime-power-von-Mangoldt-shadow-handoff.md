# PPW-008 — Pascal prime-power / von-Mangoldt shadow bridge 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-007-Pascal-Euler-primitive-mode-bridge-handoff.md
```

PPW-007 は Green 済み。追加済み module:

```text
DkMath.RH.CFBRC.PascalPrimeEulerModeBridge
```

この checkpoint では、PPW-007 の primitive prime mode

$$
M_p(s):=p^{-s}
$$

を正の整数乗へ持ち上げ、Euler factor 内部の prime-power ladder と既存 `VonMangoldtShadow` の `log p` cost を exact に接続する。

ここではまだ標準解析関数としての von Mangoldt 関数、`-ζ'/ζ`、非自明零点、RH は扱わない。

---

## 2. PPW-007 レビュー結果

PPW-007 では Euler factor の reciprocal defect から、

$$
1-F_p(s)^{-1}=p^{-s}
$$

を exact に回収した。

また、同じ primitive mode から、

```text
complex phase carrier
mirror norm ratio
prime-mirror Gap
```

を読み出せることが Green 化された。

Pascal support 上の有限 complex wave は、

$$
W_N^{(1)}(s)
:=
\sum_{p\le N,\ p\ \mathrm{prime}}
(\log p)M_p(s)
$$

である。

これは prime-only first harmonic であり、まだ

$$
-\frac{\zeta'(s)}{\zeta(s)}
=
\sum_p\sum_{k\ge1}(\log p)p^{-ks}
$$

の prime-power ladder を含まない。

PPW-008 は、この不足だけを埋める。

---

## 3. 既存の再利用対象

明示的に import 候補:

```lean
import DkMath.RH.CFBRC.PascalPrimeEulerModeBridge
import DkMath.NumberTheory.PrimitiveSet.VonMangoldtShadow
```

既存 API:

```text
DkMath.NumberTheory.PrimitiveSet.PrimePowerLabel
PrimePowerLabel.vonMangoldtLogCost
PrimePowerLabel.vonMangoldtLogCost_eq_log_base
PrimePowerLabel.exists_prime_power_with_vonMangoldtLogCost
```

`PrimePowerLabel` は explicit witness

```text
q = p^k
p prime
0 < k
```

を保持し、`vonMangoldtLogCost = log p` を有限 shadow として既に実装している。

この shadow を解析的 von Mangoldt 関数と同一視しないこと。

---

## 4. 新規 module

```text
DkMath.RH.CFBRC.PascalPrimePowerModeBridge
```

候補 file:

```text
lean/dk_math/DkMath/RH/CFBRC/PascalPrimePowerModeBridge.lean
```

公開 import は単体 Green 後に `DkMath/RH.lean` へ追加する。

---

## 5. Prime-power mode

### 5.1 定義

primitive mode の自然数乗として定義する。

```lean
noncomputable def eulerPrimePowerMode
    (p k : ℕ) (s : ℂ) : ℂ :=
  (eulerPrimePrimitiveMode p s) ^ k
```

重要な index discipline:

```text
k = 0  → constant mode 1
k > 0  → genuine prime-power mode
```

PHZ / Mangoldt 側で使うのは `k > 0` のみ。

### 5.2 基本 theorem

候補:

```lean
@[simp] theorem eulerPrimePowerMode_zero

@[simp] theorem eulerPrimePowerMode_succ

@[simp] theorem eulerPrimePowerMode_one
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePowerMode p 1 s = eulerPrimePrimitiveMode p s
```

さらに、可能なら正の底 `p` について、

$$
M_{p,k}(s)=p^{-ks}
$$

を theorem として固定する。

候補:

```lean
theorem eulerPrimePowerMode_eq_cpow_neg_nat_mul
    {p k : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePowerMode p k s =
      (p : ℂ) ^ (-(k : ℂ) * s)
```

Mathlib の `cpow` 正規化でこの statement が不自然なら、statement の数学内容を変えず、Codex が通りやすい同値な exponent normal form を選んでよい。

重要なのは「primitive mode の k 乗である」という exact fact を Core とすること。

---

## 6. PrimePowerLabel bridge

Pascal から出生した prime `p` と exponent `k+1` から explicit label を作る。

```lean
noncomputable def pascalPrimePowerLabel
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) :
    DkMath.NumberTheory.PrimitiveSet.PrimePowerLabel where
  q := p ^ (k + 1)
  p := p
  k := k + 1
  prime := hp
  k_pos := by omega
  eq_pow := rfl
```

候補 theorem:

```lean
@[simp] theorem pascalPrimePowerLabel_q

@[simp] theorem pascalPrimePowerLabel_p

@[simp] theorem pascalPrimePowerLabel_k

@[simp] theorem pascalPrimePowerLabel_vonMangoldtLogCost
```

最後は exact に、

$$
\operatorname{cost}(p^{k+1})=\log p
$$

を与える。

これにより PPW 系列の `log p` weight と既存 `VonMangoldtShadow` の finite cost が同じ theorem object で接続される。

---

## 7. Weighted prime-power mode

### 7.1 一項

```lean
noncomputable def eulerPrimePowerShadowMode
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (s : ℂ) : ℂ :=
  ((pascalPrimePowerLabel p hp k).vonMangoldtLogCost : ℂ) *
    eulerPrimePowerMode p (k + 1) s
```

中心 theorem:

```lean
theorem eulerPrimePowerShadowMode_eq_log_mul_mode
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (s : ℂ) :
    eulerPrimePowerShadowMode p hp k s =
      (Real.log (p : ℝ) : ℂ) *
        (eulerPrimePrimitiveMode p s) ^ (k + 1)
```

これは有限 von-Mangoldt shadow の complex mode 版である。

---

## 8. 有限 prime-power ladder wave

まず rectangular cutoff を使う。

- prime cutoff: `N`
- exponent-count cutoff: `K`

`K = 0` は空 ladder、`K = 1` は first harmonic のみ。

### 8.1 定義

```lean
noncomputable def pascalPrimeEulerPrimePowerLogWaveUpTo
    (N K : ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ pascalPrimeCoordinateSupportUpTo N,
    ∑ k ∈ Finset.range K,
      (Real.log (p : ℝ) : ℂ) *
        eulerPrimePowerMode p (k + 1) s
```

### 8.2 first-harmonic recovery

PPW-007 wave を exact に回収する。

```lean
@[simp] theorem pascalPrimeEulerPrimePowerLogWaveUpTo_one
    (N : ℕ) (s : ℂ) :
    pascalPrimeEulerPrimePowerLogWaveUpTo N 1 s =
      pascalPrimeEulerPrimitiveLogWaveUpTo N s
```

これは重要。PPW-008 が新しい別 wave を作るのではなく、PPW-007 を ladder の第1層として包含することを固定する。

### 8.3 exponent successor

```lean
@[simp] theorem pascalPrimeEulerPrimePowerLogWaveUpTo_exponent_succ
    (N K : ℕ) (s : ℂ) :
    pascalPrimeEulerPrimePowerLogWaveUpTo N (K + 1) s =
      pascalPrimeEulerPrimePowerLogWaveUpTo N K s +
        ∑ p ∈ pascalPrimeCoordinateSupportUpTo N,
          (Real.log (p : ℝ) : ℂ) *
            eulerPrimePowerMode p (K + 1) s
```

### 8.4 Pascal prime-birth successor

prime support 側の `(N,N+1)` 更新も保持する。

新 prime `N+1` が出生した場合、その prime の exponent `1..K` ladder 全体が追加される。

候補:

```lean
@[simp] theorem pascalPrimeEulerPrimePowerLogWaveUpTo_prime_succ_sub
    (N K : ℕ) (s : ℂ) :
    pascalPrimeEulerPrimePowerLogWaveUpTo (N + 1) K s -
        pascalPrimeEulerPrimePowerLogWaveUpTo N K s =
      if h : Nat.Prime (N + 1) then
        ∑ k ∈ Finset.range K,
          (Real.log ((N + 1 : ℕ) : ℝ) : ℂ) *
            eulerPrimePowerMode (N + 1) (k + 1) s
      else 0
```

依存 `if h : ...` が elaboration しにくければ、prime / non-prime を別 theorem に分割してもよい。

数学的内容を優先する。

---

## 9. Euler factor との有限幾何 bridge

PPW-007 の primitive mode を `M` と書くと、Euler factor は algebraically、

$$
F_p(s)=\frac1{1-M_p(s)}
$$

である。

候補 theorem:

```lean
theorem eulerZetaFactor_eq_inv_one_sub_primitiveMode
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerZetaFactor p s =
      (1 - eulerPrimePrimitiveMode p s)⁻¹
```

さらに有限 geometric identity を置く。

$$
(1-M)\sum_{j=0}^{K}M^j=1-M^{K+1}
$$

または PHZ 向けに、

$$
\sum_{j=1}^{K}M^j
$$

の形を固定する。

Mathlib の `geom_sum_mul` 等を再利用してよい。

ここでは infinite series へ進まない。

---

## 10. Prime-power mirror ratio / Gap

可能なら同じ module で、prime-power mode の horizontal selector も固定する。

```lean
noncomputable def eulerPrimePowerMirrorRatio
    (p k : ℕ) (s : ℂ) : ℝ :=
  ‖eulerPrimePowerMode p k (criticalMirror s)‖ /
    ‖eulerPrimePowerMode p k s‖
```

`hp : Nat.Prime p`, `hk : 0 < k` のもとで、

$$
R_{p,k}(s)=R_p(s)^k
$$

を証明する。

候補:

```lean
theorem eulerPrimePowerMirrorRatio_eq_pow
```

Gap:

```lean
noncomputable def eulerPrimePowerMirrorGap
    (p k : ℕ) (s : ℂ) : ℝ :=
  let r := eulerPrimePowerMirrorRatio p k s
  r + r⁻¹ - 2
```

`k > 0` なら、

```lean
theorem eulerPrimePowerMirrorGap_nonneg

theorem eulerPrimePowerMirrorGap_eq_zero_iff_re_eq_half
```

まで Green 化可能なら入れる。

ただしこの節は prime-power complex ladder より優先度は下。Lean proof engineering が重ければ PPW-009 へ送ってよい。

---

## 11. この checkpoint の数学的境界

PPW-008 で主張してよいもの:

```text
Pascal prime birth
→ primitive p-mode
→ positive integer powers
→ explicit prime-power label p^k
→ finite shadow cost log p
→ finite prime-power complex ladder
```

主張してはいけないもの:

```text
- この shadow が Mathlib / classical analytic von Mangoldt function そのものである
- rectangular cutoff が自然数 cutoff q ≤ X と同じである
- finite ladder wave が -ζ'/ζ と等しい
- Euler product と ladder wave の値が等しい
- zeta zero で wave が 0 になる
- RH が従う
```

特に、`-ζ'/ζ` は零点で 0 ではなく pole を持つ側の観測量である。後の zero-sensitive bridge では、零点との関係を「消滅」と誤読しないこと。

---

## 12. 次 checkpoint への出口

PPW-008 が Green になったら、次は rectangular `(p,k)` cutoff を自然数 prime-power label cutoffへ折り畳む。

候補 module:

```text
DkMath.RH.CFBRC.PascalPrimePowerPHZFinite
```

狙い:

```text
(p,k) with p prime, 0 < k, p^k ≤ X
        ↓
explicit PrimePowerLabel q = p^k
        ↓
weight log p
        ↓
finite Dirichlet polynomial
Σ_{p^k ≤ X} (log p) (p^k)^(-s)
```

ここで初めて classical von-Mangoldt Dirichlet polynomial と比較できる形になる。

その次に `Re(s) > 1` の安全領域で標準 `-ζ'/ζ` との接続を監査する。

---

## 13. 推奨 build

```bash
lake build DkMath.RH.CFBRC.PascalPrimePowerModeBridge
lake build DkMath.RH
git diff --check
```

新規 module に `sorry` / `axiom` / `admit` を入れない。

statement の数学内容を保つ範囲で、`simp`、`ring`、`field_simp`、`cpow` 正規形、Finset index の細部は Codex に調整を任せる。
