# Pascal–Euler primitive mode bridge 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-006 PascalPrimeEulerEnergyBridge
```

PPW-006 は Green となり、次の module が追加された。

```text
DkMath.RH.CFBRC.PascalPrimeEulerEnergyBridge
```

この checkpoint では、有限 Euler factor から、その内部にある一つの振動 mode `p⁻ˢ` を exact に回収し、同じ mode から次の二つを読む。

```text
vertical observable:
  t log p を保持する有限 prime wave

horizontal observable:
  original / critical-mirror magnitude ratio から作る非負 Gap
```

Euler product と energy を同一視してはならない。両者が同じ prime mode を異なる観測方法で読むことを形式化する。

## 2. PPW-006 レビュー結果

### 2.1 共通 Pascal support は正しく固定された

実装では、累積 Pascal prime-coordinate support

```lean
pascalPrimeCoordinateSupportUpTo N
```

が、次の二つへ供給される。

```text
multiplicative side:
  pascalPrimeEulerProductUpTo N s

additive positive side:
  pascalPrimeMirrorLogEnergyUpTo N s
```

有限 Euler product は successor cutoff で新しい birth factor を一つ掛ける。

$$
E_{N+1}(s)=E_N(s)\,F_{N+1}(s)
$$

prime-mirror log energy は、同じ birth event で新しい非負項を一つ加える。

$$
\mathcal E_{N+1}(s)-\mathcal E_N(s)
=
\operatorname{BirthLogMass}(N+1)\,G_{N+1}(s)
$$

この `(N,N+1)` 更新則は整合している。

### 2.2 `N ≥ 2` の臨界線特徴付けは妥当である

`N ≥ 2` なら Pascal 累積 support に prime `2` が含まれる。

その weight `log 2` は正であり、base `2` の prime-mirror Gap は零になるのが臨界線だけなので、有限 energy 全体について次が成立する。

$$
\mathcal E_N(s)=0
\iff
s.re=\frac12
$$

### 2.3 現在の bridge は support bridge である

PPW-006 は Euler product と mirror energy が同じ prime support と `log p` coordinate を使用することを示した。

ただし、まだ次は示していない。

```text
Euler factor の内部から mirror Gap が回収されること
Euler product の値と additive energy の解析的関係
prime-power multiplicity
von Mangoldt weight
standard zeta zero との関係
```

この境界は module docstring に明記されており、妥当である。

## 3. 次の中心観測

Euler factor を次で書く。

$$
F_p(s):=\frac{p^s}{p^s-1}
$$

この reciprocal defect を取る。

$$
M_p(s):=1-F_p(s)^{-1}
$$

`p^s ≠ 0` を使えば、有限代数として次が成立する。

$$
M_p(s)=p^{-s}
$$

この `M_p(s)` が Euler factor 内部の primitive prime mode である。

`M_p(s)` は次を同時に持つ。

```text
phase:
  exp(-i t log p)

magnitude:
  p^(-s.re)
```

critical mirror を `m(s)` とすると、magnitude ratio は次になる。

$$
R_p(s):=
\frac{\lVert M_p(m(s))\rVert}{\lVert M_p(s)\rVert}
=p^{2(s.re-1/2)}
$$

さらに ratio-gap は、既存 prime-mirror Gap と一致する。

$$
R_p(s)+R_p(s)^{-1}-2
=
\operatorname{primeMirrorOffsetGapAt}(p,s)
$$

これにより、PPW-006 の energy は Euler factor から回収した primitive mode の mirror imbalance として読める。

## 4. 新規 module

次を追加する。

```text
DkMath.RH.CFBRC.PascalPrimeEulerModeBridge
```

推奨 path:

```text
lean/dk_math/DkMath/RH/CFBRC/PascalPrimeEulerModeBridge.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.PascalPrimeEulerEnergyBridge
import DkMath.RH.CFBRC.PrimeMirrorEtaBridge
import DkMath.RH.CFBRC.PrimeMirrorEtaEnergyBridge
import Mathlib.Tactic
```

namespace は既存と同じものを使用する。

```lean
namespace DkMath.RH.CFBRCProjection
```

必要に応じて次を open する。

```lean
open DkMath.NumberTheory
open DkMath.RH.EulerZeta
open DkMath.RH.Weave.Analytic
```

## 5. 実装対象

### 5.1 Euler primitive mode

次を定義する。

```lean
noncomputable def eulerPrimePrimitiveMode
    (p : ℕ) (s : ℂ) : ℂ :=
  1 - (eulerZetaFactor p s)⁻¹
```

中心 theorem は次である。

```lean
theorem eulerPrimePrimitiveMode_eq_inv_cpow
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePrimitiveMode p s = (((p : ℂ) ^ s))⁻¹
```

可能なら負指数形も置く。

```lean
theorem eulerPrimePrimitiveMode_eq_cpow_neg
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePrimitiveMode p s = (p : ℂ) ^ (-s)
```

Mathlib の complex `cpow` 正規形により statement は調整してよい。

証明では次を明示する。

```text
p は prime なので p > 0
(p : ℂ) ^ s は非零
1 - ((p^s)/(p^s-1))⁻¹ = (p^s)⁻¹
```

分母 `p^s - 1` が零になる場合を、暗黙に通常の除法へ置き換えない。Lean の `GroupWithZero` 上で成立する変形として証明する。

### 5.2 Eta mode との exact identification

prime `p` に対し eta index は `p - 1` である。

```lean
theorem eulerPrimePrimitiveMode_eq_etaUnsignedVector
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePrimitiveMode p s =
      etaUnsignedVector s (p - 1)
```

添字変形では次を使用する。

```text
p > 0
(p - 1) + 1 = p
```

既存 eta 定義の符号付き版ではなく、primitive mode と同じ unsigned mode を使用する。

### 5.3 Primitive mode magnitude ratio

次を定義する。

```lean
noncomputable def eulerPrimePrimitiveMirrorRatio
    (p : ℕ) (s : ℂ) : ℝ :=
  ‖eulerPrimePrimitiveMode p (criticalMirror s)‖ /
    ‖eulerPrimePrimitiveMode p s‖
```

正性を証明する。

```lean
theorem eulerPrimePrimitiveMirrorRatio_pos
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    0 < eulerPrimePrimitiveMirrorRatio p s
```

eta ratio との一致を置く。

```lean
theorem eulerPrimePrimitiveMirrorRatio_eq_etaMirrorAmplitudeRatio
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePrimitiveMirrorRatio p s =
      etaMirrorAmplitudeRatio s (p - 1)
```

prime-mirror ratio との一致も置く。

```lean
theorem eulerPrimePrimitiveMirrorRatio_eq_primeMirrorAmplitudeRatio
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePrimitiveMirrorRatio p s =
      primeMirrorRightAmplitude p (centeredSigma s.re) /
        primeMirrorLeftAmplitude p (centeredSigma s.re)
```

既存 theorem

```lean
primeMirrorAmplitudeRatio_eq_etaMirrorAmplitudeRatio
```

は eta index `m` と base `m + 1` を使用するため、`m := p - 1` として再利用する。

### 5.4 Euler primitive mirror Gap

次を定義する。

```lean
noncomputable def eulerPrimePrimitiveMirrorGap
    (p : ℕ) (s : ℂ) : ℝ :=
  let r := eulerPrimePrimitiveMirrorRatio p s
  r + r⁻¹ - 2
```

中心 theorem は次である。

```lean
theorem eulerPrimePrimitiveMirrorGap_eq_primeMirrorOffsetGapAt
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePrimitiveMirrorGap p s =
      primeMirrorOffsetGapAt p s
```

ここでは新しい平方展開を再実装せず、eta ratio-gap bridge または prime-mirror ratio theorem を再利用する。

派生 theorem も置く。

```lean
theorem eulerPrimePrimitiveMirrorGap_nonneg
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    0 ≤ eulerPrimePrimitiveMirrorGap p s
```

```lean
theorem eulerPrimePrimitiveMirrorGap_eq_zero_iff_re_eq_half
    {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    eulerPrimePrimitiveMirrorGap p s = 0 ↔
      s.re = (1 : ℝ) / 2
```

### 5.5 Pascal finite primitive log wave

同じ Pascal support 上に、phase を保持した complex wave を定義する。

```lean
noncomputable def pascalPrimeEulerPrimitiveLogWaveUpTo
    (N : ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ pascalPrimeCoordinateSupportUpTo N,
    (Real.log (p : ℝ) : ℂ) * eulerPrimePrimitiveMode p s
```

これは prime-only first-harmonic wave である。

次の successor update を置く。

```lean
@[simp]
theorem pascalPrimeEulerPrimitiveLogWaveUpTo_succ_sub
    (N : ℕ) (s : ℂ) :
    pascalPrimeEulerPrimitiveLogWaveUpTo (N + 1) s -
        pascalPrimeEulerPrimitiveLogWaveUpTo N s =
      (pascalPrimeBirthLogMass (N + 1) : ℂ) *
        eulerPrimePrimitiveMode (N + 1) s
```

additive form も置く。

```lean
@[simp]
theorem pascalPrimeEulerPrimitiveLogWaveUpTo_succ_eq
    (N : ℕ) (s : ℂ) :
    pascalPrimeEulerPrimitiveLogWaveUpTo (N + 1) s =
      pascalPrimeEulerPrimitiveLogWaveUpTo N s +
        (pascalPrimeBirthLogMass (N + 1) : ℂ) *
          eulerPrimePrimitiveMode (N + 1) s
```

非 prime row では birth mass が零になるため、mode 自体を prime と仮定せず右辺へ残してよい。

### 5.6 PPW-006 energy の mode-ratio 表現

次を証明する。

```lean
theorem pascalPrimeMirrorLogEnergyUpTo_eq_primitiveMirrorGapSum
    (N : ℕ) (s : ℂ) :
    pascalPrimeMirrorLogEnergyUpTo N s =
      ∑ p ∈ pascalPrimeCoordinateSupportUpTo N,
        Real.log (p : ℝ) * eulerPrimePrimitiveMirrorGap p s
```

これが PPW-007 の load-bearing finite identity である。

意味は次である。

```text
Euler factor
  → reciprocal defect
  → primitive mode p⁻ˢ
  → original / mirror magnitude ratio
  → nonnegative horizontal Gap
  → Pascal finite log energy
```

## 6. 重要な監査境界

### 6.1 Wave と energy は同じ値ではない

`pascalPrimeEulerPrimitiveLogWaveUpTo` は複素数値であり、`t log p` の phase 干渉を保持する。

`pascalPrimeMirrorLogEnergyUpTo` は実数値・非負であり、`s.re - 1/2` の mirror magnitude imbalance を読む。

したがって次を主張しない。

```text
primitive log wave = mirror energy
Euler product = mirror energy
wave norm-square = coordinate energy
```

複素和の norm-square には異なる prime 間の交差項が含まれる。

### 6.2 Prime-only wave は `-ζ'/ζ` ではない

今回の wave は、各 prime の `k = 1` mode のみを含む。

$$
\sum_p (\log p)\,p^{-s}
$$

標準の logarithmic derivative は prime powers 全体を含む。

$$
-\frac{\zeta'(s)}{\zeta(s)}
=
\sum_p\sum_{k\ge1}(\log p)\,p^{-ks}
$$

したがって PPW-007 では、`PHZ`、von Mangoldt、標準 zeta logarithmic derivative との一致を主張しない。

### 6.3 Finite Euler product の零点を標準 zeta 零点と混同しない

有限 Euler product は、通常の解析領域で標準 zeta の非自明零点を再現する対象ではない。

今回の目的は、Euler factor 内部から prime mode を exact に抽出することだけである。

### 6.4 RH を使用しない

次を仮定または使用しない。

```text
RiemannHypothesis
NontrivialRiemannZetaZero s → s.re = 1 / 2
RH-equivalent mirror-Gap provider
standard-zeta zero → energy zero
```

## 7. Docstring 方針

module docstring に次を明記する。

```text
- reciprocal defect of one Euler factor recovers the primitive mode p⁻ˢ
- the primitive complex wave retains vertical phase t log p
- its original/mirror norm ratio recovers the horizontal prime-mirror Gap
- the finite wave and finite energy use the same Pascal-born coordinates
- the wave is prime-only and is not the full logarithmic derivative
- no equality between multiplicative product, complex wave, and positive energy is asserted
```

各 theorem docstring では `support bridge`、`mode extraction`、`mirror-ratio bridge` を区別する。

## 8. Export

単体 Green 後、次を更新する。

```text
DkMath.RH.CFBRC.PrimeMirrorEnergy
DkMath.RH
```

既存の public import 方針に合わせ、循環 import を避ける。

## 9. Build checkpoint

```bash
lake env lean DkMath/RH/CFBRC/PascalPrimeEulerModeBridge.lean
lake env lean DkMath/RH/CFBRC/PrimeMirrorEnergy.lean
lake env lean DkMath/RH.lean
```

さらに次を実行する。

```bash
lake build DkMath.RH.CFBRC.PascalPrimeEulerModeBridge
lake build DkMath.RH

git diff --check
```

新規 module に `sorry`、`axiom`、`admit` を残さない。

## 10. 完了報告に含めるもの

1. 追加・変更した file
2. Green になった theorem 一覧
3. reciprocal defect から `p⁻ˢ` を回収した証明方法
4. `p - 1` eta index の扱い
5. primitive mirror ratio と prime-mirror Gap の一致
6. finite primitive log wave の successor update
7. PPW-006 energy の primitive-mode-ratio 表現
8. warning または linter 指摘

## 11. この checkpoint 後の進路

PPW-007 Green 後、primitive mode の冪を使って prime-power ladder を構成する。

候補 module:

```text
DkMath.RH.CFBRC.PascalPrimePowerWaveBridge
```

有限段階で次を定義する。

$$
\operatorname{PrimePowerWave}_{N,K}(s)
:=
\sum_{p\le N}\sum_{1\le k\le K}
(\log p)\,M_p(s)^k
$$

`M_p(s) = p⁻ˢ` なので、各項は `log p · p⁻ᵏˢ` になる。

この層で初めて、既存 `VonMangoldtShadow` または明示的 prime-power label と接続し、有限 PHZ / logarithmic-derivative shadow へ進む。

```text
PPW-006:
  Pascal birth support
    → finite Euler product
    → positive mirror energy

PPW-007:
  Euler factor
    → primitive phase mode p⁻ˢ
    → mirror ratio-gap
    → same-support complex wave / positive energy

PPW-008:
  primitive mode powers
    → prime-power ladder
    → von Mangoldt shadow
    → finite PHZ
```
