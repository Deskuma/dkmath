# Eta unit-Gap 正規化 bridge と obstruction audit 実装指示

cid: `6a7469f9-7968-83e8-bd4d-a5f044d2ee1a`

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-002-Eta-ratio-gap-energy-bridge-handoff.md
```

PPW-002 は Green となり、次の module が追加された。

```text
DkMath.RH.CFBRC.PrimeMirrorEtaEnergyBridge
```

主要 theorem は次である。

```lean
etaEndpointIncrementMirrorRatio_pos
etaEndpointIncrementMirrorGap_eq_primeMirrorOffsetGap
etaEndpointIncrementMirrorGap_nonneg
etaEndpointIncrementMirrorGap_eq_zero_iff_re_eq_half
etaEndpointIncrementMirrorGap_pos_of_re_ne_half
etaEndpointIncrementMirrorEnergyUpTo_eq_primeMirrorEnergy
etaEndpointIncrementMirrorEnergyUpTo_succ_sub
etaEndpointIncrementMirrorEnergyUpTo_succ_eq
etaEndpointIncrementMirrorEnergy_mode_one_le
etaEndpointIncrementMirrorEnergy_pos_of_re_ne_half
```

## 2. PPW-002 レビュー結果

### 2.1 Ratio-gap identity は正しい

eta endpoint increment ratio を `R_N(s)` とすると、実装された Gap は次である。

$$
G_N(s):=R_N(s)+R_N(s)^{-1}-2
$$

prime mirror amplitudes `a`, `b` は `ab = 1` を満たすため、次が exact に成立する。

$$
G_N(s)=(a-b)^2
$$

したがって、eta endpoint increment の観測値と `primeMirrorOffsetGap` は同じ非負量を読んでいる。

### 2.2 Index discipline は整合している

eta index `N` の実際の正の底は `N + 1` である。

```text
etaEndpointIncrement N s
  → etaSignedVector s N
  → positive base N + 1
```

新 bridge も `primeMirrorOffsetGap (N + 1)` を使用しており、shift は一致している。

### 2.3 `N = 0` の除外は必要である

`N = 0` では底が `1` となる。

$$
1^\delta=1
$$

したがって Gap は任意の横 offset で零となる。臨界線の特徴付けに `0 < N` を要求する現在の theorem は妥当である。

### 2.4 Base-two lower bound は後の collision に使用できる

cutoff `M ≥ 2` では eta index `1`、すなわち底 `2` の mode が常に含まれる。

正 weight と off-critical 条件の下で、この固定 mode が finite energy の正下界を与える。これにより、同じ finite energy が零へ収束する theorem を独立に得られれば collision を構成できる。

## 3. 次に統合すべき既存 Core

PPW-002 で導入した `etaEndpointIncrementMirrorGap` は新しい独立 Gap ではない。

既存 module

```text
DkMath.RH.CFBRC.EtaMirrorUnitSplit
```

には既に次が存在する。

```lean
etaMirrorAmplitudePair
etaMirrorAmplitudeGap
etaMirrorAmplitudeProduct
etaMirrorUnitPair
etaMirrorUnitGap
```

`etaMirrorUnitGap` は、正の ratio `r` から作る reciprocal pair

$$
\left(\sqrt r,\frac1{\sqrt r}\right)
$$

の差の平方である。したがって、

$$
\left(\sqrt r-\frac1{\sqrt r}\right)^2
=r+r^{-1}-2
$$

となり、PPW-002 の `etaEndpointIncrementMirrorGap` と同じ量である。

次の実装では、この同一性を exact theorem として固定し、Gap 名の重複による意味論分裂を防ぐ。

## 4. Raw amplitude Gap と normalized unit Gap

eta index `m` に対し、次を置く。

$$
x_m(s):=\lVert\eta_m(s)\rVert
$$

$$
y_m(s):=\lVert\eta_m(\mathrm{criticalMirror}(s))\rVert
$$

$$
q_m:=m+1
$$

既存 norm formula より、

$$
x_m(s)=q_m^{-s.re}
$$

$$
y_m(s)=q_m^{-(1-s.re)}
$$

したがって積は実部に依存せず、

$$
x_m(s)y_m(s)=q_m^{-1}
$$

となる。

Raw amplitude Gap は、

$$
A_m(s):=(y_m(s)-x_m(s))^2
$$

normalized unit Gap は、

$$
U_m(s):=\frac{y_m(s)}{x_m(s)}+\frac{x_m(s)}{y_m(s)}-2
$$

である。積 identity から、

$$
U_m(s)=q_mA_m(s)
$$

および、

$$
A_m(s)=q_m^{-1}U_m(s)
$$

が exact に成立する。

この `q_m = m + 1` が、raw endpoint data と横 offset selector の間に必要な正規化係数である。

## 5. 新規 module

次を追加する。

```text
DkMath.RH.CFBRC.PrimeMirrorEtaNormalizationBridge
```

推奨 import は次である。

```lean
import DkMath.RH.CFBRC.PrimeMirrorEtaEnergyBridge
import DkMath.RH.CFBRC.EtaMirrorUnitSplit
import DkMath.RH.Weave.Analytic.EtaHalfPlaneReconstruction
import Mathlib.Tactic
```

namespace は既存と同じものを使用する。

```lean
namespace DkMath.RH.CFBRCProjection
```

必要に応じて次を open する。

```lean
open Filter
open scoped Topology
open DkMath.RH.Weave.Analytic
```

## 6. 実装対象

### 6.1 Endpoint ratio-gap と既存 unit Gap の同一性

中心 theorem は次である。

```lean
theorem etaEndpointIncrementMirrorGap_eq_etaMirrorUnitGap
    (s : ℂ) (m : ℕ) :
    etaEndpointIncrementMirrorGap s m = etaMirrorUnitGap s m
```

証明では、次を使用する。

```lean
etaEndpointIncrementMirrorRatio_eq_etaMirrorAmplitudeRatio
etaMirrorAmplitudeRatio_pos
Real.sq_sqrt
```

必要なら `etaMirrorUnitPair`、`etaMirrorUnitGap`、`UnitPair.gap` を unfold し、正の ratio に対して field simplification を行う。

この theorem により、以後の正規化 Gap の正本は既存 `etaMirrorUnitGap` とする。`etaEndpointIncrementMirrorGap` は endpoint increment observation から同じ量を読む bridge 名として残す。

### 6.2 Genuine eta amplitude product

次を証明する。

```lean
theorem etaMirrorAmplitudeProduct_eq_inv_succ
    (s : ℂ) (m : ℕ) :
    etaMirrorAmplitudeProduct s m =
      (((m + 1 : ℕ) : ℝ))⁻¹
```

または Mathlib の `Real.rpow` 正規形に合わせた同値 statement でもよい。

証明では次を使用する。

```lean
etaMirrorAmplitudeProduct_eq
norm_etaSignedVector_eq_rpow
criticalMirror_re
Real.rpow_add
Real.rpow_neg
```

底 `m + 1` は常に正である。

### 6.3 Raw Gap と normalized Gap の scaling identity

次を証明する。

```lean
theorem etaEndpointIncrementMirrorGap_eq_succ_mul_amplitudeGap
    (s : ℂ) (m : ℕ) :
    etaEndpointIncrementMirrorGap s m =
      ((m + 1 : ℕ) : ℝ) * etaMirrorAmplitudeGap s m
```

逆向きも置く。

```lean
theorem etaMirrorAmplitudeGap_eq_inv_succ_mul_endpointGap
    (s : ℂ) (m : ℕ) :
    etaMirrorAmplitudeGap s m =
      (((m + 1 : ℕ) : ℝ))⁻¹ *
        etaEndpointIncrementMirrorGap s m
```

証明は一般代数として、

$$
\frac yx+\frac xy-2=\frac{(y-x)^2}{xy}
$$

と `x y = (m + 1)⁻¹` を使用する。

近似式や漸近式へ弱めず、有限 index ごとの exact identity とする。

### 6.4 Raw amplitude Gap energy

次を定義する。

```lean
noncomputable def etaMirrorAmplitudeGapEnergyUpTo
    (weight : ℕ → ℝ) (M : ℕ) (s : ℂ) : ℝ :=
  ∑ m in Finset.range M,
    weight m * etaMirrorAmplitudeGap s m
```

normalized energy との exact rescaling を置く。

```lean
theorem etaEndpointIncrementMirrorEnergyUpTo_eq_rescaledAmplitudeGapEnergy
    (weight : ℕ → ℝ) (M : ℕ) (s : ℂ) :
    etaEndpointIncrementMirrorEnergyUpTo weight M s =
      etaMirrorAmplitudeGapEnergyUpTo
        (fun m => ((m + 1 : ℕ) : ℝ) * weight m) M s
```

statement の左右は、実装しやすい同値な weight 配置へ調整してよい。ただし、normalized Gap を得るために各 raw Gap へ `m + 1` が必要であることを明示する。

### 6.5 Open strip で raw amplitude Gap は無条件に零へ収束する

次を証明する。

```lean
theorem etaMirrorAmplitudeGap_tendsto_zero_of_openStrip
    {s : ℂ}
    (hleft : 0 < s.re)
    (hright : s.re < 1) :
    Tendsto (fun m : ℕ => etaMirrorAmplitudeGap s m)
      atTop (nhds 0)
```

考え方は次である。

1. `hleft` から original eta term norm が零へ収束する。
2. `hright` と `criticalMirror_re` から mirror 側実部 `1 - s.re` が正である。
3. mirror eta term norm も零へ収束する。
4. 二つの norm の差の平方も零へ収束する。

既存 `etaUnsignedVector_tendsto_zero_of_pos_re`、`norm_etaSignedVector_eq_rpow`、norm の連続性を利用してよい。

この theorem はゼータ零点を仮定しない。

## 7. 重要な obstruction audit

### 7.1 Raw Gap collapse は臨界線を選ばない

open strip 全体で、

$$
A_m(s)\longrightarrow0
$$

となる。

したがって、非自明零点から raw amplitude Gap collapse を得ても RH へは進まない。これは eta term 自体が減衰することによる自明な collapse である。

### 7.2 臨界線を選ぶのは normalized Gap

normalized Gap は、

$$
U_m(s)=(m+1)A_m(s)
$$

である。

各固定非定数 mode では、

$$
U_m(s)=0
\iff
s.re=\frac12
$$

となる。

したがって、zero-locus data から normalized Gap collapse を導くには、発散する可能性を持つ係数 `m + 1` を越える強い rate theorem が必要である。

### 7.3 禁止される飛躍

次を無証明で導入しない。

```text
raw endpoint Gap → 0
  だから
normalized unit Gap → 0
```

この推論には rate 情報が必要である。単なる `Tendsto ... 0` では乗算係数 `m + 1` を吸収できない。

また、この coupling を structure field として仮定するだけでは、既存 `EtaKUSMirrorGapBridgeAudit` と同様に RH-equivalent な Gap を名前変更しただけになる可能性が高い。

## 8. Build checkpoint

```bash
lake env lean DkMath/RH/CFBRC/PrimeMirrorEtaNormalizationBridge.lean
lake env lean DkMath/RH/CFBRC/PrimeMirrorEnergy.lean
lake env lean DkMath/RH.lean
```

可能なら次も実行する。

```bash
lake build DkMath.RH.CFBRC.PrimeMirrorEtaNormalizationBridge
lake build DkMath.RH
```

単体 Green 後、次を更新する。

```text
DkMath.RH.CFBRC.PrimeMirrorEnergy
DkMath.RH
```

新規 module に `sorry`、`axiom`、`admit` を残さない。

## 9. 完了報告に含めるもの

1. 追加・変更した file
2. Green になった theorem 一覧
3. `etaEndpointIncrementMirrorGap = etaMirrorUnitGap` の証明方法
4. amplitude product `1 / (m + 1)` の扱い
5. raw Gap と normalized Gap の exact scaling
6. open strip raw Gap collapse の build 結果
7. warning または linter 指摘

## 10. この checkpoint 後の進路

PPW-003 の目的は新しい RH bridge を仮定することではない。

目的は、次の三つの量を同じ体系へ統合することである。

```text
eta endpoint increment ratio-gap
existing eta mirror unit Gap
raw eta amplitude Gap
```

その上で、臨界線を選ぶために必要なのは raw collapse ではなく `m + 1` 正規化後の rate control であることを Lean theorem として固定する。

次の主要分岐は二つである。

```text
Analytic route:
  eta / completed-zeta / CFBRC 観測窓から
  normalized Gap を支配する rate identity を探す。

Arithmetic route:
  Pascal prime dial または Mangoldt weight から
  正規化係数と finite prime-coordinate energy の由来を構成する。
```

PPW-003 Green 後、既存 eta asymptotic が `m + 1` 正規化を供給できるかを先に監査し、供給できない場合は Pascal prime-coordinate decoder へ進む。
