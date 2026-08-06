# Eta normalized-Gap 漸近二分岐 audit 実装指示

cid: `6a7469f9-7968-83e8-bd4d-a5f044d2ee1a`

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-003-Eta-unit-gap-normalization-audit-handoff.md
```

PPW-003 は Green となり、次の module が追加された。

```text
DkMath.RH.CFBRC.PrimeMirrorEtaNormalizationBridge
```

主要 theorem は次である。

```lean
etaEndpointIncrementMirrorGap_eq_etaMirrorUnitGap
etaMirrorAmplitudeProduct_eq_inv_succ
etaEndpointIncrementMirrorGap_eq_succ_mul_amplitudeGap
etaMirrorAmplitudeGap_eq_inv_succ_mul_endpointGap
etaEndpointIncrementMirrorEnergyUpTo_eq_rescaledAmplitudeGapEnergy
etaMirrorAmplitudeGap_tendsto_zero_of_openStrip
```

## 2. PPW-003 レビュー結果

### 2.1 三つの Gap は exact に統合された

次の三つは同じ centered coordinate を読む。

```text
eta endpoint increment ratio-gap
eta mirror normalized unit Gap
prime mirror offset Gap
```

実装により、有限 index ごとに次が成立する。

$$
\mathrm{etaEndpointIncrementMirrorGap}(s,m)
=
\mathrm{etaMirrorUnitGap}(s,m)
$$

さらに、eta index `m` の底を `q = m + 1` とすると、raw amplitude Gap との関係は次である。

$$
\mathrm{etaEndpointIncrementMirrorGap}(s,m)
=
q\,\mathrm{etaMirrorAmplitudeGap}(s,m)
$$

近似ではなく exact identity である。

### 2.2 amplitude product は centered coordinate に依存しない

original と critical mirror の eta 一項 magnitude の積は、

$$
\lVert\eta_m(s)\rVert
\lVert\eta_m(\mathrm{criticalMirror}(s))\rVert
=
\frac1{m+1}
$$

となる。

横 offset は左右への振幅配分を変えるが、積は保存される。この保存積が raw Gap から normalized Gap への係数 `m + 1` を生む。

### 2.3 raw Gap collapse は open strip 全体で起きる

`0 < s.re < 1` では、original と mirror の一項 magnitude はともに零へ収束するため、

$$
\mathrm{etaMirrorAmplitudeGap}(s,m)\longrightarrow0
$$

となる。

この theorem は zeta zero を仮定しない。したがって raw Gap collapse は臨界線 selector ではない。

### 2.4 次に固定すべき内容

normalized Gap は raw Gap に `m + 1` を掛けた量である。

```text
raw Gap:
  open strip 全体で 0 へ収束する

normalized Gap:
  critical line では常に 0
  off-critical では増大する
```

PPW-004 では、この二分岐を exact な漸近 theorem として固定する。

## 3. 数学的 Core

複素数 `s` の centered coordinate を、

$$
\delta:=\mathrm{centeredSigma}(s.re)
$$

とする。

eta index `m` の正の底を、

$$
q_m:=m+1
$$

とする。

PPW-002 と PPW-003 の identity から、normalized Gap は次である。

$$
U_m(s)
=
q_m^{2\delta}+q_m^{-2\delta}-2
$$

同じ量は exponential 表示では次である。

$$
U_m(s)
=
\exp(2\delta\log q_m)
+
\exp(-2\delta\log q_m)
-2
$$

この式は `δ` の符号反転に対して不変である。

$$
U_m(-\delta)=U_m(\delta)
$$

したがって、

```text
δ = 0:
  U_m = 0 for every m

δ ≠ 0:
  U_m → +∞
```

となる。

raw amplitude Gap は、

$$
A_m(s)
=
q_m^{-1}U_m(s)
$$

であり、展開すると次である。

$$
A_m(s)
=
q_m^{-2s.re}
+
q_m^{-2(1-s.re)}
-
2q_m^{-1}
$$

open strip では右辺の各項が零へ収束するが、off-critical では減衰速度が `q_m^{-1}` より遅い側が残るため、`q_m A_m(s)` は発散する。

## 4. 新規 module

次を追加する。

```text
DkMath.RH.CFBRC.PrimeMirrorEtaAsymptoticDichotomy
```

推奨 import は次である。

```lean
import DkMath.RH.CFBRC.PrimeMirrorEtaNormalizationBridge
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
```

## 5. 実装対象

### 5.1 Prime mirror Gap の closed form

まず一 mode の closed form を証明する。

```lean
theorem primeMirrorOffsetGap_eq_rpow_pair
    {n : ℕ} (hn : 0 < n) (δ : ℝ) :
    primeMirrorOffsetGap n δ =
      ((n : ℝ) ^ (2 * δ)) +
        ((n : ℝ) ^ (-2 * δ)) - 2
```

項の順序は Mathlib の正規形に合わせて調整してよい。

証明では次を使用する。

```lean
primeMirrorAmplitude_mul_eq_one
Real.rpow_def_of_pos
Real.exp_add
```

または `primeMirrorOffsetGap` を展開し、ring normalization を用いてよい。

### 5.2 符号反転不変性

```lean
@[simp]
theorem primeMirrorOffsetGap_neg_delta
    (n : ℕ) (δ : ℝ) :
    primeMirrorOffsetGap n (-δ) = primeMirrorOffsetGap n δ
```

left/right amplitude が交換され、差の平方が保存されることから証明できる。

複素点についても critical mirror 対称性を置く。

```lean
@[simp]
theorem etaEndpointIncrementMirrorGap_criticalMirror
    (s : ℂ) (m : ℕ) :
    etaEndpointIncrementMirrorGap (criticalMirror s) m =
      etaEndpointIncrementMirrorGap s m
```

必要なら先に次を証明する。

```lean
centeredSigma (criticalMirror s).re = -centeredSigma s.re
```

既存に同名・同内容 theorem がある場合は再利用する。

### 5.3 Eta normalized Gap の closed form

```lean
theorem etaEndpointIncrementMirrorGap_eq_rpow_pair
    (s : ℂ) (m : ℕ) :
    etaEndpointIncrementMirrorGap s m =
      ((((m + 1 : ℕ) : ℝ) ^
        (2 * centeredSigma s.re)) +
       (((m + 1 : ℕ) : ℝ) ^
        (-2 * centeredSigma s.re)) - 2)
```

既存 bridge

```lean
etaEndpointIncrementMirrorGap_eq_primeMirrorOffsetGap
```

から導く。

### 5.4 Raw amplitude Gap の closed form

```lean
theorem etaMirrorAmplitudeGap_eq_rpow_decomposition
    (s : ℂ) (m : ℕ) :
    etaMirrorAmplitudeGap s m =
      ((((m + 1 : ℕ) : ℝ) ^ (-2 * s.re)) +
       (((m + 1 : ℕ) : ℝ) ^ (-2 * (1 - s.re))) -
       2 * (((m + 1 : ℕ) : ℝ)⁻¹))
```

statement は Mathlib の `Real.rpow` 正規形に合わせてよい。

この theorem は後の rate 比較で使用するため、近似式ではなく finite index ごとの exact identity とする。

### 5.5 Positive centered coordinate で normalized Gap が発散する

```lean
theorem etaEndpointIncrementMirrorGap_tendsto_atTop_of_centeredSigma_pos
    {s : ℂ}
    (hδ : 0 < centeredSigma s.re) :
    Tendsto
      (fun m : ℕ => etaEndpointIncrementMirrorGap s m)
      atTop atTop
```

考え方は次である。

1. `q_m ^ (2 * δ)` は `+∞` へ向かう。
2. `q_m ^ (-2 * δ)` は非負である。
3. 全体は `q_m ^ (2 * δ) - 2` 以上である。
4. 比較により normalized Gap は `+∞` へ向かう。

Mathlib API に応じて `Real.tendsto_rpow_atTop`、`tendsto_nat_succ_cast_atTop`、eventual lower bound を利用する。

### 5.6 Negative centered coordinate での発散

```lean
theorem etaEndpointIncrementMirrorGap_tendsto_atTop_of_centeredSigma_neg
    {s : ℂ}
    (hδ : centeredSigma s.re < 0) :
    Tendsto
      (fun m : ℕ => etaEndpointIncrementMirrorGap s m)
      atTop atTop
```

符号反転不変性を使い、positive case へ帰着する。

critical mirror を経由してもよい。

### 5.7 Off-critical 漸近二分岐

```lean
theorem etaEndpointIncrementMirrorGap_tendsto_atTop_of_re_ne_half
    {s : ℂ}
    (hre : s.re ≠ (1 : ℝ) / 2) :
    Tendsto
      (fun m : ℕ => etaEndpointIncrementMirrorGap s m)
      atTop atTop
```

`centeredSigma s.re ≠ 0` を得た後、正負に分ける。

### 5.8 Critical line では恒等的に零

```lean
@[simp]
theorem etaEndpointIncrementMirrorGap_eq_zero_of_re_eq_half
    {s : ℂ}
    (hre : s.re = (1 : ℝ) / 2) :
    ∀ m : ℕ, etaEndpointIncrementMirrorGap s m = 0
```

既存の pointwise zero-locus theorem を使ってよい。ただし `m = 0` も含める場合、底 `1` による自明な零と臨界線による零を区別して証明する。

より扱いやすければ、次の sequence theorem とする。

```lean
theorem etaEndpointIncrementMirrorGap_tendsto_zero_of_re_eq_half
    {s : ℂ}
    (hre : s.re = (1 : ℝ) / 2) :
    Tendsto
      (fun m : ℕ => etaEndpointIncrementMirrorGap s m)
      atTop (nhds 0)
```

### 5.9 Tendsto zero の完全特徴付け

```lean
theorem etaEndpointIncrementMirrorGap_tendsto_zero_iff_re_eq_half
    (s : ℂ) :
    Tendsto
      (fun m : ℕ => etaEndpointIncrementMirrorGap s m)
      atTop (nhds 0) ↔
      s.re = (1 : ℝ) / 2
```

逆向きは critical-line constant-zero theorem を使う。

順向きでは、off-critical を仮定すると同じ sequence が `atTop` へ発散するため、`nhds 0` への収束と両立しないことを示す。

Mathlib に適切な一意性 theorem がない場合は、例えば eventually `1 < gap` と eventually `gap < 1` の衝突を構成してよい。

### 5.10 Raw と normalized の漸近衝突を明示する

open strip と off-critical を同時に仮定した theorem を置く。

```lean
theorem etaMirrorAmplitudeGap_raw_zero_normalized_atTop
    {s : ℂ}
    (hleft : 0 < s.re)
    (hright : s.re < 1)
    (hre : s.re ≠ (1 : ℝ) / 2) :
    Tendsto (fun m : ℕ => etaMirrorAmplitudeGap s m)
        atTop (nhds 0) ∧
      Tendsto
        (fun m : ℕ =>
          ((m + 1 : ℕ) : ℝ) * etaMirrorAmplitudeGap s m)
        atTop atTop
```

第二成分は scaling identity と normalized Gap の発散から導く。

この theorem が PPW-003 の obstruction を最も明瞭に固定する。

## 6. 妥当性 audit

### 6.1 これは RH 証明ではない

normalized Gap の漸近二分岐は、`s.re` から直接計算される純代数・実解析 Core である。

```text
critical line:
  normalized Gap is identically zero

off-critical:
  normalized Gap tends to +∞
```

非自明零点条件は使用しない。

### 6.2 Endpoint decay route の限界を固定する

eta endpoint または eta 一項の raw magnitude が零へ収束しても、左右の相対比は保存されるか増幅される。

したがって次の推論は禁止される。

```text
original endpoint → 0
mirror endpoint → 0
  だから
mirror ratio-gap → 0
```

左右が異なる速度で零へ向かう場合、ratio-gap は逆に発散する。

### 6.3 Zero-locus Beam に必要なもの

今後必要なのは単一 mode の decay estimate ではない。

必要なのは、複数 prime mode の干渉、隣接 cutoff 履歴、Pascal prime coordinate、または completed-zeta の global identity から、同じ normalized residual energy を零へ送る独立な theorem である。

単一 eta term の asymptotic を精密化しても、closed form が既に off-critical 発散を固定しているため、主 Gap は埋まらない。

## 7. Build checkpoint

```bash
lake env lean DkMath/RH/CFBRC/PrimeMirrorEtaAsymptoticDichotomy.lean
lake env lean DkMath/RH/CFBRC/PrimeMirrorEnergy.lean
lake env lean DkMath/RH.lean
```

可能なら次も実行する。

```bash
lake build DkMath.RH.CFBRC.PrimeMirrorEtaAsymptoticDichotomy
lake build DkMath.RH
```

単体 Green 後、次を更新する。

```text
DkMath.RH.CFBRC.PrimeMirrorEnergy
DkMath.RH
```

新規 module に `sorry`、`axiom`、`admit` を残さない。

## 8. 完了報告に含めるもの

1. 追加・変更した file
2. Green になった theorem 一覧
3. closed form の最終 Lean 正規形
4. positive／negative centered coordinate の分岐方法
5. off-critical で `atTop` へ発散する theorem
6. critical line で zero sequence となる theorem
7. raw Gap が零へ収束し normalized Gap が発散する対照 theorem
8. 実行した build command と結果
9. warning または linter 指摘

## 9. この checkpoint 後の進路

PPW-004 が Green になれば、per-mode eta asymptotic route の audit は完了する。

次は arithmetic/global route へ移る。

```text
DkMath.NumberTheory.PascalPrimeCoordinateDecoder
```

で、既存 `PascalPrimeDial` から有限 prime coordinate と row transition を構成する。

最初の段階では Mangoldt 関数や無限 Dirichlet series まで一度に進めない。

```text
Pascal row n
  → その行で可視な prime dial support
  → row n と row n + 1 の差分
  → 新しく追加・変化した prime coordinate
```

を有限対象として Green 化する。

その後、Pascal 由来 coordinate を `PrimeMirrorFiniteEnergy` の index set と weight へ供給し、Euler-zeta／PHZ 観測窓へ接続する。
