# CFZP-0037 — CFZP-011 same-height mirror source mode-transform audit 実装指示

## 0. Status

- Repository: `Deskuma/dkmath`
- Working branch: `wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`
- Parent implementation: CFZP-010
- Expected parent commit: `c9397e71eae0d66888e9701cf6edc5e2b2dbf897`
- 日本語を正本とする。

CFZP-010 は Green-A とする。

010 で次が exact に確定した。

```text
amplitude-side mirror Gap
  = diagonal sum of modewise normSq

source-side ray-minus
  = normSq (Z - 1)

Z
  = finite sum of source geometric modes

normSq (finite sum)
  = full finite Gram ledger
  = diagonal + off-diagonal interference
```

さらに二つの equal modes だけでも

```text
normSq (a + b) != normSq a + normSq b
```

となる反例を固定したため、旧 backlog

```text
amplitude Gap = ray-minus whole
```

を一段の equality として狙う設計は棄却する。

残る橋は少なくとも次の三層である。

```text
Layer 1: mirror amplitude mode -> source geometric mode transport
Layer 2: diagonal ledger -> full Gram/interference transport
Layer 3: source baseline 1 / interaction normalization -> ray-minus whole
```

011 は Layer 1 のみを exact に閉じる。

---

## 1. 011 の中心発見

CS15 の source ray summand は既に exact に

```text
weight(t) * q^(-sR(t))
```

という形である。

ここで

```text
sR(t) := pascalSymmetricRectangleRightEdge W.rectangle.σ t
q := p^(k+1)
weight(t) := pascalCenteredXiMellinSecondDifferenceWeight ε 0
  (pascalCenteredXiPrimeSideModePhaseNode W t)
```

である。

一方 CFZP-004 には same-height critical mirror mode difference

```text
cfzpSameHeightMirrorModeDifference q s
  = q^(-criticalMirror s) - q^(-s)
```

があり、CFZP-001 により critical mirror は水平 amplitude のみを反転し、cycle height は保持する。

したがって source 側に same-height mirror summand を新しく明示すれば、mode ごとに

```text
mirrorSourceSummand - rightSourceSummand
  = weight(t) * cfzpSameHeightMirrorModeDifference q (sR(t))
```

が exact に出るはずである。

さらに normSq を取れば

```text
normSq(source pair difference)
  = normSq(weight(t)) * normSq(amplitude mirror mode difference)
```

となる。

つまり Layer 1 の本質は未知の arithmetic transform ではなく、既存 source mode へ same-height mirror mate を付与し、Mellin weight を明示的な multiplicative transport factor として残すことである。

---

## 2. 011 の出口条件

011 は一つの module で少なくとも次を exact に閉じる。

```text
right source summand
  = weight * q^(-sR)

same-height mirror source summand
  = weight * q^(-criticalMirror sR)

pair difference
  = weight * cfzpSameHeightMirrorModeDifference q sR

normSq(pair difference)
  = normSq(weight) * normSq(cfzpSameHeightMirrorModeDifference q sR)
```

次に base prime `p` の finite exponent support 上で mirror ray を定義し、既存 right ray と比較する。

```text
ZM(p,t) := sum_k mirrorSourceSummand(p,k,t)
ZR(p,t) := existing finite prime-power ray amplitude

ZM - ZR
  = sum_k weight * sameHeightMirrorModeDifference
```

ここまでが Layer 1 の主出口である。

最後に ray-minus の baseline residual を algebraically 分離する。

```text
ZR - 1
  = (ZR - ZM) + (ZM - 1)
```

必要なら `normSq` まで展開して

```text
normSq (ZR - 1)
  = normSq (ZR - ZM)
    + normSq (ZM - 1)
    + 2 * Re (conj (ZR - ZM) * (ZM - 1))
```

を exact に固定する。

この式により、011 終了時の未解決量は

```text
mirror baseline residual := ZM - 1
```

と、その residual と transformed amplitude difference の interference に局在化する。

---

## 3. 推奨 module

新規:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaSameHeightMirrorSourceModeTransformAudit
```

path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaSameHeightMirrorSourceModeTransformAudit.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaAmplitudeGapRayMinusObservableShapeAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteGeometricRayAudit
import Mathlib.Tactic
```

必要なら `CosmicFormulaZetaFinitePolarizationProjection` は 010 から transitively 入るので import duplication を避ける。

---

## 4. Gate A — right-edge source mode を q=p^(k+1) として固定

既存:

```lean
pascalCenteredXiPrimeSideFinitePrimePowerRaySummand
```

は

```text
weight(t) * ((p^(k+1)) : C)^(-sR(t))
```

である。

まず adapter theorem を用意して、source summand の構造を公開する。

候補:

```lean
cfzp011RightSourceSummand_eq_weight_mul_mode
```

右辺の `q` は `p^(k+1)` とする。

不要な新定義を増やさず、既存 summand を right source 正本として使う。

---

## 5. Gate B — same-height mirror source summand

新規定義候補:

```lean
noncomputable def cfzp011SameHeightMirrorSourceSummand
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p k : ℕ) (t : ℝ) : ℂ :=
  pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalCenteredXiPrimeSideModePhaseNode W t) *
    (((p ^ (k + 1) : ℕ) : ℂ) ^
      (-(criticalMirror
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t))))
```

これは functional reflection `1-s` ではなく、CFZP-004 と同じ **same-height `criticalMirror`** を使うこと。

必須 theorem:

```lean
cfzp011MirrorSourceSummand_sub_rightSourceSummand_eq_weight_mul_sameHeightModeDifference
```

概念形:

```text
mirrorSummand - rightSummand
  = weight * cfzpSameHeightMirrorModeDifference (p^(k+1)) sR
```

これは純代数 adapter であり、符号・非負・RH を含めない。

---

## 6. Gate C — modewise quadratic transport

Gate B から `Complex.normSq_mul` を使い、exact に

```text
normSq (mirrorSummand - rightSummand)
  = normSq weight *
      normSq (cfzpSameHeightMirrorModeDifference q sR)
```

を証明する。

候補:

```lean
cfzp011MirrorSourcePairDifference_normSq_eq_weightNormSq_mul_amplitudeModeGap
```

ここで amplitude-side の既存 theorem

```lean
normSq_cfzpSameHeightMirrorModeDifference
```

まで展開する追加 theorem は任意。

展開する場合は

```text
normSq sourcePairDifference
  = normSq weight
    * normSq sameHeightCommonCarrier
    * primeMirrorOffsetGap
```

まで exact に出してよい。

重要:

この時点で source pair diagonal ledger と CFZP-004 amplitude Gap ledger は一般には同一ではない。Mellin weight の `normSq` factor が残る。

したがって weight の normSq を勝手に `1` としない。

---

## 7. Gate D — finite same-height mirror ray

既存 exponent support

```lean
pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p
```

上で mirror ray を定義する。

候補:

```lean
noncomputable def cfzp011SameHeightMirrorPrimePowerRayAmplitude
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p,
    cfzp011SameHeightMirrorSourceSummand ε W p k t
```

既存 right ray は

```lean
pascalCenteredXiPrimeSideFinitePrimePowerRayAmplitude
```

を使う。

必須 theorem:

```lean
cfzp011MirrorRay_sub_rightRay_eq_sum_weighted_sameHeightModeDifference
```

概念形:

```text
ZM - ZR
  = sum_k weight * cfzpSameHeightMirrorModeDifference (p^(k+1)) sR
```

support reindex は既存 CS15/CS16 API を使うこと。

必要なら `Nat.Prime p` hypothesis の下で support=`Finset.range rayLength` adapter も公開してよいが、011 の本質ではない。

---

## 8. Gate E — ray-minus baseline residual decomposition

既存 source ray-minus pointwise observable は

```text
normSq (ZR - 1)
```

である。

mirror ray `ZM` を挿入して exact に

```text
ZR - 1 = (ZR - ZM) + (ZM - 1)
```

を証明する。

候補:

```lean
cfzp011RightRay_sub_one_eq_transformedAmplitudePart_add_mirrorBaselineResidual
```

さらに generic complex identity を一つ用意し、可能なら

```text
normSq (a + b)
  = normSq a + normSq b + 2 * Re (conj a * b)
```

を使って ray-minus を

```text
transformed amplitude quadratic part
+ mirror baseline residual quadratic part
+ cross interference
```

へ exact 分解する。

候補:

```lean
cfzp011RayMinusNormSq_eq_transformedAmplitude_add_mirrorResidual_add_interference
```

符号は実際の `a := ZR - ZM` の向きに Lean に決めさせること。

011 ではこの residual をゼロと証明しない。

---

## 9. Optional Gate F — canonical prime-power weight compatibility

余力があれば CS14 の canonical support / pair support reindex を使い、`q=p^(k+1)` で

```text
canonicalPrimePowerShadowCost q = log p
```

を source pair mode に transportする adapter を追加してよい。

目的は arithmetic coefficient mismatch が無いことを確認するためであり、aggregate equality を無理に閉じるためではない。

もし proof が膨らむなら 011 では省略してよい。

---

## 10. 011 closeout / frontier

011 が Green の場合、010 の三層 bridge は次のように更新する。

```text
Layer 1: CLOSED
  mirror amplitude mode
    -- multiply by Mellin weight -->
  same-height source pair difference

Layer 2: OPEN
  modewise weighted diagonal
    -> finite Gram/interference of transformed ray

Layer 3: SHARPENED
  ray-minus baseline problem
    -> mirror baseline residual (ZM - 1)
       + its interference with transformed amplitude part
```

残る Gap marker は一つか二つに整理する。

候補:

```lean
inductive Cfzp011MirrorBaselineResidualAndInterferenceBridgeGap : Prop
  | noMirrorBaselineResidualCollapseOrInterferenceProvider
```

Layer 2 を別 marker に分けるなら

```lean
inductive Cfzp011WeightedModeGramTransportGap : Prop
  | noAggregateWeightedGramTransportProvider
```

ただし marker を細分化しすぎない。

---

## 11. Hard exclusions

011 では以下をしない。

- `amplitude Gap = ray-minus whole` を直接主張しない。
- `normSq (sum) = sum normSq` を使わない。
- mirror baseline residual `ZM - 1 = 0` を仮定・証明しない。
- Mellin weight の normSq を `1` としない。
- same-height `criticalMirror` と functional reflection `1-s` を混同しない。
- `Complex.arg` を導入しない。
- global `Complex.log` branch を導入しない。
- infinite Euler product / infinite ray / cutoff limit を導入しない。
- common-baseline finite/cofinal reach provider を同時に攻めない。
- RH 結論を出さない。

---

## 12. Green 判定

Green-A 条件:

1. existing right source summand の構造 adapter が exact。
2. same-height mirror source summand が exact に定義される。
3. source pair difference が Mellin-weighted amplitude mode difference と exact に一致。
4. modewise normSq transportで `normSq weight` factor が明示される。
5. finite mirror ray minus right ray が transformed amplitude mode sumとして exact。
6. `ZR - 1` が transformed amplitude part + mirror baseline residual に exact 分解される。
7. 可能なら normSq level の residual/interference 分解まで閉じる。
8. direct amplitude-Gap/ray-minus equality、RH、無限極限を主張しない。
9. `DkMath.RH` public import と roadmap を更新。
10. focused build, `lake build DkMath.RH`, repository standard tests, `git diff --check`, forbidden-word audit が Green。

Green 後は Layer 2 を続けるか common-baseline reachへ戻るかを再判定する。特に mirror baseline residual が既存 completed/source geometryで既に制御されていないかを先に監査し、機械的に Layer 2 へ進まないこと。
