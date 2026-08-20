# CFZP-0041 / CFZP-014

## functional-reflection prime-ray canonical aggregate transport audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-011: same-height mirror/source mode transform — Green-A
- CFZP-012: mirror-baseline functional-reflection height-reversal audit — Green-A
- CFZP-013: weight-reversal conjugation and ray self-recurrence — Green-A
- CFZP-0040: branch-free positive-mode conjugation reinforcement — Green-A

本段では、CFZP-013 で prime ごとに現れた
`cfzp012FunctionalReflectionPrimePowerRayAmplitude` を、既存の canonical
prime-power support / shadow cost へ有限 exact に再集約する。

目的は、013 の `functionalReflectionPart` が新しい未知 source ではなく、
CFZP-005 の

`cfzpCanonicalFunctionalReflectionLinearSourceUpTo`

の right-edge height-reversed specializationを、Mellin weight と既存の
`log p` prime weight を伴って再構成していることを確定することである。

ただし CFZP-005 / CS38 の projected mirror density は top edge の observable
であり、013 の functional part は reversed right edge の observable である。
この edge mismatch を rename equality で消してはならない。

本段では有限 aggregate transport だけを閉じ、right-edge から top-edge への
contour relocation、無限 cutoff exchange、baseline collapse、RH は導入しない。

---

## 1. 新規 module

推奨:

`DkMath.RH.CFBRC.CosmicFormulaZetaFunctionalReflectionPrimeRayCanonicalAggregateTransportAudit`

file:

`lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaFunctionalReflectionPrimeRayCanonicalAggregateTransportAudit.lean`

最低 import 候補:

- `DkMath.RH.CFBRC.CosmicFormulaZetaWeightReversalConjugationSelfRecurrenceAudit`
- `DkMath.RH.CFBRC.CosmicFormulaZetaMellinSourceProjection`
- `DkMath.RH.CFBRC.PascalCenteredXiPrimeSidePrimePowerRayAudit`
- `DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit`
- `Mathlib.Tactic`

既存 support reindex theorem を優先し、canonical prime-power support や
prime-power pair support の新しい複製を作らない。

---

## 2. Gate A — prime-weighted functional-reflection ray aggregate

013/012 の per-prime finite ray

```lean
cfzp012FunctionalReflectionPrimePowerRayAmplitude ε W X p t
```

を既存 prime coordinate support 上で `Real.log p` により aggregate した量を
first-class にする。

推奨 shape:

```lean
noncomputable def cfzp014AggregateFunctionalReflectionPrimeRayAmplitude
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
    (Real.log (p : ℝ) : ℂ) *
      cfzp012FunctionalReflectionPrimePowerRayAmplitude ε W X p t
```

係数は source-side canonical fold と整合するよう `ℂ` coercion を明示する。

---

## 3. Gate B — pair support への finite reindex

`cfzp012FunctionalReflectionPrimePowerRayAmplitude` は one base prime `p` の
positive exponent support 上の和である。これを展開し、既存
`pascalPrimePowerPairSupportUpTo X` へ exact に reindex する。

狙う中間形は概念的に

```text
Σ p∈PrimeSupport(X) log p · Σ k∈ExponentSupport(X,p)
  weight(t) · FunctionalReflectionMode(p^(k+1), sR(-t))

= Σ (p,k)∈PrimePowerPairSupport(X)
    log p · weight(t) · FunctionalReflectionMode(p^(k+1), sR(-t))
```

である。

CS14 の既存 product/pair support rewrite が直接利用できるなら再証明しない。
必要なら support membership の exact equivalence を最小限 adapter として出す。

ここは有限 Finset algebra のみとする。

---

## 4. Gate C — canonical prime-power support / shadow cost への fold

pair support から canonical prime-power support へ既存 bijection / image theorem を
使って折り畳み、`canonicalPrimePowerShadowCost q = log p` を再利用する。

最終的に次の exact theorem を第一目標とする。

```text
AggregateFunctionalReflectionPrimeRayAmplitude(ε,W,X,t)

= weight(node(t))
  * cfzpCanonicalFunctionalReflectionLinearSourceUpTo
      X (sR(-t))
```

Lean shape は例えば:

```lean
cfzp014AggregateFunctionalReflectionPrimeRayAmplitude ε W X t =
  pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalCenteredXiPrimeSideModePhaseNode W t) *
    cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
      (pascalSymmetricRectangleRightEdge W.rectangle.σ (-t))
```

とする。

`weight(node t)` は prime/exponent に依存しないので有限和の外へ出してよい。

重要:

- `canonicalPrimePowerShadowCost` を `Real.log q` と誤認しない。
- `q = p^j` では shadow cost は `log p` である既存 canonical fold を使う。
- prime-power label の重複を手作業で潰さず、既存 injective/reindex API を使う。

---

## 5. Gate D — CFZP-005 finite symmetric Euler source へ接続

CFZP-005 の既存 theorem

```lean
cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_finiteSymmetricEulerRate
```

を使って Gate C の右辺を

```text
weight(node(t))
* pascalCenteredXiPrimeSideFiniteSymmetricEulerRate X (sR(-t))
```

へ exact に rewrite する theorem を出す。

この段階で、013 の functional part が **既存 finite symmetric Euler source の
reversed-right-edge specialization** であることを確定する。

---

## 6. Gate E — self-recurrence aggregate companion

可能なら、CFZP-013 の per-prime mirror baseline residual decomposition を
`log p` prime weight で aggregate する companion surface を追加する。

ただし対象は complex amplitude level の有限和に留める。

概念形:

```text
Σ_p log p · (ZM_p(t) - 1)

= AggregateFunctionalReflectionPrimeRayAmplitude(t)
  + Σ_p log p · (conj(ZR_p(t)) - 1)
  + skew(t) · Σ_p log p · BareReversedModeSum_p(t)
```

ここで baseline `1` は per-prime residual の内部にあるため、aggregate 後には
`Σ_p log p` の baseline mass が生じる。これを `1` のまま残したり、既存
common-energy baseline と rename してはならない。

この Gate は実装が自然なら行う。Gate A〜D が本段の必須 core。

---

## 7. Gate F — top-edge CS38 との edge mismatch を first-class にする

CFZP-005 の

```lean
cfzpFiniteMellinSymmetricEulerDensity
cfzpFiniteMellinSymmetricEulerDensity_eq_cs38
cfzpProjectedMirrorScalarDensity
```

は `pascalSymmetricRectangleTopEdge u W.rectangle.T` を使う top-edge observable。
一方 Gate C/D は

```lean
pascalSymmetricRectangleRightEdge W.rectangle.σ (-t)
```

を使う reversed-right-edge observable。

この二つを同一視しない。

本段で既存 theorem から exact edge relocation が見つからなければ、例えば

```lean
inductive Cfzp014FunctionalReflectionRightToTopEdgeTransportGap : Prop
  | noExactRightEdgeToTopEdgeFunctionalReflectionTransportProvided
```

を置く。

roadmap には少なくとも次を明記する。

```text
CFZP-013 functional-reflection per-prime ray:
  canonical finite aggregation: CLOSED

canonical functional-reflection source:
  finite symmetric Euler rate identification: CLOSED

right-edge reversed source -> CS38 top-edge source:
  OPEN unless an existing exact contour transport theorem is genuinely supplied
```

---

## 8. 禁止事項 / firewall

本段では以下を導入しない。

- 新しい `Complex.arg`
- branch-sensitive phase observable
- 新しい global `Complex.log` convention
- infinite Euler product
- infinite cutoff exchange
- unsupported sum/integral exchange
- right-edge source と top-edge source の rename equality
- amplitude Gap と ray-minus whole の直接 equality
- common-baseline reach witness
- RH または RH-equivalent provider

既存 module 内に legacy `Complex.arg` が存在しても、本段の新規 theorem proof に
持ち込まない。

---

## 9. public import / roadmap

Green の場合:

- `DkMath/RH.lean` に新規 module を公開 import
- `0000-CFZP-roadmap.md` に CFZP-014 を追記

分類は Gate A〜D が exact に閉じれば Green-A としてよい。
Gate F の edge relocation marker は、014 の core failure ではなく次 frontier の
sharp classification として扱う。

---

## 10. 検証

最低限:

```bash
lake env lean lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaFunctionalReflectionPrimeRayCanonicalAggregateTransportAudit.lean
lake build DkMath.RH
git diff --check
```

加えて新規/変更箇所について:

- `sorry`
- `admit`
- `axiom`
- `native_decide`
- 新規 `Complex.arg`

を監査する。

ユーザー環境の local Green を authoritative とする。
