# CFZP-0012 — CFZP-006H top-edge Gram specialization / dual-quadraticization boundary 実装指示書

## 0. 作業対象

Repository:

```text
Deskuma/dkmath
```

Working branch:

```text
wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0
```

この指示書作成直前に確認した Green checkpoint:

```text
e6f908705a75147d6078237cceca8514e907d50b
Add: CFZP-0011: CFZP-006G full signed Gram zero-width limit recovery
```

CFZP-006G は一般 Analysis 層で

```text
Mellin multiplier
  -> Gram kernel
  -> finite Gram quadratic form
  -> real Gram energy
```

の `ε -> 0+` 極限を閉じ、CFZP family へ instantiate して

```text
FullSignedGramEnergy(ε,X,s)
  -- ε -> 0+ -->
TotalSourceMass_X(s)
  = FullPairSum_X(s)
```

を exact に得た。

今回の CFZP-006H では zero-width limit から一旦離れ、**実際の symmetric rectangle top edge 全体へ full signed Gram を specialization する**。

同時に、既存 `PascalCenteredXiPrimeSideQuadraticizationAudit` の continuous quadraticization と今回の CFZP arithmetic signed-node Gram が同じ object ではないことを明示し、誤った同一視を防ぐ。

---

# 1. 今回の数学的核心

symmetric rectangle の top edge を

```text
TopEdge(u,T)
```

と書く。

critical center の top point を

```text
s0 = TopEdge(1/2,T)
```

とし、rectangle の half width を

```text
h = 1/2 - σ
```

とする。

すると horizontal shift は exact に

```text
cfzpHorizontalRealShift s0 τ
  = TopEdge(1/2 + τ, T)
```

であり、`τ ∈ [-h,h]` は `u ∈ [σ,1-σ]` と同じ top edge 全体を走る。

従って CFZP-006F の full Gram energy は、`ε = h` としたとき exact に

```text
FullSignedGramEnergy(h,X,s0)

= (2h)^(-1) * ∫_{u=σ}^{1-σ}
    normSq(Source_X(TopEdge(u,T))) du
```

へ書き直せる。

さらに CFZP-005 の source theorem により

```text
Source_X(s)
  = pascalCenteredXiPrimeSideFiniteSymmetricEulerRate X s
```

なので、これは actual finite functional-reflection Euler source の top-edge quadratic mass average である。

また各 top-edge point では CFZP-006D から

```text
normSq(Source_X(s))
  = TotalSourceMass_X(s)
  = FullPairSum_X(s)
```

である。

今回の checkpoint ではここまでを exact に閉じる。

---

# 2. 新規 module

推奨 filename:

```text
lean/dk_math/DkMath/RH/CFBRC/
  CosmicFormulaZetaTopEdgeGramSpecializationAudit.lean
```

推奨 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaTopEdgeGramSpecializationAudit
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaFullSignedGramLimitRecoveryAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaMellinSourceProjection
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideQuadraticizationAudit
import Mathlib.Tactic
```

`DkMath/RH.lean` に public import を追加する。

一般 Analysis module `MellinQuadraticGramLimit` の `DkMath/Analysis.lean` public import は今回の必須事項ではない。既存 library 方針に合わせて必要なら別途追加してよい。

---

# 3. Gate A — top-edge center / half-width geometry

rectangle window `W : PascalCenteredXiResidueTransportWindow` に対し、概念的に次を定義する。

```text
TopCenter(W)
  := pascalSymmetricRectangleTopEdge (1/2) W.rectangle.T

TopHalfWidth(W)
  := 1/2 - W.rectangle.σ
```

実名は既存 naming に合わせてよい。

既存 rectangle hypotheses から可能なら first-class theorem として

```text
0 < TopHalfWidth(W)
```

を得る。

次を exact に証明する。

```text
cfzpHorizontalRealShift (TopCenter W) τ
  = pascalSymmetricRectangleTopEdge
      (1/2 + τ) W.rectangle.T
```

endpoint も安価なら記録する。

```text
shift(TopCenter,-TopHalfWidth)
  = TopEdge(σ,T)

shift(TopCenter,+TopHalfWidth)
  = TopEdge(1-σ,T)
```

証明では既存 `pascalSymmetricRectangleTopEdge` 定義と `cfzpHorizontalRealShift` のみを使う。

---

# 4. Gate B — full Gram の top-edge reparameterization

次の top-edge energy wrapper を置いてよい。

```text
cfzpTopEdgeFunctionalReflectionQuadraticEnergy W X
  := cfzpCanonicalFunctionalReflectionFullSignedGramEnergy
       (TopHalfWidth W) X (TopCenter W)
```

load-bearing theorem は top-edge 全体への exact reparameterization。

```text
cfzpTopEdgeFunctionalReflectionQuadraticEnergy W X

= (2 * TopHalfWidth W)^(-1) *
    ∫ u in W.rectangle.σ..(1 - W.rectangle.σ),
      Complex.normSq(
        cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
          (pascalSymmetricRectangleTopEdge u W.rectangle.T))
```

証明は 006F の

```lean
cfzpCanonicalFunctionalReflectionFullSignedGramEnergy_eq_shiftedSource_integral
```

を使い、`u = 1/2 + τ` の interval reparameterization だけを行う。

Mathlib の interval-integral translation API の exact theorem 名は現行 v4.33.0 に合わせて選ぶこと。

新しい積分理論は作らない。

---

# 5. Gate C — actual finite symmetric Euler rate への fold

CFZP-005 の既存 theorem

```lean
cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_finiteSymmetricEulerRate
```

を pointwise に使い、Gate B を

```text
cfzpTopEdgeFunctionalReflectionQuadraticEnergy W X

= (2h)^(-1) * ∫_{σ}^{1-σ}
    normSq(
      pascalCenteredXiPrimeSideFiniteSymmetricEulerRate X
        (pascalSymmetricRectangleTopEdge u T)) du
```

へ exact に fold する。

ここで `h = TopHalfWidth W`、`T = W.rectangle.T`。

これは **finite Euler functional-reflection source の quadratic top-edge average** である。

completed / Gamma / elementary correction をこの source に混ぜない。

---

# 6. Gate D — 006D prime-power pair ledger への pointwise / integral bridge

各 top-edge pointで cheap な theorem を用意する。

```text
normSq(Source_X(TopEdge(u,T)))
  = cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo X (TopEdge(u,T))

cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo X (TopEdge(u,T))
  = cfzpCanonicalFunctionalReflectionFullPairSumUpTo X (TopEdge(u,T))
```

後者は 006D theorem の向きを整えるだけでよい。

これを Gate B に入れて、可能なら

```text
cfzpTopEdgeFunctionalReflectionQuadraticEnergy W X

= (2h)^(-1) * ∫_{σ}^{1-σ}
    cfzpCanonicalFunctionalReflectionFullPairSumUpTo X
      (pascalSymmetricRectangleTopEdge u T) du
```

まで exact に閉じる。

これにより fixed top-edge width においても

```text
signed spectral Gram family
  <-> top-edge source normSq
  <-> prime-power ordered pair ledger
```

が同じ quadratic observable の三表現になる。

---

# 7. Gate E — diagonal / off-diagonal top-edge decomposition（推奨）

006D の

```text
FullPairSum = DiagonalPairSum + OffDiagonalPairSum
```

を top edge 上で積分し、安価なら normalized averages を定義する。

概念形:

```text
TopEdgeDiagonalAverage(W,X)
TopEdgeOffDiagonalAverage(W,X)
```

そして

```text
TopEdgeQuadraticEnergy
  = TopEdgeDiagonalAverage + TopEdgeOffDiagonalAverage
```

を exact に証明する。

`0 < TopHalfWidth W` を使えば diagonal average の非負性は証明してよい。

```text
0 <= TopEdgeDiagonalAverage
```

**OffDiagonalAverage の符号は主張しない。**

ordered-pair convention の factor 2 を追加しない。

---

# 8. Gate F — CFZP-005 linear Mellin source との境界

既存

```lean
cfzpFiniteMellinSymmetricEulerDensity
```

は top edge 上で概念的に

```text
Im(TopMellinWeight(u) * Source_X(TopEdge(u,T)))
```

という **linear signed projection** である。

今回得る top-edge energy は

```text
normSq(Source_X(TopEdge(u,T)))
```

の average であり、同じものではない。

この checkpoint では

```text
TopEdgeQuadraticEnergy = TopZetaMismatchScalar
```

や

```text
normSq(Source) = linear Mellin density
```

を絶対に置かない。

必要なら次の frontier marker を置く。

```lean
inductive CfzpTopEdgeQuadraticMassToLinearMellinProjectionGap : Prop
  | noExactPolarizationBridgeProvided
```

次 checkpoint ではこの gap を ± square-mass polarization で攻める予定。

---

# 9. Gate G — legacy continuous quadraticization との dual-axis boundary

今回 `PascalCenteredXiPrimeSideQuadraticizationAudit` を import する理由は、**同一視するためではなく差を first-class に監査するため**である。

既存 legacy quadraticization は概念的に

```text
RightEdgeNode(W,t)
  = centered(right-edge contour point)

VerticalAmplitude(W,X,t)
  = finite PHZ
    + archimedean correction
    + elementary correction

AggregatedBoxFeature(W,X,u)
  = ∫_{-T}^{T}
      RightEdgeNode(W,t)^2
      * exp(u * RightEdgeNode(W,t))
      * VerticalAmplitude(W,X,t) dt
```

である。

一方 CFZP current Gram は

```text
arithmetic spectral nodes = ±log q
finite functional-reflection PHZ source
horizontal shift of s
```

から作られている。

従って index semantics は

```text
legacy: contour/spectral node t -> centered complex node
CFZP:   arithmetic label q -> ±log q
```

であり、amplitude semantics も

```text
legacy: prime + archimedean + elementary vertical source
CFZP:   finite prime-power functional-reflection difference
```

と異なる。

今回、次のような equality を作らない。

```text
CFZP FullSignedGramEnergy
  = pascalCenteredXiPrimeSideQuadraticizationContinuousGramEnergy

CFZP signed node
  = pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode

CFZP source
  = pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude
```

exact adapter がまだ無いことを marker で記録してよい。

```lean
inductive CfzpArithmeticSignedGramToLegacyContinuousQuadraticizationGap : Prop
  | noExactDualFeatureIdentificationProvided
```

この marker は impossibility theorem ではない。

---

# 10. Firewall

今回も以下を禁止する。

- `TopEdgeQuadraticEnergy = CompletionRemainder`
- `TopEdgeQuadraticEnergy = RectangleBackground`
- `TopEdgeQuadraticEnergy = TopZetaMismatchScalar`
- `TopEdgeQuadraticEnergy = cfzpAggregateMirrorGapUpTo`
- `TopEdgeQuadraticEnergy = cfzpAggregateCarrierWeightedMirrorGapUpTo`
- legacy ContinuousGramEnergy との rename-only equality
- off-diagonal average の非負性
- source remainder の非負性
- `SourceBig / SourceBody / SourceGap` の premature naming
- infinite Euler product
- zero-set / RH conclusion
- `Complex.arg`
- 新しい global `Complex.log` branch
- `sorry` / `admit` / `axiom`

---

# 11. 成功条件

最低限、次が Green なら CFZP-006H 完了とする。

```text
1. top critical center と rectangle half-width が明示される
2. horizontal shift = actual top-edge coordinate が exact
3. FullSignedGramEnergy を full top-edge normSq integral へ exact reparameterize
4. source を finite symmetric Euler rate へ exact fold
5. top-edge normSq = TotalSourceMass = 006D FullPairSum を exact に接続
6. top-edge energy を FullPairSum integral として表せる
7. legacy continuous quadraticization との index/amplitude semantic difference を保持
8. linear Mellin density / TopZetaMismatchScalar と quadratic energy を同一視しない
9. DkMath.RH public import
10. target module build Green
11. lake build DkMath.RH Green
12. nested ./lean-build.sh Green
13. nested ./lean-test.sh Green
14. git diff --check Green
15. 新規 module に sorry / admit / axiom なし
```

Gate E の diagonal/off-diagonal top-edge decomposition は強く推奨するが、Lean API 上不自然に重い場合は次へ回してよい。

---

# 12. 次 Gate への判断材料

006H が Green になれば、次は **006I top-edge weighted polarization audit** を検討する。

中心課題は、CFZP-005 の linear signed Euler density

```text
Im(TopMellinWeight * Source)
```

を、同じ source object から作る二つの nonnegative square masses の差として exact に recover できるかである。

例えば適切な `±i` polarization を使えば概念的に

```text
|A + i|^2 - |A - i|^2
```

から `Im(A)` を回収できる。

ここで `A = TopMellinWeight * Source` と置けるなら、初めて

```text
positive quadratic masses
  -> polarization difference
  -> linear Mellin source density
```

という Cosmic Formula / ThreeElement 型の bridge が source projection 上に現れる。

ただし 006I で actual factor、符号、`2` / `4`、orientation を Lean に決めさせる。006H ではまだ polarization theorem を先取りしない。
