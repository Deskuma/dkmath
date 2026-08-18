# CFZP-0013 — CFZP-006I top-edge weighted polarization 実装指示書

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
8a4883447badaddb0ef2bcda1f94ffadddcda4c9
Add: CFZP-0012: CFZP-006H top-edge Gram specialization / dual-quadraticization boundary
```

CFZP-006H 実装 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaTopEdgeGramSpecializationAudit
```

006H は full signed arithmetic Gram を actual symmetric rectangle top edge へ exact に specialization し、pointwise / integral に

```text
normSq(Source_X(topEdge u))
  = TotalSourceMass_X(topEdge u)
  = FullPairSum_X(topEdge u)
```

を閉じた。

一方 CFZP-005 の actual linear Euler projection は

```text
cfzpFiniteMellinSymmetricEulerDensity ε X W u
  := Im(TopMellinWeight(ε,W,u) * Source_X(topEdge u))
```

である。

CFZP-006I では、この quadratic mass と linear signed density を、**同じ weighted complex source から作る二つの nonnegative square masses の和差として exact に接続する**。

---

# 1. 006H signed half-width の監査訂正

006H 指示書では `TopHalfWidth = 1/2 - σ` に対して、可能なら positivity を得る、と書いた箇所があった。

しかし既存 rectangle contract では `W.rectangle.hσ` から

```text
1/2 <= W.rectangle.σ
```

が得られ、006H が採用した

```text
cfzpTopEdgeHalfWidth W := 1/2 - W.rectangle.σ
```

は **signed half-width** であり、一般に非正である。

これは実装ミスではない。既存 oriented interval

```text
W.rectangle.σ .. (1 - W.rectangle.σ)
```

の向きを保存するための正しい選択である。

006I ではこの signed half-width の positivity を要求しない。

必要なら補助量として

```text
positiveHalfWidth := W.rectangle.σ - 1/2
```

を別名で置いてよいが、006H の `cfzpTopEdgeHalfWidth` の意味を変更しないこと。

---

# 2. 今回の数学的核心

top-edge point `u` で略記する。

```text
w := pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u
S := cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
       (pascalSymmetricRectangleTopEdge u W.rectangle.T)
A := w * S
```

CFZP-005 の Euler density は

```text
EulerDensity = Im(A)
```

である。

ここで source orientation を明示するため

```text
D := -i * A
```

と置く。

すると exact に

```text
Re(D) = Im(A) = EulerDensity
```

となる。

さらに二つの square mass を

```text
Mplus  := normSq(D + 1)
Mminus := normSq(D - 1)
```

と置く。

どちらも pointwise に非負である。

一般の複素数 `D` に対する polarization identity から

```text
Mplus - Mminus = 4 * Re(D)
```

なので、今回

```text
Mplus - Mminus = 4 * EulerDensity
```

が exact に得られる。

同時に

```text
Mplus + Mminus = 2 * (normSq(D) + 1)
```

であり、`|-i| = 1` から

```text
normSq(D) = normSq(A)
```

さらに積の norm-square より

```text
normSq(A)
  = normSq(w) * normSq(S)
  = normSq(w) * TotalSourceMass_X(topEdge u)
  = normSq(w) * FullPairSum_X(topEdge u)
```

となる。

したがって同じ two-mass pair は

```text
sum  -> weighted quadratic source mass
 diff -> linear signed Mellin Euler density
```

を同時に保持する。

これが今回の load-bearing bridge である。

---

# 3. 新規 module

推奨 filename:

```text
lean/dk_math/DkMath/RH/CFBRC/
  CosmicFormulaZetaTopEdgeWeightedPolarizationAudit.lean
```

推奨 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaTopEdgeWeightedPolarizationAudit
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaTopEdgeGramSpecializationAudit
import Mathlib.Tactic
```

CFZP-005 は 006H 経由または直接 import で利用可能ならよい。

`DkMath/RH.lean` に public import を追加する。

---

# 4. Gate A — actual weighted Euler complex source

CFZP-005 の density の `.im` を取る前の complex object を first-class にする。

推奨:

```lean
noncomputable def cfzpFiniteMellinSymmetricEulerComplexSource
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
    cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
      (pascalSymmetricRectangleTopEdge u W.rectangle.T)
```

最低限、次を exact に証明する。

```text
Im(ComplexSource) = cfzpFiniteMellinSymmetricEulerDensity ε X W u
```

向きは実装しやすい方でよい。

さらに既存 theorem を使って source を actual finite symmetric Euler rate へ fold してよい。

```text
ComplexSource
  = TopMellinWeight * pascalCenteredXiPrimeSideFiniteSymmetricEulerRate(...)
```

これは rename-only ではなく既存 source equality の direct reuse とする。

---

# 5. Gate B — deoriented weighted source

horizontal/top projection の imaginary part を real interaction coordinate として扱うため、deoriented source を定義する。

推奨:

```lean
noncomputable def cfzpFiniteMellinSymmetricEulerDeorientedSource
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℂ :=
  -Complex.I * cfzpFiniteMellinSymmetricEulerComplexSource ε X W u
```

load-bearing theorem:

```text
Re(DeorientedSource) = cfzpFiniteMellinSymmetricEulerDensity ε X W u
```

factor / sign は Lean に決めさせること。

また `-i` は unit modulus なので

```text
normSq(DeorientedSource) = normSq(ComplexSource)
```

も exact に閉じる。

この deorientation は既存 whole-surface audit の orientation convention と整合するが、legacy quadraticization object と同一視しない。

---

# 6. Gate C — weighted quadratic mass と 006H FullPairSum

同じ weighted source の quadratic mass を明示する。

推奨:

```lean
noncomputable def cfzpFiniteMellinSymmetricEulerWeightedQuadraticMass
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  Complex.normSq
    (cfzpFiniteMellinSymmetricEulerDeorientedSource ε X W u)
```

まず pointwise nonnegative:

```text
0 <= WeightedQuadraticMass
```

次に exact factorization:

```text
WeightedQuadraticMass
  = normSq(TopMellinWeight) *
      cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo X (topEdge u)
```

さらに 006D / 006H を使って

```text
WeightedQuadraticMass
  = normSq(TopMellinWeight) *
      cfzpCanonicalFunctionalReflectionFullPairSumUpTo X (topEdge u)
```

まで閉じる。

この theorem が、006H の quadratic source mass と 005 の actual Mellin weight の最初の exact multiplicative bridge になる。

### 注意

`WeightedQuadraticMass` を `CompletionRemainder`、`RectangleBackground`、`TopZetaMismatchScalar`、または既存 amplitude Gap と呼ばない。

---

# 7. Gate D — two nonnegative polarized masses

DeorientedSource から二つの square mass を定義する。

推奨:

```lean
noncomputable def cfzpFiniteMellinSymmetricEulerPolarizedPlusMass
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  Complex.normSq
    (cfzpFiniteMellinSymmetricEulerDeorientedSource ε X W u + 1)

noncomputable def cfzpFiniteMellinSymmetricEulerPolarizedMinusMass
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  Complex.normSq
    (cfzpFiniteMellinSymmetricEulerDeorientedSource ε X W u - 1)
```

両方の pointwise nonnegative theorem を証明する。

```text
0 <= PolarizedPlusMass
0 <= PolarizedMinusMass
```

ここでは interval orientation に依存しない。

---

# 8. Gate E — exact polarization decomposition

必要なら先に一般補題を local theorem として置く。

概念形:

```text
normSq(z + 1) - normSq(z - 1) = 4 * z.re
normSq(z + 1) + normSq(z - 1) = 2 * (normSq z + 1)
```

Mathlib に適切な既存 lemma があれば再利用してよい。

これを DeorientedSource に適用し、load-bearing theorem を閉じる。

### difference channel

```text
PolarizedPlusMass - PolarizedMinusMass
  = 4 * cfzpFiniteMellinSymmetricEulerDensity ε X W u
```

同値な recovery theorem も欲しい。

```text
cfzpFiniteMellinSymmetricEulerDensity ε X W u
  = (PolarizedPlusMass - PolarizedMinusMass) / 4
```

### sum channel

```text
PolarizedPlusMass + PolarizedMinusMass
  = 2 * (WeightedQuadraticMass + 1)
```

可能なら左右個別にも

```text
PolarizedPlusMass
  = WeightedQuadraticMass + 1 + 2 * EulerDensity

PolarizedMinusMass
  = WeightedQuadraticMass + 1 - 2 * EulerDensity
```

を閉じる。

この形は CF2D / ThreeElement の plus/minus whole と同型の algebraic pattern だが、既存一般 Core との definitional equality は主張しない。

---

# 9. Gate F — balance/collision surface

今回の構造上もっとも重要な pointwise balance theorem を明示する。

```text
PolarizedPlusMass = PolarizedMinusMass
  <-> cfzpFiniteMellinSymmetricEulerDensity ε X W u = 0
```

これは two-mass balance が linear Mellin Euler projection の zero と exact に一致することを意味する。

ただし次を絶対に主張しない。

```text
EulerDensity = 0 <-> Source = 0
EulerDensity = 0 <-> zeta zero
PolarizedPlusMass = PolarizedMinusMass <-> Re(s) = 1/2
```

projection の imaginary component が zero であることと complex source 自身が zero であることは別である。

必要なら frontier marker を追加する。

```lean
inductive CfzpWeightedPolarizationBalanceToSourceZeroGap : Prop
  | noExactComplexSourceZeroIdentificationProvided
```

---

# 10. Gate G — 006H Gap marker を実質的に閉じる意味

006H には

```lean
CfzpTopEdgeQuadraticMassToLinearMellinProjectionGap
```

があり、`noExactPolarizationBridgeProvided` を記録している。

006I が Green になれば、この marker 自体を削除・変更する必要はない。006H checkpoint の歴史的 boundary として残してよい。

代わりに 006I の theorem surface が

```text
normSq(Source)
  -> weighted normSq(Source)
  -> polarized plus/minus masses
  -> difference
  -> actual CFZP-005 Euler density
```

を exact に閉じることで、その frontier が後続 module で解消されたことを示す。

---

# 11. Optional Gate H — positive-direction half-interval masses

pointwise Gate がきれいに閉じた後、Lean API 上安価なら actual half-interval projectionまで進めてよい。

既存 rectangle では

```text
1/2 <= W.rectangle.σ
```

なので、**非負 mass の積分には positive orientation**

```text
(1/2) .. W.rectangle.σ
```

を使う。

概念的に

```text
PlusHalfMass  := ∫_(1/2)^σ PolarizedPlusMass(u) du
MinusHalfMass := ∫_(1/2)^σ PolarizedMinusMass(u) du
```

とする。

integrability が clean に得られる場合のみ、

```text
0 <= PlusHalfMass
0 <= MinusHalfMass
```

を証明してよい。

一方 CFZP-005 / CS38 の projection は oriented half interval

```text
σ .. (1/2)
```

を使うため、符号反転を正確に処理すると概念的に

```text
∫_σ^(1/2) EulerDensity(u) du
  = (MinusHalfMass - PlusHalfMass) / 4
```

となる。

この integrated theorem は **optional** とする。pointwise polarization を無理に重くしない。

TopZetaMismatchScalar 全体には completed / Gamma channel も含まれるので、Euler half integralだけを TopZetaMismatchScalar と同一視しない。

---

# 12. 今回閉じてはいけないもの

CFZP-006I では以下を禁止する。

- `PolarizedPlusMass` または `PolarizedMinusMass` を `SourceBig / SourceGap` と命名すること
- `WeightedQuadraticMass = CompletionRemainder`
- `WeightedQuadraticMass = RectangleBackground`
- `WeightedQuadraticMass = TopZetaMismatchScalar`
- Euler density zero から complex source zero を導くこと
- Euler density zero から zeta zero / critical-line statement を導くこと
- plus/minus mass の大小関係を無仮定で主張すること
- off-diagonal pair sum の符号主張
- legacy continuous quadraticization との rename-only equality
- infinite Euler product
- new `Complex.arg`
- new global `Complex.log` branch
- `sorry` / `admit` / `axiom` / `native_decide`

---

# 13. 成功条件

最低限、次が Green なら CFZP-006I 完了とする。

```text
1. actual TopMellinWeight * functional-reflection source の complex object が first-class
2. その imaginary part = CFZP-005 Euler density
3. -i deorientation 後の real part = Euler density
4. deorientation が normSq を保存
5. WeightedQuadraticMass >= 0
6. WeightedQuadraticMass = normSq(weight) * TotalSourceMass
7. WeightedQuadraticMass = normSq(weight) * FullPairSum
8. polarized plus/minus masses が pointwise nonnegative
9. plus - minus = 4 * EulerDensity
10. plus + minus = 2 * (WeightedQuadraticMass + 1)
11. plus = minus iff EulerDensity = 0
12. DkMath.RH public import
13. target module build Green
14. lake build DkMath.RH Green
15. nested ./lean-build.sh Green
16. nested ./lean-test.sh Green
17. git diff --check Green
18. 新規 module に sorry / admit / axiom / native_decide なし
```

---

# 14. 次 Gate への判断材料

006I が Green になれば、次は **006J completed/Gamma/Euler channel polarization + oriented half-integral audit** を検討する。

006I は Euler channel だけで

```text
positive weighted quadratic pair
  -> exact difference
  -> linear signed Euler density
```

を閉じる。

006J では同じ algebraic device を completed mirror channel と Gamma mirror channelにも適用できるか監査し、三 channel の density sum

```text
cfzpProjectedMirrorScalarDensity
```

を nonnegative square-mass pairs の signed combinationとして表す。

その後、`σ .. 1/2` の oriented half integralと既存

```text
TopZetaMismatchScalar
  = (1 / π) * ∫ projectedMirrorScalarDensity
```

を組み合わせる。

ここでも rectangle completion remainder との identification は別 Gate とし、positive-direction masses と oriented contour sign を混同しないこと。
