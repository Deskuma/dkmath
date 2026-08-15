# CFZP-0006 — CFZP-006B source interaction classification 実装指示書

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
c3de62fe0fafc34777ad85c4ad735c6f1de10d1f
Add: CFZP-0005: CFZP-006 source completion geometry audit
```

CFZP-006 実装 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaSourceCompletionGeometryAudit
```

CFZP-006 は次を exact に閉じている。

```text
functional reflection
  = cycle displacement + same-height mirror

finite canonical functional source
  = cycle displacement source + same-height mirror source

Mellin symmetric Euler density
  = cycle displacement density + same-height mirror density

CompletionRemainder
  = RectangleBackground - TopZetaMismatchScalar
  = RadialContactDeficit / π
  = FixedRadialSecondMoment - IndependentCompleteSourceReal
```

また、`CompletionRemainder ≥ 0` は主張せず、radial deficit との符号同値だけを提供している。

今回の CFZP-006B は、この `CompletionRemainder` の source-side algebraic type を確定する。

---

# 1. 監査結論 — 現時点では genuine Gap へ昇格しない

既存 CS25:

```text
PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit
```

には public theorem

```lean
pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_zeroCutoff_deficit_sub_interaction
```

があり、概念的に

```text
G_X = G_0 - I_X
```

を与える。

ここで

```text
G_X = finite radial contact deficit
I_X = aggregate ray interaction energy
```

である。

CS25 の interaction density は

```text
2 * Re Z
```

であり、符号不定である。

さらに CS26 はこの interaction の finite phase primitive を閉じているが、interaction sign provider は与えていない。

従って CFZP-006 で得た

```text
CompletionRemainder = G_X / π
```

は、現時点では positive quadratic Gap ではなく

```text
zero-cutoff baseline - signed interaction
```

という affine signed observable として分類するのが正しい。

今回ここを Lean theorem として固定する。

---

# 2. 今回の目的

今回の最重要 theorem は概念的に

```text
CompletionRemainder
  = SourceZeroCutoffBaseline
    - SourceInteraction
```

である。

さらに既存 CS24 / CS25 の plus / minus positive energies を使い、

```text
SourceInteraction
  = SourcePlusMass - SourceMinusMass
```

を exact に閉じる。

従って

```text
CompletionRemainder
  = SourceZeroCutoffBaseline
    + SourceMinusMass
    - SourcePlusMass
```

を得る。

この形により、rectangle remainder が現時点で

```text
nonnegative Gap
```

ではなく

```text
baseline + positive mass - positive mass
```

という signed polarization remainder であることを明確化する。

---

# 3. 新規 module

推奨 filename:

```text
lean/dk_math/DkMath/RH/CFBRC/
  CosmicFormulaZetaSourceInteractionClassificationAudit.lean
```

推奨 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaSourceInteractionClassificationAudit
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaSourceCompletionGeometryAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit
import Mathlib.Tactic
```

新しい解析依存や zeta zero theorem は追加しない。

---

# 4. 正規化 source quantities

以下の意味を持つ CFZP 名を用意する。

名前は repository style に合わせて軽微に変更してよいが、意味は変えない。

## 4.1 zero-cutoff baseline

```lean
noncomputable def cfzpFiniteSourceZeroCutoffBaseline
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 / Real.pi
```

これは `X = 0` の radial deficit を `π` で正規化したもの。

`RectangleBackground` を直接 baseline と定義しない。

## 4.2 normalized interaction

```lean
noncomputable def cfzpFiniteSourceInteraction
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X / Real.pi
```

interaction は signed であり、`Mass` や `Gap` と命名しない。

## 4.3 normalized plus / minus masses

```lean
noncomputable def cfzpFiniteSourcePlusMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  pascalCenteredXiPrimeSideAggregateRayPlusEnergy ε W X /
    (2 * Real.pi)

noncomputable def cfzpFiniteSourceMinusMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X /
    (2 * Real.pi)
```

これらは既存 positive whole energies の正規化である。

---

# 5. Gate A — CompletionRemainder = baseline - interaction

CFZP-006 の theorem

```lean
cfzpFiniteRectangleCompletionRemainder_eq_radialDeficit_div_pi
```

と CS25 の theorem

```lean
pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_zeroCutoff_deficit_sub_interaction
```

を使い、CS30 safety / integrability assumptions の下で

```text
cfzpFiniteRectangleCompletionRemainder ε W X
  = cfzpFiniteSourceZeroCutoffBaseline ε W
    - cfzpFiniteSourceInteraction ε W X
```

を証明する。

これが load-bearing theorem。

定義展開だけで rectangle side を変形して作らず、既存 `G_X` theorem を通すこと。

---

# 6. Gate B — interaction = plus mass - minus mass

既存 CS25:

```lean
pascalCenteredXiPrimeSideAggregateRayPlusEnergy_eq_common_add_interaction
pascalCenteredXiPrimeSideAggregateRayMinusEnergy_eq_common_sub_interaction
```

を使い、

```text
cfzpFiniteSourceInteraction ε W X
  = cfzpFiniteSourcePlusMass ε W X
    - cfzpFiniteSourceMinusMass ε W X
```

を exact に証明する。

同値な係数形でもよいが、`π` と `2` は Lean に決めさせる。

この theorem は common carrier が差分から exact cancellation することを CFZP source terminology で固定する。

---

# 7. Gate C — CompletionRemainder の canonical signed polarization form

Gate A/B から

```text
cfzpFiniteRectangleCompletionRemainder ε W X
  = cfzpFiniteSourceZeroCutoffBaseline ε W
    + cfzpFiniteSourceMinusMass ε W X
    - cfzpFiniteSourcePlusMass ε W X
```

を証明する。

この theorem は今回の最終分類 theorem とする。

必要なら別 theorem として

```text
CompletionRemainder + SourcePlusMass
  = SourceZeroCutoffBaseline + SourceMinusMass
```

という balanced form も追加してよい。

ただしこの balanced form を `Big = Body + Gap` と命名しない。

---

# 8. Gate D — positive whole masses

既存 theorem を再利用して

```text
0 ≤ cfzpFiniteSourcePlusMass ε W X
0 ≤ cfzpFiniteSourceMinusMass ε W X
```

を `hε : 0 < ε` の下で証明する。

必要なら `Real.pi_pos` を利用する。

ここから `CompletionRemainder ≥ 0` を導いてはいけない。

`baseline + nonnegative - nonnegative` の符号は一般には決まらない。

---

# 9. Gate E — common-carrier cancellation の CFZP wrapper

可能なら次も追加する。

```text
SourcePlusMass - SourceMinusMass = SourceInteraction
```

に加えて、CS25 の aggregate common energy を正規化した

```text
SourceCommonMass
```

を薄く定義し、

```text
SourcePlusMass  = SourceCommonMass + SourceInteraction / 2
SourceMinusMass = SourceCommonMass - SourceInteraction / 2
```

を exact に閉じる。

これは optional ではあるが、実装が素直なら追加してよい。

ただし今回の load-bearing Gate は A/B/C/D である。

---

# 10. 最重要区別 — CFZP-004 amplitude plus/minus と CS24/25 ray energiesを混同しない

CFZP-004 には

```text
cfzpAggregateMirrorPlusWholeUpTo
cfzpAggregateMirrorMinusWholeUpTo
```

がある。

CS24/25 には

```text
pascalCenteredXiPrimeSideAggregateRayPlusEnergy
pascalCenteredXiPrimeSideAggregateRayMinusEnergy
```

がある。

これらは同じ object ではない。

前者は finite canonical prime-power amplitude ledger。

後者は normalized geometric ray state を contour-height 方向へ積分した positive energy。

従って今回、両者の equality を仮定・定義してはならない。

exact bridge が将来得られるまでは別 observable として保持する。

---

# 11. 今回確定させる obstruction

今回の Green 結果が得られた場合、次を source classification として記録する。

```text
CompletionRemainder
  = baseline - signed interaction
  = baseline + positive minus-mass - positive plus-mass
```

従って現時点では

```text
CompletionRemainder = SourceGap
0 ≤ CompletionRemainder
```

を主張できない。

必要なら module 末尾に named frontier を置いてよい。

例:

```lean
inductive CfzpSourcePositiveGapIdentificationGap : Prop
  | noQuadraticNonnegativeSourceGapProvider
```

これは「不可能 theorem」ではなく、現実装に provider が無いことを記録するだけ。

---

# 12. 次の phase への準備 — CFZP-006C

CFZP-006B が Green なら、次は rectangle remainder を無理に Gap 化するのではなく、CFZP-004 の positive mode Gap から **induced quadratic companion projection** を構成する。

次段で監査する対象は二種類の interference。

## 12.1 mode 内 interference

CFZP-006 で

```text
FunctionalReflectionDifference
  = CycleDisplacement + SameHeightMirrorDifference
```

を得た。

quadraticize すると概念的に

```text
|FunctionalDifference|²
  = |CycleDisplacement|²
    + |SameHeightMirrorDifference|²
    + 2 Re(CycleDisplacement * conj(SameHeightMirrorDifference))
```

となる。

same-height term は CFZP-004 の carrier-weighted positive mirror Gap に exact 接続できる。

cycle term は非負。

cross term は signed。

## 12.2 mode 間 interference

linear PHZ source は finite sum なので

```text
|Σ mode|²
```

には cross-mode term が出る。

```text
|Σ mode|² = Σ |mode|²
```

とはしない。

さらに PHZ coefficient は `w_q` なので total source を square すると diagonal coefficient は `w_q²` になる。

CFZP-003 positive aggregate は `w_q * Gap_q` であるため、ここには **weight-degree mismatch** もある。

これを次の 006C で正面から扱う。

今回 006B ではそこまで進まない。

---

# 13. Firewall

今回禁止:

- `CompletionRemainder` を `Gap` に rename する。
- `CompletionRemainder ≥ 0` を仮定する。
- radial deficit の符号を zero-side / RH-equivalent theorem から持ち込む。
- CFZP-004 amplitude plus/minus と CS24/25 integrated ray plus/minus を同一視する。
- `Complex.normSq` を finite sum に分配する。
- quadratic Gram form へ進む。
- completed zeta / standard zeta の新しい zero theorem を使う。
- infinite Euler product / limit exchange を導入する。
- `Complex.arg` や global `Complex.log` branch を追加する。
- `sorry` / `admit` / `axiom` を追加する。
- CFZP-007 へ進む。

---

# 14. Validation

最低限:

```text
lake build DkMath.RH.CFBRC.CosmicFormulaZetaSourceInteractionClassificationAudit
lake build DkMath.RH
./lean-build.sh
./lean-test.sh
git diff --check
```

新規 module に

```text
sorry
admit
axiom
```

が無いことを確認する。

Green 後にのみ `DkMath/RH.lean` へ public import を追加する。

---

# 15. Stop condition

今回は次までで停止する。

```text
CompletionRemainder
  = normalized zero-cutoff baseline
    - normalized signed interaction

normalized signed interaction
  = normalized plus mass
    - normalized minus mass

CompletionRemainder
  = baseline + minus mass - plus mass

0 ≤ plus mass
0 ≤ minus mass
```

ここまで Green にして push する。

quadratic companion / Gram / cross-mode interference は次回 CFZP-006C とする。
