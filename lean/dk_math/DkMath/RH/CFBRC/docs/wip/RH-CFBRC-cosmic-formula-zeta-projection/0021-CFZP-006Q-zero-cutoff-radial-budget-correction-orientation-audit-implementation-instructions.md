# CFZP-0021 — CFZP-006Q zero-cutoff radial budget / correction orientation audit 実装指示書

## 0. 作業対象

Repository:

```text
Deskuma/dkmath
```

Working branch:

```text
wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0
```

この指示書作成直前の Green checkpoint:

```text
f97d8f03ae13a1ec1bb819f3fe5915d5f68a5fd0
Add: CFZP-0020: CFZP-006P zero-cutoff contact baseline public decomposition audit
```

直前 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaZeroCutoffContactBaselineAudit
```

006P で exact に得られた核心は次。

```text
ZeroCutoffBaseline
  = π * (FixedRadialSecondMoment - IndependentCorrectionSourceReal)
```

かつ

```text
IndependentCorrectionSourceReal
  = NormalizedArchimedeanContribution
    + NormalizedElementaryContribution
    + NormalizedTopContribution
```

さらに 006O / 006P から contact は

```text
AggregateRayInteractionEnergy(X)
  = ZeroCutoffBaseline
```

と exact に同値。

今回 CFZP-006Q では、ここをさらに一段整理して、

```text
π * FixedRadialSecondMoment
```

を **radial budget reference** として読み、

```text
π * CorrectionSource + AggregateRayInteractionEnergy
```

との exact balance に変換する。

重要:

- `FixedRadialSecondMoment` 自体は `W.circle_safe` により finite window radial `normSq` sum へ戻せるため、その非負性はこの module で安全に証明してよい。
- しかし Archimedean / Elementary / Top correction は既存 API 上では signed real/imag projections であり、componentwise positivity は既知ではない。
- interaction も signed であり、monotonicity / reach provider は既知ではない。
- したがって今回の目的は positivity を作ることではなく、**contact を radial budget equality として exact に固定し、残る quantitative dominance / reach frontier を明示すること**。

---

# 1. 現行 source で確認済みの API

## 1.1 residue transport window の circle safety

`PascalCenteredXiResidueTransportWindow` には public field

```lean
circle_safe : IsPascalCenteredXiBoundarySafeRadius R
```

がある。

## 1.2 fixed radial second moment

Module:

```text
DkMath.RH.CFBRC.PascalCenteredXiFixedSecondMomentDefectBridge
```

Public theorem:

```lean
pascalCenteredXiFixedRadialSecondMomentFunctional_eq_windowRadial
```

内容:

```text
FixedRadialSecondMomentFunctional R
  = pascalCriticalMirrorZeroWindowRadialSecondMoment R
```

boundary-safe radius の下で成立。

Window radial second moment の definition は

```text
Σ ρ in finite zero window,
  multiplicity(ρ) * normSq(ρ - criticalLineCenter)
```

なので finite sum nonnegativity から fixed radial reference の非負性を証明できる。

## 1.3 correction source components

`PascalCenteredXiPrimeSideSignAudit` の public definitions:

```lean
pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution
pascalCenteredXiMellinQuadraticNormalizedElementaryContribution
pascalCenteredXiMellinQuadraticNormalizedTopContribution
```

同 module は明示的に、prime / correction terms の sign を主張していない。

## 1.4 component orientation

Module:

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit
```

Public theorems:

```lean
pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution_eq_re_div_pi
pascalCenteredXiMellinQuadraticNormalizedElementaryContribution_eq_re_div_pi
pascalCenteredXiMellinQuadraticNormalizedTopContribution_eq_im_div_pi
```

さらに genuine oriented vertical source について

```lean
pascalCenteredXiMellinQuadraticOrientedArchimedeanSurface_deorient_re_eq_pi_mul_normalized
pascalCenteredXiMellinQuadraticOrientedElementarySurface_deorient_re_eq_pi_mul_normalized
```

がある。

Whole-surface audit 自身が、source reconstruction だけでは square / Gram / nonnegativity provider を与えないことを明記している。

## 1.5 interaction

CS25 public definition:

```lean
pascalCenteredXiPrimeSideAggregateRayInteractionEnergy
```

006P から named baseline bridge:

```lean
cfzpIntegratedPolarizedContactSlack_eq_four_mul_zeroCutoffBaseline_sub_interaction
```

および

```lean
cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_interaction_reaches_zeroCutoffBaseline
```

が利用可能。

---

# 2. 推奨 module

```text
DkMath.RH.CFBRC.CosmicFormulaZetaZeroCutoffRadialBudgetAudit
```

推奨 path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaZeroCutoffRadialBudgetAudit.lean
```

最低限 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaZeroCutoffContactBaselineAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit
import Mathlib.Tactic
```

既存 import chain で fixed radial / sign audit API に届くなら direct import は増やさなくてよい。

`DkMath/RH.lean` に public import を追加する。

---

# 3. Gate A — fixed radial budget reference の非負性

新しい alias は必須ではない。

まず public theorem として、任意の residue transport window `W` について

```text
0 <= pascalCenteredXiFixedRadialSecondMomentFunctional W.R
```

を証明する。

推奨 theorem 名:

```lean
cfzpFixedRadialSecondMomentFunctional_nonneg
```

推奨 proof 方針:

```text
1. W.circle_safe を使って
   FixedRadialSecondMomentFunctional = window radial second moment
   へ rewrite
2. pascalCriticalMirrorZeroWindowRadialSecondMoment を unfold
3. Finset.sum_nonneg
4. 各項は
   multiplicity cast >= 0
   normSq >= 0
   なので mul_nonneg
```

`positivity` で閉じるならそれでよい。

重要:

- これは baseline の非負性ではない。
- radial reference の非負性だけを閉じる。
- `0 <` の strict positivity は主張しない。

---

# 4. Gate B — correction source の oriented scalar representation

006P の

```text
IndependentCorrectionSourceReal
  = Arch + Elem + Top
```

と WholeSurface orientation theorem を使い、scaled correction source を genuine source projection へ exact に戻す。

目標形:

```text
π * IndependentCorrectionSourceReal
  = re(deorient(OrientedArchimedeanSurface))
    + re(deorient(OrientedElementarySurface))
    + im(HorizontalBase)
```

ここで `HorizontalBase` は既存

```lean
pascalCenteredXiMellinQuadraticHorizontalBase
```

または top contribution 本体を使ってよい。

推奨 theorem 名:

```lean
cfzpPiMulIndependentCorrectionSourceReal_eq_orientedCorrectionScalar
```

実装しやすい場合は右辺を直接展開してよく、新しい structure / record は不要。

係数 `π` と top の `im` orientation を Lean に必ず確認させる。

禁止:

- Arch / Elem / Top を normSq と同一視すること。
- top を vertical `re` として扱うこと。
- orientation を消して単純な complex sum の real partとみなすこと。

---

# 5. Gate C — zero-cutoff baseline の oriented budget representation

Gate B と 006P を組み合わせて exact に

```text
ZeroCutoffBaseline
  = π * FixedRadialSecondMoment
    - (
        re(deorient Arch)
        + re(deorient Elem)
        + im(TopHorizontal)
      )
```

を証明する。

推奨 theorem 名:

```lean
cfzpZeroCutoffRadialContactBaseline_eq_radialBudget_sub_orientedCorrectionScalar
```

これは baseline sign を source orientation のまま読むための load-bearing theorem。

---

# 6. Gate D — contact slack の radial-budget residual representation

006P:

```text
ContactSlack
  = 4 * (ZeroCutoffBaseline - Interaction)
```

へ Gate C を代入し、exact に

```text
ContactSlack
  = 4 * (
      π * FixedRadialSecondMoment
      - π * IndependentCorrectionSourceReal
      - AggregateRayInteractionEnergy
    )
```

を証明する。

推奨 theorem 名:

```lean
cfzpIntegratedPolarizedContactSlack_eq_four_mul_radialBudgetResidual
```

同値な括弧形:

```text
ContactSlack
  = 4 * (
      π * FixedRadialSecondMoment
      - (π * IndependentCorrectionSourceReal
         + AggregateRayInteractionEnergy)
    )
```

どちらでもよいが、後続の balance theorem を読みやすくするため括弧形を推奨。

この residual は signed。

`Gap`, `Mass`, `PositiveResidual` とは呼ばない。

新 alias を作る場合でも `RadialBudgetResidual` のような sign-neutral naming に限定する。

---

# 7. Gate E — radial budget contact equality

今回の最重要 theorem。

006P の contact condition を exact に

```text
IntegratedPolarizedImbalance = ContactThresholdLevel
```

と

```text
π * FixedRadialSecondMoment
  = π * IndependentCorrectionSourceReal
    + AggregateRayInteractionEnergy
```

の同値として閉じる。

推奨 theorem 名:

```lean
cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_radialBudget_balance
```

内容:

```text
contact
  ↔ radial reference budget
      = correction source + prime-side interaction
```

これは RH / zeta-zero theorem ではなく、finite source ledger の exact balance classification。

さらに安価なら

```text
ContactSlack = 0
  ↔ π * FixedRadialSecondMoment
      = π * IndependentCorrectionSourceReal
        + AggregateRayInteractionEnergy
```

も置く。

---

# 8. Gate F — radial budget order classification

Gate D から exact に以下を揃える。

## nonnegative slack side

```text
0 <= ContactSlack
  ↔ π * IndependentCorrectionSourceReal
      + AggregateRayInteractionEnergy
      <= π * FixedRadialSecondMoment
```

## nonpositive slack side

```text
ContactSlack <= 0
  ↔ π * FixedRadialSecondMoment
      <= π * IndependentCorrectionSourceReal
        + AggregateRayInteractionEnergy
```

さらに threshold notation へ戻して

```text
IntegratedPolarizedImbalance <= ContactThresholdLevel
  ↔ π * IndependentCorrectionSourceReal
      + AggregateRayInteractionEnergy
      <= π * FixedRadialSecondMoment
```

```text
ContactThresholdLevel <= IntegratedPolarizedImbalance
  ↔ π * FixedRadialSecondMoment
      <= π * IndependentCorrectionSourceReal
        + AggregateRayInteractionEnergy
```

を置いてよい。

これらは order classification であり dominance provider ではない。

---

# 9. Gate G — component-expanded radial budget equality

006P の correction component expansionを使って contact balance をさらに

```text
π * FixedRadialSecondMoment
  = π * ArchimedeanContribution
    + π * ElementaryContribution
    + π * TopContribution
    + AggregateRayInteractionEnergy
```

へ展開する。

推奨 theorem 名:

```lean
cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_componentExpandedRadialBudget_balance
```

また oriented source 版として

```text
π * FixedRadialSecondMoment
  = re(deorient Arch)
    + re(deorient Elem)
    + im(TopHorizontal)
    + AggregateRayInteractionEnergy
```

まで安価なら置く。

これは今回の conceptual summary theorem になる。

---

# 10. Gate H — component sign だけでは budget dominance は決まらないことの抽象 audit

既存 WholeSurface audit は sign provider を持たない。

今回、componentwise sign の探索に誤って進まないため、安価なら pure real countermodel を一つ置く。

例:

```text
非負な R, C, I だけを仮定しても
R - (C + I)
は正にも負にもなり得る。
```

推奨 theorem shape:

```lean
∃ R C I : ℝ,
  0 <= R ∧ 0 <= C ∧ 0 <= I ∧
  0 < R - (C + I)
```

かつ別 witness で

```lean
∃ R C I : ℝ,
  0 <= R ∧ 0 <= C ∧ 0 <= I ∧
  R - (C + I) < 0
```

一 theorem の conjunction でもよい。

意味:

- radial reference 非負
- correction 非負
- interaction 非負

が仮に全部分かっても、**contact slack の sign には量的比較が必要**。

したがって本当の frontier は component sign ではなく dominance / reach。

この countermodel は任意。既存 theorem の再利用だけで十分明瞭なら省略してよい。

---

# 11. Frontier markers

最低限、今回の結果に即した frontier を明示する。

推奨:

```lean
inductive CfzpZeroCutoffRadialBudgetDominanceGap : Prop
  | noIndependentCorrectionPlusInteractionLeRadialBudgetProvider
```

必要なら component source sign frontier:

```lean
inductive CfzpZeroCutoffCorrectionComponentSignGap : Prop
  | noIndependentArchimedeanElementaryTopSignProvider
```

interaction reach は既存 006O / CS25 marker を保持する。

```text
noIndependentZeroCutoffInteractionReachProvider
noIndependentCofinalInteractionReachProvider
```

を解決済み扱いしない。

---

# 12. 今回の重要な数学的整理

006Q が Green になると、finite contact は概念的に

```text
π * radial reference
  = π * correction source
    + prime-side interaction
```

となる。

これは宇宙式風には three-element balance に見えるが、現時点では

- radial reference は nonnegative を証明可能
- correction source は signed
- interaction は signed

である。

よってまだ

```text
Big = Body + Gap
```

の positive decomposition と同一視してはならない。

今回得るのは **signed radial-budget balance**。

この distinction を doc comment に明示すること。

---

# 13. Firewall

今回も以下を禁止する。

- `ZeroCutoffBaseline >= 0` の無条件 theorem
- `IndependentCorrectionSourceReal >= 0` の無条件 theorem
- Archimedean contribution の無条件 sign theorem
- Elementary contribution の無条件 sign theorem
- Top contribution の無条件 sign theorem
- AggregateRayInteractionEnergy の無条件 sign theorem
- AggregateRayInteractionEnergy の monotonicity theoremを根拠なく追加すること
- correction + interaction <= radial budget の無条件 theorem
- radial budget equality の存在 / 到達性を無条件に主張すること
- contact residual を `Gap`, `Mass`, `Big`, `Body` と命名すること
- correction components を normSq / square と同一視すること
- WholeSurface の affine real/imag projection から positivity を推論すること
- CompletionRemainder / ContactSlack を prime-mirror Gap または cosmic `δ²` と同一視すること
- pointwise polarization balance への飛躍
- complex source zero への飛躍
- zeta zero への飛躍
- RH conclusion
- infinite Euler product
- `X -> infinity`
- 新しい cofinal provider
- `Complex.arg`
- 新しい global `Complex.log` branch
- `sorry` / `admit` / `axiom` / `native_decide`

---

# 14. 成功条件

最低限、次が Green なら CFZP-006Q 完了とする。

```text
1. FixedRadialSecondMomentFunctional W.R >= 0 を W.circle_safe から証明
2. π * CorrectionSource の oriented scalar representation
3. ZeroCutoffBaseline の radial budget - oriented correction 表現
4. ContactSlack = 4 * (π*Radial - (π*Correction + Interaction))
5. contact ↔ π*Radial = π*Correction + Interaction
6. ContactSlack の nonneg/nonpos ↔ radial budget ordering
7. threshold ordering ↔ radial budget ordering
8. correction component-expanded balance
9. top horizontal orientation を im として保持
10. correction components の sign を新規主張しない
11. interaction の sign / monotonicity / reach を新規主張しない
12. radial budget dominance provider を捏造しない
13. prime-mirror/cosmic Gap と同一視しない
14. source/zeta-zero/RH へ進まない
15. DkMath.RH public import
16. target module build Green
17. lake build DkMath.RH Green
18. ./lean-build.sh Green
19. ./lean-test.sh Green
20. git diff --check Green
21. 新規 module に sorry / admit / axiom / native_decide / Complex.arg / Complex.log なし
```

---

# 15. 次 Gate への判断材料

006Q が Green になれば、contact の finite target は

```text
AggregateRayInteractionEnergy(ε,W,X)
  = π * FixedRadialSecondMoment(W.R)
    - π * IndependentCorrectionSourceReal(ε,W)
```

または等価に

```text
π * FixedRadialSecondMoment
  = π * CorrectionSource + AggregateRayInteractionEnergy(X)
```

へ完全に固定される。

ここで右辺の correction source は `X` に依存せず、interaction だけが cutoff `X` で変化する。

したがって次 CFZP-006R の第一候補は **interaction cutoff increment / finite partial-sum reach audit**。

CS25 には既に

```lean
pascalCenteredXiPrimeSideAggregateRayInteractionEnergy_eq_two_modeSum
```

があり、概念的に

```text
Interaction(X)
  = 2 * Σ_{n <= X} Λ(n) * ModeKernel(n)
```

である。

よって次は exact に

```text
Interaction(X+1) - Interaction(X)
  = 2 * Λ(X+1) * ModeKernel(X+1)
```

を finite successor identity として閉じ、

- composite non-prime-power step では increment zero になるのか
- prime-power step だけが interaction を動かすのか
- increment の sign は何が決めるのか
- fixed baseline への finite reach problem がどの partial sum 問題に一致するのか

を audit するのが自然。

この 006R で初めて、006O まで抽象的だった `interaction reach` が具体的な von Mangoldt / prime-power cutoff dynamics へ戻る。