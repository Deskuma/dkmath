# CFZP-0044 / CFZP-017

## radial-margin prime-threshold decomposition audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-014: functional-reflection prime-ray canonical aggregate transport — Green-A
- CFZP-015: arithmetic radial-domination margin frontier — Green-A
- CFZP-016: cofinal radial-domination frontier minimization — Green-A

CFZP-016 により、finite-window criticality を得るための十分条件は
CFZP-015 の eventual domination より弱い

```text
cofinally ε → 0+,
  cofinally X → ∞,
    WholeShiftedRadialMargin(ε,W,X) ≥ 0
```

まで縮約された。

ただし、この margin は finite prime contribution だけではない。既存
`PascalCenteredXiPrimeSideSignAudit` の four-term decomposition により、normalized
arithmetic surface は

```text
NormalizedPrimeContribution_X
+ NormalizedArchimedeanContribution
+ NormalizedElementaryContribution
+ NormalizedTopContribution
```

からなる。後三項と fixed radial observable は `X` に依存しない。

従って本段では margin を

```text
4 * π * (finite prime contribution - X-independent threshold)
```

へ exact に分解し、016 の cofinal domination frontier を
**cofinal prime-threshold crossing** として再表現する。

これは旧 CFZP-006W/006Y の phase-cell sign route を再利用する前の必須監査である。
phase-cell positivity が供給するのは prime-side kernel の符号情報であり、正の
threshold を超える magnitude は自動ではない。符号と threshold crossing を混同しない。

本段では独立 threshold-crossing provider、phase equidistribution、RH は証明しない。

---

## 1. 新規 module

推奨:

`DkMath.RH.CFBRC.CosmicFormulaZetaRadialMarginPrimeThresholdDecompositionAudit`

file:

`lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaRadialMarginPrimeThresholdDecompositionAudit.lean`

最低 import 候補:

- `DkMath.RH.CFBRC.CosmicFormulaZetaCofinalRadialDominationFrontierMinimizationAudit`
- `DkMath.RH.CFBRC.PascalCenteredXiPrimeSideSignAudit`
- `DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit`
- `Mathlib.Tactic`

既存 four-term decomposition、scalar-surface relation、CS25 interaction identity を
adapter として再利用する。

---

## 2. Gate A — X-independent normalized threshold

fixed `(ε,W)` に対して、prime contribution が越えるべき background threshold を
first-class にする。

推奨 shape:

```lean
noncomputable def cfzp017NormalizedPrimeThreshold
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
    pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution ε W -
    pascalCenteredXiMellinQuadraticNormalizedElementaryContribution ε W -
    pascalCenteredXiMellinQuadraticNormalizedTopContribution ε W
```

この threshold は `X` に依存しないことを定義上明確に保つ。

名称は多少調整してよいが、radial mass と三つの non-prime background correction を
混ぜた量であることが判るものにする。

---

## 3. Gate B — margin = 4π × prime-threshold excess

既存 theorem:

```lean
pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant_re_eq_four_terms
pascalCenteredXiPrimeSideQuadraticization_scalarSurface_eq_pi_mul_normalizedArithmetic_re
```

および CFZP-015 の margin/scalar identity を使って、conceptually

```text
cfzp015WholeShiftedRadialMargin ε W X
  = 4 * π *
      (pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X
        - cfzp017NormalizedPrimeThreshold ε W)
```

を exact に証明する。

`0 < ε` が既存 scalar/four-term theorem に必要なら hypothesis を保持する。

この identity から `Real.pi_pos` を使って

```text
0 ≤ cfzp015WholeShiftedRadialMargin ε W X
↔ cfzp017NormalizedPrimeThreshold ε W
    ≤ pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X
```

を出す。

これは本段の中心 theorem とする。

---

## 4. Gate C — CS25 interaction / finite mode sum への exact rewrite

既存 CS25 theorem:

```lean
pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_aggregateInteraction_div_pi
pascalCenteredXiPrimeSideAggregateRayInteractionEnergy_eq_two_modeSum
```

を再利用し、threshold crossing を interaction と finite von Mangoldt mode sum で
読める companion theorem を出す。

安全な形は division を避けて、例えば

```text
0 ≤ margin
↔ π * threshold ≤ AggregateRayInteractionEnergy
```

さらに

```text
0 ≤ margin
↔ π * threshold ≤
    2 * Σ n∈range(X+1),
      Λ(n) * pascalCenteredXiPrimeSideFiniteModeKernel ε W n
```

とする。

係数 `π`, `2` の向きは既存 theorem を実際に rewrite して確認し、推測で固定しない。

必要なら finite mode sum を CFZP-facing 名で first-class にしてよいが、既存 sum を
複製するだけなら theorem 右辺にそのまま置く。

---

## 5. Gate D — cofinal prime-threshold crossing

fixed epsilon の cofinal condition を named proposition にする。

推奨:

```lean
def Cfzp017CofinalPrimeThresholdCrossingAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∃ᶠ X : ℕ in Filter.atTop,
    cfzp017NormalizedPrimeThreshold ε W ≤
      pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X
```

`0 < ε` のもとで exact に

```text
Cfzp017CofinalPrimeThresholdCrossingAt ε W
↔ Cfzp016CofinalCutoffRadialDominationAt ε W
```

を証明する。

さらに outer cofinality を含む

```lean
def Cfzp017DoublyCofinalPrimeThresholdCrossing
    (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∃ᶠ ε : ℝ in 𝓝[>] 0,
    0 < ε ∧ Cfzp017CofinalPrimeThresholdCrossingAt ε W
```

を置き、可能なら

```text
Cfzp017DoublyCofinalPrimeThresholdCrossing W
↔ Cfzp016DoublyCofinalRadialDomination W
```

を exact に証明する。

この equivalence が閉じれば、CFZP-016 の finite-window criticality theorem を
threshold-crossing provider から再公開してよい。

これは provider の existence 証明ではなく、frontier の observable を sharpen する
だけである。

---

## 6. Gate E — sign-only route と magnitude route の分離

旧 CFZP-006W/006Y を今後再利用するため、次の logical distinction を Lean に残す。

### E1. threshold が非正なら prime nonnegativity で十分

conceptually:

```text
threshold ≤ 0
and 0 ≤ normalizedPrimeContribution
→ 0 ≤ margin
```

または threshold crossing を直接経由してもよい。

この theorem は単純な order adapter であり、prime contribution の非負性自体を
本段で証明しない。

### E2. prime nonnegativity だけでは正 threshold を越えない

小さな実数 countermodel を theorem として置く。例えば概念的に

```text
∃ (P T : ℝ),
  0 ≤ P ∧ 0 < T ∧ ¬ T ≤ P
```

`P = 0`, `T = 1` でよい。

この countermodel の目的は、CFZP-006W/006Y の phase-cell sign information を
そのまま CFZP-016 domination と同一視しないための firewall である。

---

## 7. Gate F — phase-cell route との境界を明示

CFZP-006W の branch-free phase-cell theorem は pointwise height `t` での
prime-power mode sign を扱う。一方 CS25 の finite mode sum は height integration
後の kernel を aggregate した scalar である。

従って本段では以下を禁止する。

- pointwise phase-cell positivity と integrated mode-sum threshold crossing の rename
- `0 ≤ prime contribution` から正 threshold crossing への無条件推論
- phase-cell coverage / equidistribution provider の捏造

roadmap には、006W/006Y を再利用するには少なくとも次の二つを区別する必要があると
記録する。

```text
1. pointwise phase-cell information
   -> integrated prime contribution sign/magnitude transport

2. integrated prime contribution
   -> X-independent threshold crossing
```

本段では 2 の exact target を固定する。1 は次段以降の独立解析 frontier とする。

---

## 8. Gate G — frontier marker

推奨 marker:

```lean
inductive Cfzp017PrimeThresholdCrossingGap : Prop
  | noIndependentDoublyCofinalPrimeThresholdCrossingProvider
```

必要なら pointwise phase-cell → integrated threshold crossing の別 marker を追加しても
よいが、marker を増やしすぎない。active frontier はまず doubly-cofinal prime-threshold
crossing 一つに再中心化する。

roadmap の想定分類:

```text
CFZP-016 doubly-cofinal radial domination: CLOSED as conditional interface
radial margin -> prime/background threshold decomposition: CLOSED
cofinal radial domination <-> cofinal prime-threshold crossing: CLOSED
independent doubly-cofinal prime-threshold crossing provider: OPEN / GAP
phase-cell sign -> integrated threshold crossing: OPEN analytic route
```

---

## 9. firewall

本段では以下を導入しない。

- `sorry`, `admit`, `axiom`, `native_decide`
- 新しい `Complex.arg`
- branch-sensitive phase observable
- 新しい global `Complex.log` convention
- pointwise/integrated observable の rename equality
- phase equidistribution provider
- independent threshold-crossing provider
- whole shifted energy の無条件 ordering
- contour deformation provider
- infinite Euler product
- joint `(ε,X)` limit
- `X → ∞` と `ε → 0+` の limit exchange
- common-baseline reach witness
- global RH または RH-equivalent provider の無条件証明

---

## 10. public import / roadmap / 検証

Green の場合:

- `DkMath/RH.lean` に新規 module を公開 import
- `0000-CFZP-roadmap.md` に CFZP-017 を追記

Gate A〜E が exact に閉じ、provider existence を open marker として残せれば
Green-A としてよい。

最低限:

```bash
lake env lean lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaRadialMarginPrimeThresholdDecompositionAudit.lean
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
