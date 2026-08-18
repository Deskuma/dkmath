# CFZP-0045 / CFZP-018

## prime-threshold approximate-reach frontier audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-015: arithmetic radial-domination margin frontier — Green-A
- CFZP-016: cofinal radial-domination frontier minimization — Green-A
- CFZP-017: radial-margin prime-threshold decomposition — Green-A

CFZP-017 により finite radial margin は fixed `(ε,W)` で

```text
M_X = 4 * π * (P_X - T)
```

へ exact に分解された。

ここで

```text
P_X := NormalizedPrimeContribution(ε,W,X)
T   := NormalizedPrimeThreshold(ε,W)
```

であり、`T` は `X` に依存しない。

さらに CS25 により

```text
P_X = I_X / π
G_X = G_0 - I_X
```

が既に存在する。CS24 の correction source は

```text
Archimedean + Elementary + Top
```

そのものであり、zero-cutoff radial deficit は conceptually

```text
G_0 = π * T
```

となる。

従って CFZP-017 の exact threshold crossing

```text
T ≤ P_X
```

は finite radial deficit の

```text
G_X ≤ 0
```

と同じ observable を別座標で読んでいる。

しかし既存 CS22 の
`PascalCenteredXiPrimeSideCofinalRadialContactZeroAt` は、実際に `G_X ≤ 0`
となる cutoff を要求しない。任意の `η > 0` に対し arbitrarily late に

```text
G_X ≤ η
```

へ近づけば fixed-`ε` endpoint defect の非正性を得る。

normalized prime threshold 座標では、これは

```text
P_X ≥ T - δ
```

を任意の `δ > 0` について cofinally 実現することに相当する。

本段の目的は、CFZP-017 の exact threshold crossing frontier をこの
**arbitrarily-close cofinal threshold reach** へさらに弱め、既存 CS22 と exact に
統合することである。

これは phase-cell sign route を攻める前の frontier minimization である。
本段では threshold への exact crossing、phase equidistribution、provider existence、
RH は証明しない。

---

## 1. 新規 module

推奨:

`DkMath.RH.CFBRC.CosmicFormulaZetaPrimeThresholdApproximateReachFrontierAudit`

file:

`lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPrimeThresholdApproximateReachFrontierAudit.lean`

最低 import 候補:

- `DkMath.RH.CFBRC.CosmicFormulaZetaRadialMarginPrimeThresholdDecompositionAudit`
- `DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCofinalRadialContactAudit`
- `DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCanonicalPolarizationSignedMassAudit`
- `DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit`
- `Mathlib.Tactic`

既存 API を adapter として使う。古い theorem を再証明するだけの duplicate module に
しない。

---

## 2. Gate A — CFZP-017 threshold と CS24 correction source の同一化

まず CFZP-017 threshold が CS24 correction source を使えば

```text
T
  = FixedRadialSecondMomentFunctional
    - IndependentCorrectionSourceReal
```

であることを first-class theorem にする。

概念 shape:

```lean
theorem cfzp018NormalizedPrimeThreshold_eq_fixed_sub_correction
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) :
    cfzp017NormalizedPrimeThreshold ε W =
      pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
        pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W := by
  ...
```

これは定義展開と ring/simp で閉じるはずである。

ここでは sign を主張しない。

---

## 3. Gate B — threshold は zero-cutoff radial deficit の normalized form

fixed positive epsilon で exact に

```text
π * T = G_0
```

を証明する。

推奨 theorem shape:

```lean
theorem cfzp018_pi_mul_normalizedPrimeThreshold_eq_zeroCutoffRadialDeficit
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) :
    Real.pi * cfzp017NormalizedPrimeThreshold ε W =
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 := by
  ...
```

証明では private theorem に依存しない。

利用候補:

- `pascalCenteredXiPrimeSideCanonicalPolarizationRemainder_eq_zeroCutoff_deficit_add_minusMass`
- `pascalCenteredXiPrimeSideAggregateRayMinusEnergy_zero`
- `pascalCenteredXiPrimeSideIndependentCorrectionSourceReal`
- Gate A theorem

あるいは public CS23/CS24 source decomposition から直接閉じてもよい。

重要:

- `G_0` を新しい background mass と呼び替えない。
- これは既存 zero-cutoff radial deficit の exact normalization である。
- threshold の非負性・正値性は導かない。

---

## 4. Gate C — CFZP-015 margin は finite radial deficit の `-4` 倍

既存

```text
cfzp015WholeShiftedRadialMargin
  = -4 * π * ArithmeticDefectApproximant
```

と CS22

```text
FiniteRadialContactDeficit
  = π * ArithmeticDefectApproximant
```

から exact に

```text
M_X = -4 * G_X
```

を出す。

推奨:

```lean
theorem cfzp018WholeShiftedRadialMargin_eq_neg_four_mul_radialContactDeficit
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    cfzp015WholeShiftedRadialMargin ε W X =
      -4 * pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X := by
  ...
```

そこから

```text
0 ≤ M_X  ↔  G_X ≤ 0
```

を公開する。

さらに CFZP-017 の exact threshold crossing と合わせ、可能なら

```text
T ≤ P_X  ↔  G_X ≤ 0
```

も first-class theorem にする。

この Gate により、017 の exact crossing が zero-crossing observable そのものだと
明示する。

---

## 5. Gate D — aggregate interaction reach との canonical identification

CS25 の

```text
G_X = G_0 - I_X
```

および Gate B の `π*T = G_0` を使い、exact threshold crossing を

```text
G_0 ≤ I_X
```

としても読めるようにする。

候補:

```lean
theorem cfzp018_primeThresholdCrossing_iff_zeroCutoffInteractionReach ... :
    cfzp017NormalizedPrimeThreshold ε W ≤
        pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X ↔
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 ≤
        pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X := by
  ...
```

係数 `π` を消す場合は必ず既存
`NormalizedPrimeContribution_eq_aggregateInteraction_div_pi`
と `Real.pi_pos` を使って確認する。

推測で normalization を変えない。

---

## 6. Gate E — arbitrarily-close prime-threshold reach

fixed `(ε,W)` に対し、exact crossing より弱い normalized threshold approach を
first-class にする。

推奨:

```lean
def Cfzp018CofinalPrimeThresholdApproximateReachAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧
    cfzp017NormalizedPrimeThreshold ε W - δ ≤
      pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X
```

同値な `T ≤ P_X + δ` 形でもよいが、一つに統一する。

これは `Frequently (T ≤ P_X)` ではない。

意味は

```text
for every positive normalized slack δ,
arbitrarily late finite prime cutoffs reach T - δ.
```

---

## 7. Gate F — CS22 cofinal radial contact zero との exact equivalence

本段の中心 theorem。

fixed positive epsilon で

```text
Cfzp018CofinalPrimeThresholdApproximateReachAt ε W
↔ PascalCenteredXiPrimeSideCofinalRadialContactZeroAt ε W
```

を exact に証明する。

スケール変換は

```text
G_X = π * (T - P_X)
```

を使うのが最も明瞭である。

この identity は Gate B + CS25、または CS22/CS23/CFZP-017 から導出して
first-class theorem として先に置いてもよい。

normalized slack `δ` と geometric slack `η` の変換は

```text
η = π * δ
δ = η / π
```

であり、`Real.pi_pos` を使う。

この Gate によって exact crossing を要求せず、threshold へ任意精度で cofinal に
近づくだけで fixed-ε endpoint nonpositivity に届くことを閉じる。

さらに既存 CS22 theorem により companion として

```text
Cfzp018CofinalPrimeThresholdApproximateReachAt ε W
↔ pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W ≤ 0
```

も公開してよい。

---

## 8. Gate G — CFZP-017 exact crossing は approximate reach を含意する

fixed positive epsilon で

```text
Cfzp017CofinalPrimeThresholdCrossingAt ε W
→ Cfzp018CofinalPrimeThresholdApproximateReachAt ε W
```

を証明する。

`Frequently` crossing と `atTop` の eventual `N ≤ X` を交差させればよい。

逆向きは主張しない。

pointwise firewall として、例えば

```lean
theorem cfzp018ApproximateSlack_does_not_imply_exactCrossing :
    ∃ P T δ : ℝ,
      0 < δ ∧ T - δ ≤ P ∧ ¬ T ≤ P := by
  ...
```

のような純実数 countermodel を置いてよい。

これは cofinal strictness 全体の formal counterexample ではなく、slack relation を
exact crossing へ rename できないことの局所 firewall と明記する。

sequence-level strictness countermodel は Lean API 負担が大きければ不要。

---

## 9. Gate H — doubly-cofinal approximate-reach provider

外側 epsilon も CFZP-016 と同じく `Frequently` を維持する。

推奨:

```lean
def Cfzp018DoublyCofinalPrimeThresholdApproximateReach
    (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∃ᶠ ε : ℝ in 𝓝[>] 0,
    0 < ε ∧ Cfzp018CofinalPrimeThresholdApproximateReachAt ε W
```

この provider から finite-window criticality まで conditional に閉じる。

手順:

1. Gate F により cofinally many positive epsilon で CS22 cofinal radial contact zero。
2. CS22 theorem により同じ epsilon で arithmetic defect endpoint `≤ 0`。
3. existing
   `tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_epsilon W`
   と `Frequently(endpoint ≤ 0)` から fixed defect `≤ 0`。
4. safe-radius nonnegativity と合わせ fixed defect `= 0`。
5. existing zero iff から finite zero window criticality。

`Frequently(nonpositive)` + `Tendsto` から limit nonpositive を得る小補題は、CFZP-016 の
private helper を外から使えない場合、この module 内で局所的に証明してよい。

概念:

```lean
private theorem nonpos_of_tendsto_of_frequently_nonpos ...
```

limit が正なら eventually 正となり、frequently nonpositive と衝突するだけでよい。

重要:

- outer condition を `Eventually` に強めない。
- joint `(ε,X)` limit を導入しない。
- limit exchange をしない。

---

## 10. Gate I — 017 provider hierarchy

可能なら

```text
Cfzp017DoublyCofinalPrimeThresholdCrossing W
→ Cfzp018DoublyCofinalPrimeThresholdApproximateReach W
```

を hierarchy adapter として証明する。

これにより

```text
017 exact crossing
    ↓
018 arbitrary-slack cofinal reach
    ↓
finite-window criticality
```

という strict weakening direction を roadmap に明示できる。

逆 implication は証明しない。

---

## 11. Gate J — sharpened provider frontier

本段の unresolved frontier は exact threshold crossing ではなく、より弱い

```text
cofinally ε -> 0+,
  for every δ > 0,
    arbitrarily late X reaches P_X ≥ T - δ
```

である。

marker 例:

```lean
inductive Cfzp018PrimeThresholdApproximateReachGap : Prop
  | noIndependentDoublyCofinalPrimeThresholdApproximateReachProvider
```

名称は調整してよい。

ここで provider inhabitant を作らない。

---

## 12. phase-cell route との境界

CFZP-006W/006Y の sign-cell 情報を本段で provider に昇格しない。

特に

```text
mode/kernel ≥ 0
```

から

```text
P_X ≥ T - δ
```

を無条件に推論しない。

ただし本段により今後 phase-cell 側が供給すべき magnitude は exact threshold crossing
ではなく、任意 slack 付きの cofinal approximation まで弱まる。

これは次段以降の analytic target を明確化するための成果である。

---

## 13. Firewall

導入禁止:

- `Complex.arg`
- 新しい global `Complex.log` branch
- zero counting
- phase equidistribution の仮定
- exact threshold-crossing provider
- unconditional approximate-reach provider
- joint `(ε,X)` limit
- limit exchange
- contour relocation の新規仮定
- common-baseline reach の rename
- global RH
- RH-equivalent provider

また、次を混同しない:

```text
exact crossing:        T ≤ P_X
approximate reach:     T - δ ≤ P_X for every δ > 0 cofinally
sign only:             0 ≤ P_X or mode/kernel sign
```

三者は別である。

---

## 14. public import / roadmap

実装完了後:

1. `DkMath/RH.lean` に新 module import を追加。
2. `0000-CFZP-roadmap.md` に CFZP-018 section を追加。
3. classification は、上記 exact finite identities・CS22 equivalence・conditional
   finite-window criticality が閉じれば Green-A。
4. roadmap では明示的に

```text
π * normalized threshold = zero-cutoff radial deficit: CLOSED
whole shifted margin = -4 * finite radial deficit: CLOSED
exact threshold crossing = finite deficit zero-crossing: CLOSED
arbitrary-slack threshold reach <-> CS22 cofinal radial contact zero: CLOSED
017 exact crossing -> 018 approximate reach: CLOSED
independent doubly-cofinal approximate-reach provider: OPEN / GAP
phase-cell sign -> approximate magnitude reach: OPEN analytic route
```

と整理する。

---

## 15. Green suite

最低限:

- 新 module 単体 build
- `lake build DkMath.RH`
- project full build script
- project test script
- `git diff --check`
- `sorry`, `admit`, `axiom`, `native_decide` の新規導入なし
- `Complex.arg` の新規導入なし
- global `Complex.log` branch の新規導入なし

GitHub Actions は必須ではない。local Green を正本とする。

---

## 16. Exit condition

CFZP-018 の終了条件は、CFZP-017 の threshold observable を CS22/CS25 の既存
radial-contact geometry へ完全に戻し、現在の ordered-limit route に必要な provider を

```text
exact crossing
```

から

```text
arbitrarily-close cofinal reach
```

へ弱め切ることである。

ここが閉じた後に初めて、CFZP-006W/006Y phase-cell ledger がこの weaker magnitude
frontierへどこまで届くかを監査する。
