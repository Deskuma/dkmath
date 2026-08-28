# CFZP-0042 / CFZP-015

## arithmetic radial-domination margin frontier audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-010: amplitude-Gap / ray-minus observable-shape audit — Green-A
- CFZP-011: same-height mirror/source mode transform — Green-A
- CFZP-012: mirror-baseline functional-reflection height-reversal audit — Green-A
- CFZP-013: weight-reversal conjugation / self-recurrence — Green-A
- CFZP-014: functional-reflection prime-ray canonical aggregate transport — Green-A

CFZP-014 により、013 の functional-reflection prime-ray contribution は canonical finite symmetric Euler source まで exact に合流した。一方、reversed right-edge source から CS38 top-edge source への direct relocation は、既存 contour API 自体が conditional deformation provider に留まるため、現在の finite algebra の次段としては追わない。

本段では source-shape の細分化を止め、既存 `PascalCenteredXiPrimeSideQuadraticizationAudit`、`PascalCenteredXiPrimeSideSignAudit`、`PascalCenteredXiArithmeticDefectRepresentation`、`PascalCenteredXiFixedSecondMomentDefectBridge` を使って、RH へ向かう本当の finite analytic frontier を theorem-level に再中心化する。

核心は finite arithmetic defect

```text
D_X(ε,W)
```

の非正値を、whole shifted ± energy と fixed radial mass の間の **radial-domination margin** として exact に書くことである。

既存 theorem から概念的に

```text
D_X(ε,W) ≤ 0
  ↔ π * Radial(W) ≤ ScalarSurface_X(ε,W)
```

かつ

```text
4 * ScalarSurface_X
  = WholeShiftedPlusEnergy_X - WholeShiftedMinusEnergy_X
```

がある。従って新しい margin

```text
M_X :=
  (WholeShiftedPlusEnergy_X - WholeShiftedMinusEnergy_X)
  - 4 * π * Radial(W)
```

は exact に

```text
M_X = -4 * π * D_X
```

となるはずである。

本段ではこの algebra と ordered-limit sign transport を閉じる。`M_X ≥ 0` の独立証明そのものは導入しない。

---

## 1. 新規 module

推奨:

`DkMath.RH.CFBRC.CosmicFormulaZetaArithmeticRadialDominationMarginFrontierAudit`

file:

`lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaArithmeticRadialDominationMarginFrontierAudit.lean`

最低 import 候補:

- `DkMath.RH.CFBRC.CosmicFormulaZetaFunctionalReflectionPrimeRayCanonicalAggregateTransportAudit`
- `DkMath.RH.CFBRC.PascalCenteredXiPrimeSideQuadraticizationAudit`
- `DkMath.RH.CFBRC.PascalCenteredXiPrimeSideSignAudit`
- `DkMath.RH.CFBRC.PascalCenteredXiFixedSecondMomentDefectBridge`
- `Mathlib.Tactic`

既存 theorem を adapter として再利用し、quadraticization machinery を複製しない。

---

## 2. Gate A — finite radial comparison を defect sign として再公開

既存 theorem:

```lean
pascalCenteredXiPrimeSideQuadraticization_radial_le_scalarSurface_iff_defect_nonpos
```

を CFZP-facing adapter として再公開する。

狙う shape:

```text
π * fixedRadialSecondMoment(W.R)
  ≤ scalarSurface(ε,W,X)
↔ arithmeticDefectApproximant(ε,W,X) ≤ 0
```

`0 < ε` を明示する。

これは既存 theorem の rename adapter でよい。新しい sign proof は不要。

---

## 3. Gate B — whole shifted radial margin

first-class definition を置く。

推奨:

```lean
noncomputable def cfzp015WholeShiftedRadialMargin
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  (pascalCenteredXiPrimeSideQuadraticizationWholeShiftedPlusEnergy ε W X -
    pascalCenteredXiPrimeSideQuadraticizationWholeShiftedMinusEnergy ε W X) -
  4 * Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R
```

既存

```lean
pascalCenteredXiPrimeSideQuadraticization_scalarSurface_eq_shiftedEnergyDifference
pascalCenteredXiMellinQuadraticScalarExcess_eq_neg_pi_mul_defect
```

を使って exact に

```text
cfzp015WholeShiftedRadialMargin ε W X
  = -4 * π * pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X
```

を証明する。

さらに `Real.pi_pos` を使って

```text
0 ≤ margin ↔ defect ≤ 0
```

を証明する。

可能なら companion として

```text
0 ≤ margin
↔ 4 * π * Radial ≤ WholePlus - WholeMinus
↔ π * Radial ≤ ScalarSurface
```

も出す。

重要:

- `WholeShiftedPlusEnergy` と `WholeShiftedMinusEnergy` は個別には PSD だが、差の符号は自動ではない。
- `wholeShiftedMinus ≤ wholeShiftedPlus` だけでは `π * Radial ≤ ScalarSurface` は出ない。radial baseline が残る。
- radial term を 0 と誤認しない。

---

## 4. Gate C — ordered finite radial-domination provider proposition

finite analytic frontier を一つの proposition として named にする。

例えば:

```lean
def Cfzp015OrderedFiniteRadialDomination
    (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ X : ℕ in Filter.atTop,
      0 ≤ cfzp015WholeShiftedRadialMargin ε W X
```

または同値な radial comparison shape:

```text
∀ ε > 0, eventually X,
  π * Radial(W) ≤ ScalarSurface(ε,W,X)
```

を採用してよい。

ただしこの proposition の inhabitant を本 module で製造しない。

---

## 5. Gate D — ordered-limit transport to fixed finite-window defect zero

既存 `PascalCenteredXiPrimeSideSignAudit` の

```lean
pascalCenteredXiArithmeticDefectEndpoint_nonpos_of_eventually_approximant_nonpos
pascalCenteredXiFixedDefect_nonpos_of_eventually_endpoint_nonpos
```

および fixed defect の非負性

```lean
pascalCenteredXiFixedSecondMomentDefectFunctional_nonneg
```

を使う。

`Cfzp015OrderedFiniteRadialDomination W` から少なくとも次を証明する。

```text
pascalCenteredXiFixedSecondMomentDefectFunctional W.R = 0
```

proof route:

1. 各 fixed `ε > 0` で margin eventual nonnegative。
2. Gate B により defect approximant eventual nonpositive。
3. fixed-ε `X → ∞` adapter により arithmetic defect endpoint `≤ 0`。
4. positive ε 全体で成立するので `ε → 0+` の eventual endpoint nonpositive を構成。
5. ordered ε-limit adapter により fixed defect `≤ 0`。
6. `W.circle_safe` による fixed defect `≥ 0` と合わせて equality。

`𝓝[>] 0` の filter bookkeeping は既存 Mathlib API を使い、joint limit や limit exchange を導入しない。

さらに既存

```lean
pascalCenteredXiFixedSecondMomentDefectFunctional_eq_zero_iff
```

を使って、同じ仮定から

```text
∀ ρ ∈ pascalCriticalMirrorZeroWindowFinset W.R,
  ρ.re = 1 / 2
```

まで証明する。

これは finite window conclusion であり、ここから無条件 RH を主張しない。

---

## 6. Gate E — global RH についての firewall

既存 theorem

```lean
pascalCenteredXiFixedDefectVanishesOnSafeRadii_iff_riemannHypothesis
```

は利用可能だが、本段の provider は `ResidueTransportWindow W` 単位である。

**全 boundary-safe radius が現在の W-family で exact に cover される既存 theorem が本当に見つかった場合のみ**、global sufficient-condition theorem を追加してよい。

そのような coverage theorem が無ければ、無理に RH theorem を作らない。

特に以下を禁止する。

- `∀ W` を `∀ safe R` と暗黙同一視すること
- 新しい window-existence assumption を RH の証明済み provider として扱うこと
- `Cfzp015OrderedFiniteRadialDomination` 自体を証明したことにすること

---

## 7. Gate F — frontier marker / roadmap re-centering

新 marker 推奨:

```lean
inductive Cfzp015ArithmeticRadialDominationGap : Prop
  | noIndependentEventualWholeShiftedRadialDominationProvider
```

roadmap には次を明記する。

```text
CFZP-010..014 source-shape / canonical finite transport: CLOSED
CFZP-014 right-edge -> CS38 top-edge direct relocation:
  PARKED behind conditional contour-deformation provider

ordered arithmetic representation:
  X -> ∞: CLOSED
  ε -> 0+: CLOSED

fixed defect:
  nonnegative on safe radius: CLOSED
  zero iff all finite-window zeros are critical: CLOSED
  vanishing on all safe radii iff RH: CLOSED AS EQUIVALENCE ONLY

active analytic frontier:
  eventual finite arithmetic-to-radial domination
  equivalently eventual nonnegativity of cfzp015WholeShiftedRadialMargin
```

common-baseline finite/cofinal reach は別 route として OPEN のまま保持するが、本 route の次 provider と混同しない。

---

## 8. 禁止事項 / firewall

本段では以下を導入しない。

- `sorry`, `admit`, `axiom`, `native_decide`
- 新しい `Complex.arg`
- branch-sensitive phase observable
- 新しい global `Complex.log` convention
- contour deformation provider の捏造
- right-edge/top-edge rename equality
- infinite Euler product
- joint `(ε,X)` limit
- `X → ∞` と `ε → 0+` の交換
- whole shifted energy の無条件 ordering
- radial domination provider の無条件 existence
- common-baseline reach witness
- RH または RH-equivalent provider の無条件証明

既存 imported module 内の legacy `Complex.arg` は本段の新規 proof に持ち込まない。

---

## 9. public import / roadmap

Green の場合:

- `DkMath/RH.lean` に新規 module を公開 import
- `0000-CFZP-roadmap.md` に CFZP-015 を追記

Gate A〜D が exact に閉じ、provider existence を未証明のまま sharp marker に残せれば Green-A としてよい。

---

## 10. 検証

最低限:

```bash
lake env lean lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaArithmeticRadialDominationMarginFrontierAudit.lean
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
