# CFZP-0050 / CFZP-023

## quantitative prime-power pulse margin audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-019: branch-free signed-mass budget — Green-A
- CFZP-020: cutoff-frontier signed-mass recurrence — Green-A
- CFZP-021: von Mangoldt one-mode pulse compression — Green-A
- CFZP-022: finite pulse-block compensation — Green-A
- CFZP-006W/X/Y: branch-free centered profile / exact derivative / phase-cell sign adapters

CFZP-022 により fixed-`ε` closure frontier は、任意の現在 cutoff `A` からある有限 future block `(A,B]` が現在の radial deficit を任意 slack まで支払えるか、という有限量的問題へ exact に圧縮された。

ここから先は座標変換を増やさず、**one-event sign を one-event magnitude へ昇格する**。

既存 CFZP-006W には safe-frequency prime-power event の exact factorization

```text
Event(p,j)
  = PositiveScale(ε,p,j)
      * (Profile(left) - Profile(right))
```

があり、CFZP-006X には positive half-line 上の exact derivative

```text
Profile'(u)
  = exp(-a*u) / u^3 * DerivativeCore(a,T,u)
```

と mean-value/monotonicity machinery がある。

本段では centered interval 全体で derivative が一定量だけ負であるという **quantitative drop margin** を仮定したとき、profile drop、prime-power event、von Mangoldt pulse に explicit positive lower bound が入ることを証明する。

さらに derivative の absolute envelope から event / pulse の absolute upper boundを作る。

最重要の観測は centered interval width が `2*ε` であり、existing positive event scale が `(2*ε)⁻¹` を含むため、mean-value lower boundとの積で smoothing-window width が exact に消えることである。

概念的には

```text
Profile'(u) ≤ -κ on centered interval
  -> Profile(left) - Profile(right) ≥ 2*ε*κ
  -> Event(p,j) ≥ 2*log(p)*CriticalScale(p^j)*κ
```

を得たい。

この theorem は independent margin provider ではない。`κ` を実際に prime-power / phase geometry から供給することは次段以降の算術・解析 frontier として残す。

---

## 1. 新規 module

作成候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaQuantitativePrimePowerPulseMarginAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaQuantitativePrimePowerPulseMarginAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaFinitePulseBlockCompensationAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaNegativeFrequencyProfileDerivativeAudit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic
```

transitive import で十分なら重複 import は減らしてよい。

---

## 2. Gate A — generic quantitative derivative-drop lemma

まず RH 固有定義から離れた local real lemma として、`0 < l < r` の区間で differentiable な実関数 `f` が

```text
∀ u ∈ Ioo l r, deriv f u ≤ -κ
```

を満たすなら、`0 ≤ κ` の下で

```text
κ * (r - l) ≤ f l - f r
```

を証明する。

Mathlib の mean-value inequality / convex interval API を優先する。

既存 theorem 名を確認し、無理に独自 MVT を再証明しない。

必要なら CFZP profile に特化した theorem として直接閉じてもよいが、再利用可能な local lemma が短く書けるなら private/public helper として残す。

同時に absolute derivative envelope版も狙う:

```text
0 ≤ K
∀ u ∈ Ioo l r, |deriv f u| ≤ K
  -> |f r - f l| ≤ K * (r - l)
```

こちらも Mathlib MVT API を優先する。

---

## 3. Gate B — centered interval exact width

既存 definitions

```text
cfzpPrimePowerPhaseMagnitudeLeft ε p j
cfzpPrimePowerPhaseMagnitudeRight ε p j
```

について exact に

```text
right - left = 2 * ε
```

を public theorem にする。

例:

```lean
theorem cfzp023PrimePowerPhaseMagnitude_width
    (ε : ℝ) (p j : ℕ) :
    cfzpPrimePowerPhaseMagnitudeRight ε p j -
        cfzpPrimePowerPhaseMagnitudeLeft ε p j = 2 * ε := by
  ...
```

この theorem は window-normalization cancellation の algebraic key なので first-class に残す。

---

## 4. Gate C — quantitative centered derivative-drop contract

prime-power centered frequency intervalに対する Prop を定義する。

推奨 shape:

```lean
def Cfzp023CenteredProfileDerivativeDropMargin
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) (κ : ℝ) : Prop :=
  ∀ u ∈ Set.Ioo
      (cfzpPrimePowerPhaseMagnitudeLeft ε p j)
      (cfzpPrimePowerPhaseMagnitudeRight ε p j),
    deriv
      (fun x : ℝ =>
        cfzpNegativeFrequencyBoundaryProfile
          (cfzpModePhaseAbscissa W) W.rectangle.T x) u ≤ -κ
```

`κ` の非負性は Prop 内に埋めず theorem hypothesis に分離してよい。

同様に absolute envelope:

```lean
def Cfzp023CenteredProfileDerivativeAbsEnvelope ... (K : ℝ) : Prop :=
  ∀ u ∈ Ioo left right,
    |deriv profile u| ≤ K
```

---

## 5. Gate D — centered profile quantitative drop

safe-frequency assumptions

```text
0 < ε < log 2
Nat.Prime p
0 < j
0 ≤ κ
CenteredProfileDerivativeDropMargin ... κ
```

の下で、centered endpoints が正かつ ordered である既存 theorem を使い、

```text
2 * ε * κ
  ≤ Profile(left) - Profile(right)
```

を証明する。

積の並びは `ring` / `nlinarith` が扱いやすい形でよい。

absolute envelope 版では

```text
|Profile(left) - Profile(right)| ≤ 2 * ε * K
```

を証明する。

---

## 6. Gate E — window-normalization cancellation / event lower bound

006W の exact event factorization

```text
cfzpPrimePowerBranchFreeTrigEvent_eq_positiveScale_mul_centeredProfileDifference
```

と Gate D を合成する。

中心 theorem shape:

```text
2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j) * κ
  ≤ cfzpPrimePowerBranchFreeTrigEvent ε W p j
```

ここで既存

```text
cfzpPrimePowerEventPositiveScale ε p j
  = 2 * log p * ((2*ε)⁻¹ * CriticalScale(p^j))
```

と profile drop `≥ 2*ε*κ` を掛けると、`0 < ε` により `(2*ε)⁻¹ * (2*ε) = 1` が exact に消える。

この cancellation を proof の偶然に埋めず、docstring で数学的意味を明記する。

### strict positivity adapter

`0 < κ` の場合、prime `p` の `log p > 0` と critical scale positivity を使い

```text
0 < cfzpPrimePowerBranchFreeTrigEvent ε W p j
```

まで出す。

ただし main target は sign ではなく explicit lower bound。

---

## 7. Gate F — event absolute upper envelope

Gate D の absolute derivative envelope と positive-scale factorizationから、`0 ≤ K` の下で

```text
|cfzpPrimePowerBranchFreeTrigEvent ε W p j|
  ≤ 2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j) * K
```

を証明する。

符号を仮定しない genuine magnitude upper bound とする。

必要なら `abs_mul`、positiveScale positivity、`abs_of_nonneg` を使う。

この theorem は後続 block で negative debt を upper-bound するための主要 API になる。

---

## 8. Gate G — positive mass / negative debt adapters

019 の canonical one-event parts に接続する。

quantitative drop lower boundから、右辺 credit が nonnegative であることを確認し、

```text
credit(p,j,κ)
  ≤ cfzp019PrimePowerEventPositiveMass ε W p j
```

を証明する。

absolute event upper boundから

```text
cfzp019PrimePowerEventNegativeDebt ε W p j
  ≤ envelope(p,j,K)
```

を証明する。

可能なら positive mass に対する同じ envelope upper boundも追加してよい。

ここで

```text
credit := 2*log p*CriticalScale(p^j)*κ
envelope := 2*log p*CriticalScale(p^j)*K
```

を local defs にするか explicit expression のまま使うかは proof ergonomics で選ぶ。

---

## 9. Gate H — von Mangoldt pulse adapters

CFZP-021 の prime-power pulse/event identificationを使い、`n = p^j` のとき同じ quantitative boundを pulse に transportする。

必須:

```text
credit(p,j,κ) ≤ Pulse(p^j)
|Pulse(p^j)| ≤ envelope(p,j,K)
```

`X+1 = p^j` shape の successor adapter も短く閉じるなら追加してよい。

これにより CFZP-022 block を構成する各 nonzero termに quantitative certificateを付けられる。

---

## 10. Gate I — quantitative-vs-sign consistency

`κ = 0` の drop-margin theoremが既存 006X/006Y sign theoremと矛盾せず、少なくとも

```text
Centered derivative ≤ 0 -> Event ≥ 0
```

を再現できることを adapter theorem または docstring で明確にする。

既存 sign theoremそのものを再証明する必要はない。quantitative theoremがその strict refinement であることが分かればよい。

重要:

- phase-cell sign coverageだけから `κ > 0` を捏造しない。
- cell boundaryでは derivative marginが0になり得る。
- strict interior / uniform margin provider は別問題として残す。

---

## 11. Gate J — explicit provider frontier

Gap marker を置く。

例:

```lean
inductive Cfzp023QuantitativePrimePowerPulseMarginGap : Prop
  | noIndependentUniformPrimePowerDerivativeMarginProvider
```

意味:

- one-event sign は既にある。
- one-event quantitative lower/upper bound machinery は本段で閉じる。
- しかし actual prime-power phases が、cofinally / sufficiently often、どの positive margin `κ` を持つかは未解決。
- block 内 negative debt envelope と positive credit の dominance もまだ provider ではない。

---

## 12. firewall

本段で禁止:

```text
phase-cell sign -> positive uniform κ without proof
universal derivative margin
pulse eventual positivity
block dominance provider
phase equidistribution assumption
asymptotic density assumption
joint (ε,X) limit
limit exchange
infinite Euler-product argument
unconditional CFZP-022 compensation provider
unconditional finite-window criticality / RH
```

特に `sin ≤ 0`, `cos ≤ 0` の closed quadrant signだけでは strict magnitudeを得ない。boundaryで0になり得るため、quantitative marginは explicit hypothesis として保持する。

---

## 13. desired exit condition

CFZP-023 終了時に Lean API から次が読めること。

```text
Profile'(u) ≤ -κ on centered interval
  -> Profile(left)-Profile(right) ≥ 2ε κ
  -> Event(p,j) ≥ 2 log(p) CriticalScale(p^j) κ
  -> PositiveMass(p,j) ≥ same credit
```

and

```text
|Profile'(u)| ≤ K on centered interval
  -> |Event(p,j)| ≤ 2 log(p) CriticalScale(p^j) K
  -> NegativeDebt(p,j) ≤ same envelope
```

prime-power witnessでは同じ bounds が `cfzp021VonMangoldtPulse` にも成立する。

この段を Green にした後の本命は、CFZP-022 block supportを quantitative good/bad certificatesで分割し、

```text
current deficit + certified bad-envelope mass
  ≤ certified good-credit mass + η
```

を finite sufficient conditionとして閉じること。その次に初めて phase/arithmetic structureから good credit の供給と bad debt の抑制を攻める。
