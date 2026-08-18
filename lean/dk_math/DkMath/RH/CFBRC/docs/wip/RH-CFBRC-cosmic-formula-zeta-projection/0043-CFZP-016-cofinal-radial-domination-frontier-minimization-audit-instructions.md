# CFZP-0043 / CFZP-016

## cofinal radial-domination frontier minimization audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-014: functional-reflection prime-ray canonical aggregate transport — Green-A
- CFZP-015: arithmetic radial-domination margin frontier — Green-A

CFZP-015 では finite margin

```text
M_X(ε,W)
```

を first-class にし、既存 arithmetic defect approximant `D_X(ε,W)` に対して

```text
M_X(ε,W) = -4 * π * D_X(ε,W)
```

を exact に証明した。また

```text
0 ≤ M_X(ε,W)
↔ D_X(ε,W) ≤ 0
↔ π * Radial(W) ≤ ScalarSurface_X(ε,W)
```

を閉じた。

さらに

```text
∀ ε > 0, eventually X → ∞, 0 ≤ M_X(ε,W)
```

という `Cfzp015OrderedFiniteRadialDomination W` を十分条件として、ordered limits を通じた finite-window criticality まで証明した。

ただしこの provider は収束列に対する十分条件としては強い。固定 `ε > 0` で `M_X(ε,W)` は既存 defect convergence から endpoint margin に収束するので、極限値を非負にするには **eventually nonnegative** ではなく **frequently / cofinally nonnegative** で十分である。同様に `ε → 0+` 側も全ての正の `ε` で endpoint margin が非負である必要はなく、0 に向かって cofinally 多くの `ε` で非負なら fixed margin の非負性を強制できる。

本段では provider を証明しない。CFZP-015 の frontier を、より弱い二重 cofinal sign condition まで theorem-level に縮める。

---

## 1. 新規 module

推奨:

`DkMath.RH.CFBRC.CosmicFormulaZetaCofinalRadialDominationFrontierMinimizationAudit`

file:

`lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaCofinalRadialDominationFrontierMinimizationAudit.lean`

最低 import 候補:

- `DkMath.RH.CFBRC.CosmicFormulaZetaArithmeticRadialDominationMarginFrontierAudit`
- `DkMath.RH.CFBRC.PascalCenteredXiArithmeticDefectRepresentation`
- `DkMath.RH.CFBRC.PascalCenteredXiFixedSecondMomentDefectBridge`
- `Mathlib.Tactic`

既存 ordered-limit theorem を再利用し、joint limit を作らない。

---

## 2. Gate A — endpoint / fixed margin を first-class にする

finite margin の極限先を明示するため、例えば次を定義する。

```lean
noncomputable def cfzp016EndpointRadialMargin
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  -4 * Real.pi *
    pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W

noncomputable def cfzp016FixedRadialMargin
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  -4 * Real.pi *
    pascalCenteredXiFixedSecondMomentDefectFunctional W.R
```

固定 `ε > 0` で既存

```lean
tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectApproximant
```

と CFZP-015 の exact identity から

```text
M_X(ε,W) → EndpointMargin(ε,W)
```

を証明する。

同様に既存

```lean
tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_epsilon
```

から

```text
EndpointMargin(ε,W) → FixedMargin(W)
```

を `ε → 0+` の ordered filter で証明する。

ここでは定数倍の Tendsto のみを使う。

---

## 3. Gate B — frequently nonnegative + convergence ⇒ nonnegative limit

一般的な実数補題を module 内 private theorem として証明してよい。

概念形:

```text
f → L along l
and Frequently (0 ≤ f x) along l
implies 0 ≤ L
```

Mathlib に直接 lemma があれば再利用する。無ければ contradiction で証明する。

proof idea:

1. `L < 0` を仮定。
2. `(-∞, 0)` は `L` の neighborhood なので、`Tendsto` から eventually `f x < 0`。
3. `Frequently (0 ≤ f x)` と矛盾。

線形順序 topology の一般 lemma にする必要はない。`ℝ` 専用で十分。

重要:

- `Frequently` を `Eventually` に取り違えない。
- classical choice や subsequence constructionは不要。
- joint `(ε,X)` filterを作らない。

---

## 4. Gate C — fixed ε で cofinal X domination から endpoint sign

例えば proposition:

```lean
def Cfzp016CofinalCutoffRadialDominationAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∃ᶠ X : ℕ in Filter.atTop,
    0 ≤ cfzp015WholeShiftedRadialMargin ε W X
```

を置く。

`0 < ε` とこの proposition から

```text
0 ≤ cfzp016EndpointRadialMargin ε W
```

を証明する。

さらに正の定数 `4π` を使い、同値または少なくとも implication として

```text
0 ≤ EndpointMargin(ε,W)
→ ArithmeticDefectEndpoint(ε,W) ≤ 0
```

を出す。

可能なら exact iff まで出してよい。

---

## 5. Gate D — ε 側も cofinal に弱める

CFZP-015 の

```text
∀ ε > 0, eventually X, margin ≥ 0
```

より弱い frontier を named proposition にする。

推奨 shape:

```lean
def Cfzp016DoublyCofinalRadialDomination
    (W : PascalCenteredXiResidueTransportWindow) : Prop :=
  ∃ᶠ ε : ℝ in 𝓝[>] 0,
    0 < ε ∧
      Cfzp016CofinalCutoffRadialDominationAt ε W
```

`𝓝[>] 0` 自体が positive side filter だが、Lean proof bookkeeping を安定させるため predicate 内に `0 < ε` を明示してよい。

この provider から:

```text
Frequently ε → 0+,
  0 ≤ EndpointMargin(ε,W)
```

を作る。

Gate A の endpoint-margin epsilon convergence と Gate B の frequent-limit lemma を使って

```text
0 ≤ cfzp016FixedRadialMargin W
```

を証明する。

fixed margin の定義から

```text
pascalCenteredXiFixedSecondMomentDefectFunctional W.R ≤ 0
```

へ変換する。

---

## 6. Gate E — safe-radius nonnegativity と合わせて finite-window criticality

既存

```lean
pascalCenteredXiFixedSecondMomentDefectFunctional_nonneg
pascalCenteredXiFixedSecondMomentDefectFunctional_eq_zero_iff
```

を使い、`Cfzp016DoublyCofinalRadialDomination W` から

```text
pascalCenteredXiFixedSecondMomentDefectFunctional W.R = 0
```

および

```text
∀ ρ ∈ pascalCriticalMirrorZeroWindowFinset W.R,
  ρ.re = 1 / 2
```

まで閉じる。

これは finite-window conclusion に留める。

---

## 7. Gate F — CFZP-015 provider から cofinal provider への implication

既存の強い provider

```lean
Cfzp015OrderedFiniteRadialDomination W
```

から

```lean
Cfzp016DoublyCofinalRadialDomination W
```

が従うことを証明できるなら出す。

ただしこの theorem は hierarchy adapter であり、どちらの provider existence も証明しない。

`Eventually P` から `Frequently P` への移行には filter の NeBot 条件が必要になる場合がある。`atTop` on `ℕ` と `𝓝[>] 0` について既存 instance / theorem を使い、無理に一般化しない。

この Gate が Lean bookkeeping 上不自然なら optional としてよい。Gate A〜E が core。

---

## 8. Gate G — frontier marker の sharpen

新しい active marker は eventual domination ではなく doubly-cofinal domination に置き換える。

推奨:

```lean
inductive Cfzp016CofinalArithmeticRadialDominationGap : Prop
  | noIndependentDoublyCofinalRadialDominationProvider
```

roadmap では次を明記する。

```text
CFZP-015 eventual finite radial domination:
  sufficient but stronger than necessary

fixed-ε cutoff frontier:
  cofinally/frequently many nonnegative margins are sufficient

ε→0+ frontier:
  cofinally/frequently many nonnegative endpoint margins are sufficient

active sufficient frontier:
  doubly cofinal radial domination

independent provider:
  OPEN / GAP
```

「minimal」という語を使う場合は、絶対的な論理最小性を主張しない。**current ordered-limit route に対する strictly weakened / sharpened sufficient frontier** と表現する。

---

## 9. 研究上の意味 / 次段候補

この Gate が Green になれば、次に調べるべきは `eventually sign` ではなく、有限 prime-side oscillationが

```text
margin ≥ 0
```

を cofinally 再訪する mechanism である。

その候補として過去 CFZP-006V〜006Y の phase-cell / branch-free sign-cell ledger を再監査する価値がある。ただし本段では接続しない。

特に

- phase-cell coverage
- prime-power arithmetic coverage
- equidistribution
- zero counting

を provider として仮定・捏造しない。

---

## 10. firewall

本段では以下を導入しない。

- `sorry`, `admit`, `axiom`, `native_decide`
- 新しい `Complex.arg`
- global phase branch
- contour deformation provider
- right-edge/top-edge relocation
- infinite Euler product
- joint `(ε,X)` limit
- limit exchange
- unconditional finite margin sign
- unconditional cofinal domination provider
- common-baseline reach witness
- RH または RH-equivalent provider の無条件証明

---

## 11. public import / roadmap

Green の場合:

- `DkMath/RH.lean` に新規 module を公開 import
- `0000-CFZP-roadmap.md` に CFZP-016 を追記

Gate A〜E が exact に閉じ、doubly-cofinal provider existence を未証明 marker として残せれば Green-A としてよい。

---

## 12. 検証

最低限:

```bash
lake env lean lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaCofinalRadialDominationFrontierMinimizationAudit.lean
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
