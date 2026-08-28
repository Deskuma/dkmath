# XDP-016 — Finite rectangle principal-part sum / fixed-Xi residue assembly 実装指示書

作成日: 2026-08-12

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-explicit-formula-transport-260812-v0
workdir: lean/dk_math
Lean / Mathlib: repository pinned toolchain
```

XDP-015 は `Strong Green through Gate G` で閉じた。

現在 Green の residue-side chain は次である。

```text
square Cauchy charge
→ arbitrary interior-pole rectangle charge
→ centered Xi zero の ordinary-pole localization
→ coordinate-safe principal-part charge provider existence
```

主要 endpoint:

```lean
pascalRectangleBoundaryIntegral_cauchyKernel_eq_two_pi_I_of_mem_open

pascalCenteredXiOrdinaryPole_mem_rectangleOpen_of_mem_zeroDiskFinset

exists_pascalCenteredXiRectanglePrincipalPartChargeProvider
```

XDP-012 ではさらに、fixed centered-Xi の disk regularizer を ordinary rectangle へ pull back し、

```lean
pascalCenteredXiRectangleIntegral_diskWeightedRegularizer_eq_zero
pascalCenteredXiDiskWeightedRegularizer_eq_raw_on_rectangleBoundary
pascalCenteredXiRectangleIntegral_diskWeightedRawRegularizer_eq_zero
```

まで Green である。

circle 側では既に

```lean
circleIntegral_pascalCenteredXiDiskWeightedPrincipalPartSum_eq
pascalCenteredXiWeightedOuterContourMass_eq
```

により、finite principal-part sum と weighted Xi outer contour が同じ finite weighted zero moment へ接続されている。

XDP-016 の目的は、**rectangle 側に残った finite-sum linearity / raw decomposition bridge を actual theorem として閉じ、XDP-012〜015 の residue transport 系を closure すること**である。

principal target は次である。

```text
finite principal-part sum rectangle charge
→ fixed-Xi rectangle weighted residue formula
→ fixed Xi circle = fixed Xi rectangle
→ XDP-011 finite explicit-formula skeleton
```

理想 endpoint:

```text
-2πi × finite Xi weighted zero moment
=
2 × right-edge decomposed contribution
+ 2 × finite top-horizontal contribution
```

本 phase では `T → ∞`、horizontal decay、prime cutoff と interval integral の極限交換、defect sign / defect vanishing、RH は扱わない。

---

# Gate 0 — Mandatory coordinate-integrability audit / legacy contract repair

## 0.1 centered / ordinary を混同しない

rectangle boundary の parameter point は ordinary coordinate `s` である。

以下の centered functions を rectangle へ入れる場合は必ず

```lean
fun s => F (pascalOrdinaryToCentered s)
```

とする。

対象:

```lean
pascalCenteredXiWeightedNegLogDeriv h
pascalCenteredXiDiskWeightedRawRegularizer h R
pascalCenteredXiDiskWeightedPrincipalPartSum h R
pascalCenteredXiWeightedPrincipalPart h a
```

XDP-010 / XDP-013 で修正した coordinate discipline を崩さないこと。

## 0.2 XDP-009 legacy provider の boundary_integrable contract を修正

現状 `PascalExplicitFormulaContourTransportProvider` は rectangle contribution 自体は centered→ordinary translation を行う一方、`boundary_integrable` field が raw `F` を ordinary edge に直接渡す旧 shape のまま残っている。

current shape:

```lean
boundary_integrable :
  PascalSymmetricRectangleBoundaryIntegrable F
    W.rectangle.σ W.rectangle.T
```

coordinate-safe shape は概念的に

```lean
boundary_integrable :
  PascalSymmetricRectangleBoundaryIntegrable
    (fun s => F (pascalOrdinaryToCentered s))
    W.rectangle.σ W.rectangle.T
```

である。

この phase で可能なら actual structure field を修正し、dependent declarations を build Green に戻すこと。

もし既存 surface への破壊的変更が広すぎる場合は、最低でも named coordinate-safe wrapper / replacement structure を追加し、**XDP-016 の proof では旧 field を使用しないこと**。result report に migration status を明記する。

---

# Gate A — Rectangle boundary linearity API

XDP-016 で必要なのは general contour framework ではなく、既存

```lean
pascalSymmetricRectangleBoundaryIntegral
PascalSymmetricRectangleBoundaryIntegrable
```

に対する有限線形性だけである。

まず次を audit する。

```text
intervalIntegral.integral_add
intervalIntegral.integral_sub
intervalIntegral.integral_const_mul
intervalIntegral.integral_finset_sum あるいは equivalent pinned lemma
```

使える pinned finite-sum theorem があれば優先して使う。

無ければ Finset induction で小さな local helper を作ってよい。

推奨 generic helper:

```lean
pascalSymmetricRectangleBoundaryIntegral_add
pascalSymmetricRectangleBoundaryIntegral_finset_sum
```

あるいは必要最小限の specialized helper でもよい。

要求:

- right / top / left / bottom の4辺すべてで必要な `IntervalIntegrable` を明示する。
- integrability hypothesis を落として `integral_add` を乱用しない。
- orientation は既存 `pascalSymmetricRectangleBoundaryIntegral` の定義に従う。
- vertical edge の `* Complex.I` を忘れない。

Acceptance:

```text
Gate A Green:
rectangle boundary integral で add と finite sum を合法に交換できる actual theorem がある。
```

---

# Gate B — One principal part is rectangle-boundary integrable

`W : PascalCenteredXiResidueTransportWindow`、
`a ∈ pascalCenteredXiZeroDiskFinset W.R` とする。

XDP-015 で

```lean
pascalCenteredXiOrdinaryPole_mem_rectangleOpen_of_mem_zeroDiskFinset
```

が Green なので ordinary pole

```lean
p := pascalCenteredXiOrdinaryPole a
```

は rectangle の open interior にある。

XDP-015 既存 helper

```lean
intervalIntegrable_cauchyKernel_horizontal_of_im_ne
intervalIntegrable_cauchyKernel_vertical_of_re_ne
```

と coordinate bridge

```lean
pascalCenteredXiWeightedPrincipalPart_comp_toCentered_eq_cauchyKernel
```

を使い、各 edge で

```lean
fun s =>
  pascalCenteredXiWeightedPrincipalPart h a
    (pascalOrdinaryToCentered s)
```

が interval-integrable であることを示す。

推奨 theorem:

```lean
pascalCenteredXiRectangleBoundaryIntegrable_weightedPrincipalPart
    (h : ℂ → ℂ)
    (W : PascalCenteredXiResidueTransportWindow)
    {a : ℂ}
    (ha : a ∈ pascalCenteredXiZeroDiskFinset W.R) :
    PascalSymmetricRectangleBoundaryIntegrable
      (fun s => pascalCenteredXiWeightedPrincipalPart h a
        (pascalOrdinaryToCentered s))
      W.rectangle.σ W.rectangle.T
```

係数

```text
-(multiplicity a : ℂ) * h a
```

は constant factor として処理する。

---

# Gate C — Finite principal-part sum integrability and charge

定義:

```lean
pascalCenteredXiDiskWeightedPrincipalPartSum h W.R
```

を ordinary rectangle へ pull back する。

目標1:

```lean
pascalCenteredXiRectangleBoundaryIntegrable_diskWeightedPrincipalPartSum
```

目標2:

```lean
pascalCenteredXiRectangleIntegral_diskWeightedPrincipalPartSum_eq
```

概念式:

```text
∮Rect Σ_a PP_a
= Σ_a ∮Rect PP_a
= Σ_a (-2πi * m_a * h(a))
= -2πi * pascalCenteredXiZeroDiskWeightedMoment h W.R
```

Gate G の actual provider theorem

```lean
exists_pascalCenteredXiRectanglePrincipalPartChargeProvider h W
```

を使ってよい。

ただし provider field を「有限和 charge theorem」そのものとして読み替えないこと。finite sum と interval integral の交換は Gate A/B で actual に証明する。

最終 scalar algebra は circle 側

```lean
circleIntegral_pascalCenteredXiDiskWeightedPrincipalPartSum_eq
```

の Finset.sum / Finset.mul_sum pattern を参考にしてよい。

Acceptance:

```text
Gate C Green:
rectangle principal-part finite sum = -2πi × finite weighted zero moment
```

---

# Gate D — Raw regularizer boundary integrability

XDP-012 では already Green:

```lean
pascalCenteredXiRectangleIntegral_diskWeightedRawRegularizer_eq_zero
```

ただし raw + principal-part decomposition に `integral_add` を使うため、raw pullback の boundary integrability を named theorem として供給する。

推奨 theorem:

```lean
pascalCenteredXiRectangleBoundaryIntegrable_diskWeightedRawRegularizer
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalSymmetricRectangleBoundaryIntegrable
      (fun s => pascalCenteredXiDiskWeightedRawRegularizer h W.R
        (pascalOrdinaryToCentered s))
      W.rectangle.σ W.rectangle.T
```

最短 route は XDP-012 の

```lean
pascalCenteredXiDiskWeightedRegularizer_eq_raw_on_rectangleBoundary
```

と patched regularizer の closed-rectangle continuity を利用すること。

各 edge で patched pullback は continuous、従って interval-integrable。
境界上の pointwise equality で raw へ congruence する。

raw の zero integral theoremを integrability の代用にしないこと。

---

# Gate E — Coordinate-safe raw decomposition on the rectangle

定義から centered coordinate `z` では pointwise に

```text
h z * pascalCenteredXiNegLogDeriv z
=
pascalCenteredXiDiskWeightedRawRegularizer h W.R z
+
pascalCenteredXiDiskWeightedPrincipalPartSum h W.R z
```

が成立する。

これを ordinary rectangle 上へ pull back した named theorem を作る。

推奨:

```lean
pascalCenteredXiWeightedNegLogDeriv_comp_toCentered_eq_raw_add_principalPartSum
```

概念 shape:

```lean
∀ s,
  pascalCenteredXiWeightedNegLogDeriv h
      (pascalOrdinaryToCentered s)
  =
    pascalCenteredXiDiskWeightedRawRegularizer h W.R
      (pascalOrdinaryToCentered s)
    +
    pascalCenteredXiDiskWeightedPrincipalPartSum h W.R
      (pascalOrdinaryToCentered s)
```

これは analytic theorem ではなく definition unfolding + ring で閉じるはずである。

---

# Gate F — Fixed-Xi rectangle weighted residue formula

Gate C/D/E を assembly する。

推奨 principal theorem:

```lean
pascalCenteredXiWeightedRectangleContribution_eq
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiRectangleContribution
      h W.toContourTransportWindow
    =
      -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment h W.R
```

名前は repository conventions に合わせて調整してよい。

proof skeleton:

```text
rectangle weighted Xi
= rectangle (raw + principal-part sum)
= rectangle raw + rectangle principal-part sum
= 0 + (-2πi × weighted moment)
= -2πi × weighted moment
```

ここで

```lean
pascalCenteredXiRectangleContribution h ...
```

は centered observable を canonical ordinary rectangle へ translation する既存 wrapper である。

手作業で別の rectangle integrand を再定義しないこと。

Acceptance:

```text
Gate F Green:
combined fixed-Xi rectangle residue formula is an actual theorem.
```

---

# Gate G — Circle = rectangle bridge

circle side existing theorem:

```lean
pascalCenteredXiWeightedOuterContourMass_eq
    hh W.circle_safe
```

rectangle side Gate F theoremは同じ

```lean
-(2 * Real.pi * Complex.I) *
  pascalCenteredXiZeroDiskWeightedMoment h W.R
```

へ到達する。

従って actual theorem:

```lean
pascalCenteredXiWeightedRectangleContribution_eq_outerContourMass
```

または同等の命名で

```text
fixed Xi rectangle = fixed Xi centered circle
```

を閉じる。

この theorem は direct homotopy theorem ではない。
**common finite residue endpoint を介する equality** と docstring に明記する。

---

# Gate H — XDP-011 finite explicit-formula skeleton

`h` が even centered weight であることも仮定する。

既存 XDP-011:

```lean
pascalCenteredXiRectangleContribution_eq_two_right_decomposed_add_two_top
```

と Gate F を合成する。

principal endpoint:

```lean
pascalCenteredXiFiniteExplicitFormulaSkeleton
    {h : ℂ → ℂ}
    (hdiff : Differentiable ℂ h)
    (heven : PascalCenteredEvenWeight h)
    (W : PascalCenteredXiResidueTransportWindow) :
    -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment h W.R
      =
        2 * (∫ t in (-W.rectangle.T)..W.rectangle.T,
          (h (pascalOrdinaryToCentered
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            pascalXiDecomposedNegLogDeriv
              (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
            Complex.I) +
        2 * pascalCenteredXiTopHorizontalContribution
          h W.toContourTransportWindow
```

左右の orientation / equality の向きは existing theorem に合わせる。

必要なら rectangle contribution を intermediate equality に置き、`rw` / `calc` で繋ぐ。

**horizontal term は finite `T` のまま残す。**

`T → ∞`、horizontal vanishing を導入しない。

---

# Gate I — Optional normalized and `z ^ 2` specializations

Gate H まで Green の後、余力があれば以下を追加してよい。

## I.1 normalized weighted form

`(2 * π * I)⁻¹` を掛けた finite explicit formula。

## I.2 quadratic weight

既存

```lean
pascalCenteredXiSecondWeight
```

または repository の `z ^ 2` canonical weight を用い、fixed second contour / centered second moment と接続する。

ただし、この specialization から defect vanishing を導いてはならない。

目的は explicit-formula transport surface を fixed-defect chain に近づけることだけである。

---

# Gate J — Documentation / migration closure

result report:

```text
XDP-016-Finite-rectangle-principal-part-sum-and-fixed-Xi-residue-assembly-result.md
```

を作成する。

XDP-012〜015 の result report へ必要な addendum を入れてよい。

最低限、次を記録する。

```text
one-pole rectangle charge: GREEN
provider existence: GREEN
finite principal-part sum rectangle charge: GREEN / BLOCKED
raw decomposition assembly: GREEN / BLOCKED
fixed-Xi rectangle residue formula: GREEN / BLOCKED
circle = rectangle: GREEN / BLOCKED
finite explicit-formula skeleton: GREEN / BLOCKED
```

旧 XDP-009 `boundary_integrable` coordinate contract の migration 状況も明記する。

---

# Acceptance levels

## Minimum Green

```text
Gate A–C
finite principal-part sum rectangle charge
```

まで actual theorem。

## Strong Green

```text
Gate A–G
fixed-Xi rectangle residue formula
circle = rectangle
```

まで actual theorem。

## Ideal Green

```text
Gate A–H
finite explicit-formula skeleton
```

まで actual theorem。

XDP-016 の推奨判定は **Ideal Green** を狙う。

---

# 禁止事項

以下を導入しない。

```text
sorry
admit
new axiom
native_decide による analytic fact の代用
unproved provider existence
RH
critical-line concentration
horizontal energy vanishing
defect vanishing
T → ∞ under fixed same-zero-set window
horizontal term = 0
prime cutoff ↔ interval integral exchange
```

また、circle finite-sum theorem を rectangle theorem として読み替えない。
rectangle では rectangle edge integrability / finite-sum interchange を actual に証明する。

---

# Validation

最低限:

```text
lake env lean <new-or-updated-module>.lean
lake build DkMath.RH.CFBRC.<target-module>
lake build DkMath.RH
git diff --check
```

principal theorem 群に対して

```lean
#print axioms ...
```

を実行する。

新規 source について

```text
sorry
admit
axiom
native_decide
```

の禁止宣言検索を実施する。

既存 unrelated warning は新規 XDP-016 warning と区別して result report に記録する。

---

# XDP-016 完了後の frontier

Ideal Green なら residue/deformation 系は閉幕とする。

次の principal frontier は

```text
right-edge decomposed integral
→ ordinary-zeta right-edge integral
→ finite Pascal / von Mangoldt cutoff integral
→ cutoff limit / interval integral transport audit
```

である。

horizontal finite correction は別 ledger として保持し、right-edge arithmetic transport と混ぜない。
