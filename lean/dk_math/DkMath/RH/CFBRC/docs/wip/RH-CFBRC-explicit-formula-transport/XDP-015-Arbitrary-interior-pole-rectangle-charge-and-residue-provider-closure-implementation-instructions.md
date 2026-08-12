# XDP-015 — Arbitrary interior-pole rectangle charge / residue-provider closure 実装指示書

作成日: 2026-08-12

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-explicit-formula-transport-260812-v0
workdir: lean/dk_math
Lean / Mathlib: repository pinned toolchain
```

XDP-014 は `Strong Green through Gate E` で閉じた。

現在 Green の局所 Cauchy charge は次である。

```lean
theorem pascalRectangleBoundaryIntegral_inv_centeredSquare
    {δ : ℝ} (hδ : 0 < δ) :
    pascalRectangleBoundaryIntegral (fun z : ℂ => z⁻¹)
      (-δ) δ (-δ) δ =
        2 * Real.pi * Complex.I

theorem pascalRectangleBoundaryIntegral_cauchyKernel_centeredSquare
    {p : ℂ} {δ : ℝ} (hδ : 0 < δ) :
    pascalRectangleBoundaryIntegral (fun z : ℂ => (z - p)⁻¹)
      (p.re - δ) (p.re + δ) (p.im - δ) (p.im + δ) =
        2 * Real.pi * Complex.I
```

また XDP-013 で、generic rectangle boundary、vertical / horizontal subdivision、strict-inside square geometry、pole-free rectangle Cauchy–Goursat も Green である。

```lean
pascalRectangleBoundaryIntegral_vertical_split
pascalRectangleBoundaryIntegral_horizontal_split
exists_pascalRectangle_square_radius
pascalRectangleBoundaryIntegral_cauchyKernel_eq_zero_of_not_mem_closed
```

XDP-015 の principal goal は、これらだけを用いて arbitrary interior pole に対する rectangle charge を actual theorem として閉じることである。

```text
p strictly inside rectangle
→ choose positive centered square around p
→ split big rectangle into 3 × 3 finite blocks
→ center block charge = 2πi
→ 8 outer block charges = 0
→ big rectangle charge = 2πi
```

さらに principal goal が Green になった場合は、XDP-012 の coordinate-safe principal-part provider を actual theorem に昇格し、可能なら finite principal-part sum、fixed-Xi rectangle residue formula、circle = rectangle、XDP-011 finite explicit-formula skeleton まで連鎖させる。

本 phase では一般 residue theorem、winding number、homotopy、polygon library、chain complex framework を新設しない。

`T → ∞`、horizontal decay、prime cutoff の積分交換、defect sign、defect vanishing、RH は扱わない。

---

# Gate A — Arbitrary interior-pole rectangle theorem

principal theorem の候補 shape は次とする。

```lean
theorem pascalRectangleBoundaryIntegral_cauchyKernel_eq_two_pi_I_of_mem_open
    {xL xR yB yT : ℝ} {p : ℂ}
    (hp : p ∈ Set.Ioo xL xR ×ℂ Set.Ioo yB yT) :
    pascalRectangleBoundaryIntegral
      (fun z : ℂ => (z - p)⁻¹)
      xL xR yB yT =
        2 * Real.pi * Complex.I
```

必要なら `xL < xR`、`yB < yT` を `hp` から先に取り出して named helper にしてよい。

## A1. 内部 square の選択

必ず既存 theorem を使う。

```lean
exists_pascalRectangle_square_radius hp
```

得られる `δ > 0` と四つの strict margin を named facts に分解する。

```text
xL < p.re - δ
p.re + δ < xR
yB < p.im - δ
p.im + δ < yT
```

新しい radius selection theory は作らない。

---

# Gate B — 3 × 3 finite subdivision assembly

## B1. vertical split を二回

まず `p.re - δ`、次に `p.re + δ` で分割し、三つの vertical strip にする。

概念的には

```text
[xL, xR]
→ [xL, p.re-δ]
 + [p.re-δ, p.re+δ]
 + [p.re+δ, xR]
```

使用する正本 theorem:

```lean
pascalRectangleBoundaryIntegral_vertical_split
```

interval-integrability obligation は Cauchy kernel が各 split line 上で pole を踏まないことから供給する。

必要なら次のような専用 helper を追加してよい。

```lean
intervalIntegrable_cauchyKernel_horizontalEdge_of_im_ne
intervalIntegrable_cauchyKernel_verticalEdge_of_re_ne
```

ただし generic analytic library へ拡張しない。

## B2. 各 strip を horizontal split 二回

各 vertical strip に対して `p.im - δ`、`p.im + δ` で分割し、合計 9 block にする。

概念的には

```text
3 vertical strips × 3 horizontal strips
→ 9 rectangle boundary integrals
```

使用する正本 theorem:

```lean
pascalRectangleBoundaryIntegral_horizontal_split
```

重要:

**内部辺 cancellation を別 theorem として手計算し直さない。**

vertical / horizontal split theorem 自体が、親 rectangle boundary integral を子 rectangle boundary integrals の和に exact に変換する theorem である。したがって XDP-015 では split theorem の反復適用を正本とする。

---

# Gate C — Center block

center block は exact に

```text
[p.re - δ, p.re + δ]
×
[p.im - δ, p.im + δ]
```

である。

ここには既存 theorem をそのまま適用する。

```lean
pascalRectangleBoundaryIntegral_cauchyKernel_centeredSquare hδ
```

従って center block charge は

```text
2 * Real.pi * Complex.I
```

で Green。

新しい square integral proof は書かない。

---

# Gate D — 8 outer blocks vanish

center block 以外の 8 block について、pole `p` が closed rectangle に入らないことを strict margin から証明する。

使用する theorem:

```lean
pascalRectangleBoundaryIntegral_cauchyKernel_eq_zero_of_not_mem_closed
```

各 block の `p ∉ uIcc ×ℂ uIcc` は、少なくとも実部または虚部の一方が block interval から strict に外れることで閉じる。

典型例:

```text
left column:
p.re > p.re - δ
したがって p は [xL, p.re-δ] に入らない

right column:
p.re < p.re + δ
したがって p は [p.re+δ, xR] に入らない

middle/top:
p.im < p.im + δ
したがって p は [p.im+δ, yT] に入らない

middle/bottom:
p.im > p.im - δ
したがって p は [yB, p.im-δ] に入らない
```

8 個すべてを巨大な一発 tactic に押し込まず、column / row 単位の helper を作ってよい。

推奨 helper shape:

```lean
not_mem_closed_left_block_of_delta_pos
not_mem_closed_right_block_of_delta_pos
not_mem_closed_bottom_block_of_delta_pos
not_mem_closed_top_block_of_delta_pos
```

ただし theorem 名は実装に合わせて調整してよい。

---

# Gate E — Assemble arbitrary rectangle charge

9 block の decomposition に Gate C / D を代入し、ring / simp で

```lean
pascalRectangleBoundaryIntegral
  (fun z : ℂ => (z - p)⁻¹)
  xL xR yB yT =
    2 * Real.pi * Complex.I
```

を閉じる。

ここまでが **Minimum Green** である。

Acceptance:

```text
Gate A: arbitrary interior pole statement shaped
Gate B: 3 × 3 split actual theorem chain
Gate C: center block 2πi
Gate D: 8 outer blocks 0
Gate E: arbitrary rectangle charge actual theorem
```

---

# Gate F — Symmetric rectangle specialization

Gate E が Green なら、XDP-012 / XDP-013 の ordinary symmetric rectangleへ specialization する。

必要な pole は centered Xi zero `a` に対する ordinary pole

```lean
pascalCenteredXiOrdinaryPole a
```

である。

`a ∈ pascalCenteredXiZeroDiskFinset W.R` から、strong residue window の same-zero-set contract と boundary safety を使い、ordinary pole が open symmetric rectangle interior にあることを theorem 化する。

候補 theorem:

```lean
theorem pascalCenteredXiOrdinaryPole_mem_rectangleOpen_of_mem_zeroDiskFinset
    (W : PascalCenteredXiResidueTransportWindow)
    {a : ℂ}
    (ha : a ∈ pascalCenteredXiZeroDiskFinset W.R) :
    pascalCenteredXiOrdinaryPole a ∈
      pascalSymmetricRectangleOpen W.rectangle.σ W.rectangle.T
```

ここで boundary point にならないことは rectangle boundary safety から出す。

既存 `zero_mem_iff` は interior contract なので、使える向きを優先する。

---

# Gate G — Actual principal-part charge provider realization

XDP-012 の coordinate-safe provider:

```lean
structure PascalCenteredXiRectanglePrincipalPartChargeProvider
    (h : ℂ → ℂ) (W : PascalCenteredXiResidueTransportWindow) where
  principalPart_boundary_eq : ∀ {a : ℂ},
    a ∈ pascalCenteredXiZeroDiskFinset W.R →
    pascalSymmetricRectangleBoundaryIntegral
      (fun s => pascalCenteredXiWeightedPrincipalPart h a
        (pascalOrdinaryToCentered s))
      W.rectangle.σ W.rectangle.T =
      -(2 * Real.pi * Complex.I) *
        (pascalCenteredXiZeroMultiplicity a : ℂ) * h a
```

を actual theorem から構成する。

使用する bridge:

```lean
pascalCenteredXiWeightedPrincipalPart_comp_toCentered_eq_cauchyKernel
pascalRectangleBoundaryIntegral_symmetric
```

Cauchy kernel charge に constant coefficient

```text
-(multiplicity a) * h a
```

を掛けるだけなので、ここで新しい解析を導入しない。

理想 target:

```lean
theorem exists_pascalCenteredXiRectanglePrincipalPartChargeProvider
    (h : ℂ → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalCenteredXiRectanglePrincipalPartChargeProvider h W
```

provider structure 自体を削除する必要はない。存在 theorem が Green になれば conditional boundary は actual reusable API に昇格する。

ここまでを **Strong Green** とする。

---

# Gate H — Finite principal-part sum charge

Gate G が Green なら finite sum を rectangle boundary integral の有限加法性へ移す。

対象:

```lean
pascalCenteredXiDiskWeightedPrincipalPartSum h W.R
```

ordinary rectangle 上では必ず translation を入れる。

```lean
fun s =>
  pascalCenteredXiDiskWeightedPrincipalPartSum h W.R
    (pascalOrdinaryToCentered s)
```

期待 endpoint:

```text
rectangle boundary integral of principal-part sum
→ sum of one-pole rectangle charges
→ -2πi × pascalCenteredXiZeroDiskWeightedMoment h W.R
```

finite sum と interval integral の交換だけであり、無限和・dominated convergence は使わない。

---

# Gate I — Fixed-Xi rectangle weighted residue formula

XDP-012 で Green 済み:

```lean
pascalCenteredXiRectangleIntegral_diskWeightedRawRegularizer_eq_zero
```

および raw decomposition

```text
weighted Xi integrand
= raw regularizer + principal-part sum
```

を rectangle ordinary-to-centered coordinate 上で組み合わせる。

目標 theorem 候補:

```lean
theorem pascalCenteredXiWeightedRectangleMass_eq
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiRectangleContribution h W.toContourTransportWindow =
      -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment h W.R
```

実際の既存 definition 名・argument order に合わせて調整する。

注意:

`pascalCenteredXiRectangleContribution` は weighted fixed-Xi negative log derivative の canonical centered→ordinary translation wrapper である。coordinate translation を重複して入れない。

---

# Gate J — Circle = rectangle

既存 circle theorem:

```lean
pascalCenteredXiWeightedOuterContourMass_eq
```

と Gate I は同じ

```text
-2πi × pascalCenteredXiZeroDiskWeightedMoment h W.R
```

へ着地する。

従って actual theorem として

```text
rectangle weighted fixed-Xi contribution
=
circle weighted fixed-Xi contribution
```

を閉じる。

候補 theorem:

```lean
theorem pascalCenteredXiWeightedRectangle_eq_outerCircle
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    ...
```

ここでは homotopy / contour deformation を新設しない。共通 finite residue endpoint を経由する equality とする。

---

# Gate K — XDP-011 finite explicit-formula skeleton

Gate J まで Green なら、even centered weight `h` の下で XDP-011 principal theorem

```lean
pascalCenteredXiRectangleContribution_eq_two_right_decomposed_add_two_top
```

と合成する。

期待する finite explicit-formula skeleton:

```text
-2πi × finite Xi zero weighted moment
=
2 × right-edge decomposed contribution
+ 2 × finite top-horizontal contribution
```

候補 theorem shape:

```lean
theorem pascalCenteredXiFiniteExplicitFormulaSkeleton
    {h : ℂ → ℂ}
    (hhDiff : Differentiable ℂ h)
    (hhEven : PascalCenteredEvenWeight h)
    (W : PascalCenteredXiResidueTransportWindow) :
    -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment h W.R =
      2 * (...) +
        2 * pascalCenteredXiTopHorizontalContribution
          h W.toContourTransportWindow
```

right-edge integral の exact body は既存 XDP-011 theorem を再利用し、写経しない。

ここまでを **Ideal Green** とする。

---

# Gate L — Optional Mellin specialization

Ideal Green まで到達した場合のみ、余力があれば

```lean
centeredMellinSecondDifferenceWeight
  (centeredMellinBoxApprox ε) τ
```

を finite explicit-formula skeleton に specialization してよい。

ただし XDP-015 では

```text
τ → 0
ε → 0⁺
prime cutoff X → ∞
T → ∞
```

の任何の limit exchange も行わない。

finite-height / fixed-parameter theorem の specialization のみ許可する。

---

# 禁止事項

XDP-015 では次を禁止する。

```text
sorry
admit
新規 axiom
native_decide
RH を仮定する provider
critical-line concentration を仮定する shortcut
defect = 0 の仮定
T → ∞
prime cutoff と integral の交換
一般 residue / winding / homotopy framework の新設
内部辺 cancellation の別巨大 proof の再実装
```

既存 unrelated warning は XDP-015 の失敗と混同しない。

---

# 実装ファイル候補

principal implementation は既存

```text
DkMath/RH/CFBRC/PascalCenteredXiRectangleCauchyCharge.lean
```

を延長してよい。

XDP-012 downstream residue theorem が大きくなる場合は companion module を分けてよい。

候補:

```text
DkMath/RH/CFBRC/PascalCenteredXiExplicitFormulaRectangleResidueClosure.lean
```

新 module を作成した場合は `DkMath.RH` の public import を追加する。

---

# Result report

必ず次を作成する。

```text
DkMath/RH/CFBRC/docs/wip/RH-CFBRC-explicit-formula-transport/
XDP-015-Arbitrary-interior-pole-rectangle-charge-and-residue-provider-closure-result.md
```

最低限、次を記録する。

```text
Gate A–E arbitrary rectangle charge status
Gate F ordinary Xi pole interior status
Gate G provider realization status
Gate H finite principal-part sum status
Gate I rectangle residue formula status
Gate J circle=rectangle status
Gate K finite explicit-formula skeleton status
残った blocker の exact theorem / proof obligation
no-circularity audit
build / axioms audit
```

XDP-012 / XDP-013 / XDP-014 result report に migration addendum を追加する場合は、既存記録を削除せず追記形式にする。

---

# Validation

最低限:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiRectangleCauchyCharge.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiRectangleCauchyCharge
./lb DkMath.RH
git diff --check
```

companion module を追加した場合はその module も個別 build する。

principal theorem 群について `#print axioms` を確認する。

期待範囲:

```text
[propext, Classical.choice, Quot.sound]
```

新規 source に

```text
sorry
admit
axiom
native_decide
```

が存在しないことを確認する。

---

# Phase acceptance

## Minimum Green

```text
arbitrary interior-pole rectangle Cauchy charge = 2πi
```

## Strong Green

```text
Minimum Green
+ ordinary Xi pole specialization
+ coordinate-safe principal-part provider existence
```

## Ideal Green

```text
Strong Green
+ finite principal-part sum charge
+ fixed-Xi rectangle residue formula
+ circle = rectangle
+ XDP-011 finite explicit-formula skeleton
```

Ideal Green まで閉じても RH は未証明である。

次 frontier はその時点で初めて、right-edge ordinary-zeta integral を Pascal / von Mangoldt finite cutoff integralへ transport する問題と、finite top-horizontal correction の扱いへ移る。