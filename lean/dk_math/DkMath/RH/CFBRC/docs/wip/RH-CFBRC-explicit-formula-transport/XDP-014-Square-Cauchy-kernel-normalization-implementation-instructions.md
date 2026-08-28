# XDP-014 — Square Cauchy-kernel normalization 実装指示書

作成日: 2026-08-12

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-explicit-formula-transport-260812-v0
workdir: lean/dk_math
Lean / Mathlib: repository pinned toolchain
```

XDP-013 は `Partial Green` で閉じた。

Green surface は次である。

```text
coordinate-safe centered/ordinary principal-part bridge
→ generic axis-aligned rectangle boundary integral
→ vertical / horizontal finite subdivision algebra
→ strict-inside square geometry
→ pole-free rectangle Cauchy–Goursat
```

残った blocker は一般 residue theory ではない。正の半辺長 `δ` に対する局所正方形の Cauchy kernel normalization

```text
pascalRectangleBoundaryIntegral (fun z : ℂ => z⁻¹)
  (-δ) δ (-δ) δ
= 2 * Real.pi * Complex.I
```

だけである。

XDP-014 の目的は、この micro-lemma を pinned Mathlib の interval integral / real arctangent API で actual theorem として閉じることである。

**本 phase では一般 winding number、一般 residue theorem、一般 homotopy library、contour deformation framework を新設しない。**

また、prime-side transport、horizontal decay、`T → ∞`、defect sign、defect vanishing、RH は扱わない。

---

# 1. Principal target

最優先 theorem shape は次とする。

```lean
theorem pascalRectangleBoundaryIntegral_inv_centeredSquare
    {δ : ℝ} (hδ : 0 < δ) :
    pascalRectangleBoundaryIntegral (fun z : ℂ => z⁻¹)
      (-δ) δ (-δ) δ =
        2 * Real.pi * Complex.I := by
  ...
```

必要なら名前は repository style に合わせて調整してよいが、意味は変えない。

同値な centered Cauchy-kernel 版も companion theorem として許可する。

```lean
theorem pascalRectangleBoundaryIntegral_cauchyKernel_centeredSquare
    {p : ℂ} {δ : ℝ} (hδ : 0 < δ) :
    pascalRectangleBoundaryIntegral (fun z : ℂ => (z - p)⁻¹)
      (p.re - δ) (p.re + δ) (p.im - δ) (p.im + δ) =
        2 * Real.pi * Complex.I
```

ただし principal implementation はまず `p = 0` の正規化を閉じ、その後 translation で一般 `p` へ運ぶ方針を優先する。

---

# Gate A — Four-edge explicit normal forms

`pascalRectangleBoundaryIntegral` の定義を展開し、正方形四辺を named helper に分離してよい。

推奨 helper shape:

```lean
noncomputable def pascalSquareBottomInvIntegral (δ : ℝ) : ℂ := ...
noncomputable def pascalSquareTopInvIntegral (δ : ℝ) : ℂ := ...
noncomputable def pascalSquareRightInvIntegral (δ : ℝ) : ℂ := ...
noncomputable def pascalSquareLeftInvIntegral (δ : ℝ) : ℂ := ...
```

ただし API を増やしすぎない。proof-local `have` で十分なら public definition にしない。

各辺で complex inverse を explicit rational form へ落とす。

例えば bottom edge は

```text
z = x - δ I
```

なので、`δ > 0` から denominator nonzero を示し、概念的に

\[
(x-i\delta)^{-1}
=
\frac{x+i\delta}{x^2+\delta^2}
\]

へ正規化する。

同様に top / right / left も実装する。

### 必須注意

- `Complex.inv_def`、`Complex.normSq_apply`、`Complex.ext`、`field_simp` 等、pinned toolchain で最も安定する形を選ぶ。
- denominator nonzero は `δ > 0` から直接示す。
- totalized inverse を pole 上で評価する必要はない。各辺は `δ > 0` により `0` を通らない。
- complex integral を直接 `norm_num` で押し切らない。

---

# Gate B — Opposite-edge pairing

四辺を個別に最後まで積分するより、対向辺を先に pairing することを第一候補とする。

目標 normal form は概念的に

```text
bottom contribution + top contribution
→ 2 * I * δ * ∫ x in -δ..δ, (x^2 + δ^2)⁻¹
```

および

```text
right contribution + left contribution
→ 2 * I * δ * ∫ y in -δ..δ, (y^2 + δ^2)⁻¹
```

である。

両者は同じ実数積分へ落ちるため、四辺全体は

\[
4i\delta
\int_{-\delta}^{\delta}
\frac{dt}{t^2+\delta^2}
\]

となる。

Lean では必要に応じて次を使う。

```text
intervalIntegral.integral_add
intervalIntegral.integral_sub
intervalIntegral.integral_mul_const
intervalIntegral.integral_const_mul
intervalIntegral.integral_neg
intervalIntegral.integral_congr
Complex.ext
```

実数値関数を `ℂ` へ coe した積分の変換が必要なら、既存 lemma を audit して使う。見つからなければ小さな coercion helper を作る。

---

# Gate C — Real integral normalization

最重要 real scalar lemma を独立に切ることを推奨する。

```lean
theorem integral_inv_sq_add_sq_neg_delta_delta
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ t in (-δ)..δ, (t ^ 2 + δ ^ 2)⁻¹) =
      Real.pi / (2 * δ) := by
  ...
```

repository 内で名前衝突する場合は prefix を付ける。

pinned Mathlib の候補 API:

```text
integral_inv_sq_add_sq
Real.arctan_one
Real.arctan_neg
Real.arctan_zero
Real.pi_pos
```

`integral_inv_sq_add_sq` の exact statement は `#check` / `#print` で確認してから proof を組むこと。

必要なら scale 変数の theorem ではなく、既存 theorem の endpoints を `-δ`, `δ` に specialize する。

### 期待する数学 normal form

\[
\int_{-\delta}^{\delta}
\frac{dt}{t^2+\delta^2}
=
\frac{1}{\delta}
\left(
\arctan(1)-\arctan(-1)
\right)
=
\frac{\pi}{2\delta}.
\]

Lean では `hδ.ne'`、`abs_of_pos hδ`、`field_simp`、`ring_nf` を使ってよい。

---

# Gate D — Square normalization assembly

Gate B と Gate C を合成し、principal target を閉じる。

概念的には

\[
4i\delta
\cdot
\frac{\pi}{2\delta}
=
2\pi i.
\]

ここでは `δ ≠ 0` を `hδ.ne'` から供給し、最終 algebra は `field_simp` / `ring` でよい。

Principal theorem が Green になるまで、XDP-012 provider realization へ進まない。

---

# Gate E — Translation to an arbitrary pole

Principal square normalizationが Green になった後、任意の pole `p : ℂ` に対する translated-square theorem を追加する。

目標:

```lean
theorem pascalRectangleBoundaryIntegral_cauchyKernel_square
    {p : ℂ} {δ : ℝ} (hδ : 0 < δ) :
    pascalRectangleBoundaryIntegral (fun z : ℂ => (z - p)⁻¹)
      (p.re - δ) (p.re + δ)
      (p.im - δ) (p.im + δ) =
        2 * Real.pi * Complex.I := by
  ...
```

実装は各辺への translation を直接 simplification してもよい。一般 contour translation theorem は作らない。

---

# Gate F — Close the XDP-013 one-pole rectangle theorem

XDP-013 の subdivision machinery と Gate E を使い、任意の open rectangle 内 pole に対して actual theorem を閉じる。

principal shape:

```lean
theorem pascalRectangleBoundaryIntegral_cauchyKernel_eq_two_pi_I_of_mem_open
    {xL xR yB yT : ℝ} {p : ℂ}
    (hp : p ∈ Set.Ioo xL xR ×ℂ Set.Ioo yB yT) :
    pascalRectangleBoundaryIntegral (fun z : ℂ => (z - p)⁻¹)
      xL xR yB yT =
        2 * Real.pi * Complex.I := by
  ...
```

必要に応じて `xL < xR`, `yB < yT` を `hp` から導出する。

XDP-013 の

```lean
exists_pascalRectangle_square_radius
pascalRectangleBoundaryIntegral_vertical_split
pascalRectangleBoundaryIntegral_horizontal_split
pascalRectangleBoundaryIntegral_cauchyKernel_eq_zero_of_not_mem_closed
```

を再利用する。

### 推奨 subdivision

pole-centered square の boundaries

```text
p.re - δ
p.re + δ
p.im - δ
p.im + δ
```

で big rectangle を最大 9 blocks へ分割する。

中央 block の charge は Gate E。
その他 block は pole が closed rectangle に入らないことを示して Gate E1 の zero theorem を使う。

内部 boundary cancellation は既存 vertical/horizontal split theorem に任せる。

**手計算で 8 block の boundary を全展開しない。**

---

# Gate G — Realize the coordinate-safe XDP-012 provider

one-pole theorem が Green になったら、XDP-012 の

```lean
PascalCenteredXiRectanglePrincipalPartChargeProvider
```

の actual constructor theorem を実装する。

推奨 shape:

```lean
theorem exists_pascalCenteredXiRectanglePrincipalPartChargeProvider
    (h : ℂ → ℂ)
    (W : PascalCenteredXiResidueTransportWindow) :
    Nonempty (PascalCenteredXiRectanglePrincipalPartChargeProvider h W) := by
  ...
```

またはより直接に constructor:

```lean
noncomputable def pascalCenteredXiRectanglePrincipalPartChargeProvider
    ... : PascalCenteredXiRectanglePrincipalPartChargeProvider h W := ...
```

ただし、既存 structure 名と衝突するので命名は repository style に合わせる。

ここでは `a ∈ pascalCenteredXiZeroDiskFinset W.R` から ordinary pole

```lean
pascalCenteredXiOrdinaryPole a
```

が open rectangle 内にあることを `W.zero_mem_iff` と boundary safety / existing membership bridge から供給する。

その後

```lean
pascalCenteredXiWeightedPrincipalPart_comp_toCentered_eq_cauchyKernel
```

で constant coefficient を Cauchy kernel の外へ出し、one-pole charge theorem を適用する。

符号は必ず監査する。

期待値:

\[
\int_{\partial\mathcal R}
\operatorname{PP}_a
=
-2\pi i\,m_a h(a).
\]

---

# Gate H — Optional immediate downstream closure

Gate G が Green で、残りが単純な finite-sum algebra のみなら、この checkpoint 内で次まで閉じてよい。

1. rectangle principal-part finite sum charge
2. fixed-Xi weighted rectangle residue formula
3. circle = rectangle bridge
4. XDP-011 finite explicit-formula skeleton

ただし無理に scope を広げない。

最低 acceptance endpoint は Gate D、理想 endpoint は Gate G/H である。

もし Gate D の square normalization が閉じたが 9-block subdivision が長大化する場合、そこで phase close してよい。その場合 result report に exact next blocker を書く。

---

# Forbidden shortcuts

次は禁止する。

```text
- `sorry`
- `admit`
- new `axiom`
- `native_decide`
- provider existence の無根拠仮定
- `∮ dz/z = 2πi` をコメントだけで利用
- circle residue theorem を rectangle charge の代用として rewrite
- general residue / winding framework の新設
- RH または RH-equivalent assumption の導入
```

`Complex.log` の branch jump を暗黙に使って四辺 charge を証明するのも避ける。今回の route は real rational integral + arctan normalization を正本とする。

---

# Expected implementation location

主実装は既存

```text
DkMath/RH/CFBRC/PascalCenteredXiRectangleCauchyCharge.lean
```

を拡張することを第一候補とする。

proof が大きくなりすぎる場合のみ、generic analysis helper を

```text
DkMath/Analysis/ComplexRectangleCauchyKernel.lean
```

等へ分離してよい。ただし RH / Xi specific symbol を generic Analysis module から import しない。

XDP-012 provider realization は

```text
DkMath/RH/CFBRC/PascalCenteredXiExplicitFormulaRectangleResidueTransport.lean
```

側に置いてよい。

必要な public import を `DkMath/RH.lean` に追加する。

---

# Result report

作業後、次を作成する。

```text
lean/dk_math/DkMath/RH/CFBRC/docs/wip/RH-CFBRC-explicit-formula-transport/
XDP-014-Square-Cauchy-kernel-normalization-result.md
```

result report には最低限次を記録する。

```text
1. square normalization の Gate 判定
2. 使用した pinned Mathlib integral / arctan API
3. four-edge complex inverse の normal form
4. real scalar integral theorem の exact statement
5. translated-square theorem の有無
6. general one-pole rectangle theorem の有無
7. XDP-012 provider realization の有無
8. downstream residue/circle=rectangle closure の有無
9. no-circularity / no-shortcut audit
10. build / test / #print axioms / git diff --check
```

もし Partial Green なら、`Blocked` を抽象語で書かず、失敗した theorem shape と Mathlib normal form の差を具体的に記録する。

---

# Validation

最低限:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiRectangleCauchyCharge.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiRectangleCauchyCharge
./lb DkMath.RH
git diff --check
```

principal theorem に対して `#print axioms` を確認する。

新規 source について次を検索する。

```text
sorry
admit
axiom
native_decide
```

既存 unrelated warning は result report で分離する。

---

# Phase success criteria

## Minimum Green

```text
δ > 0
→ square boundary Cauchy kernel charge = 2πi
```

## Strong Green

```text
square charge
→ arbitrary interior-pole rectangle charge
→ actual XDP-012 principal-part provider
```

## Ideal Green

```text
actual provider
→ finite principal-part sum
→ fixed-Xi rectangle residue formula
→ circle = rectangle
→ XDP-011 finite explicit-formula skeleton
```

Ideal endpoint が閉じれば、zero side と finite rectangle side の analytic transport は provider-free となり、次 phase から right-edge prime transport を principal frontier に昇格できる。
