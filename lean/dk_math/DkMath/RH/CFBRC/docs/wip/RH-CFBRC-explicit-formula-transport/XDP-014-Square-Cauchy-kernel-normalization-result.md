# XDP-014 — Square Cauchy-kernel normalization result

作成日: 2026-08-12

## Phase close

判定は `Strong Green through Gate E` である。

XDP-013 で残っていた正方形上の Cauchy kernel normalization を、pinned
Mathlib の実数区間積分と arctangent API による actual theorem として閉じた。
translated-square theorem も閉じた。XDP-014 の Gate F 以降は、指示書が許容する
phase boundary に従い、3×3 finite subdivision を次の exact blocker として残した。

## 1. Square normalization

主 theorem は次である。

```lean
pascalRectangleBoundaryIntegral_inv_centeredSquare
    {δ : ℝ} (hδ : 0 < δ) :
    pascalRectangleBoundaryIntegral (fun z : ℂ => z⁻¹)
      (-δ) δ (-δ) δ = 2 * Real.pi * Complex.I
```

証明は次の順序で行う。

1. bottom/top と right/left の対向辺を pointwise rational identity にする。
2. 各対向辺を同じ実数 scalar integralへ変換する。
3. `4 * I * δ` と scalar integral を assembly する。
4. `4 * I * δ * (π / (2 * δ)) = 2 * π * I` を `field_simp` と algebra で閉じる。

## 2. Pinned integral and arctangent API

使用した pinned theorem は次である。

```lean
integral_inv_sq_add_sq
Real.arctan_one
Real.arctan_neg
```

独立の scalar theorem は次である。

```lean
integral_inv_sq_add_sq_neg_delta_delta
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ t in (-δ)..δ, (t ^ 2 + δ ^ 2)⁻¹) =
      Real.pi / (2 * δ)
```

`integral_inv_sq_add_sq` の denominator order `δ^2 + t^2` と、対象の
`t^2 + δ^2` は pointwise function equality で接続した。`hδ.ne'` は denominator
と最終的な `δ` の非零性に使用した。

## 3. Four-edge complex normal forms

bottom/top の pointwise form は次である。

```lean
pascalSquare_inv_bottom_top_pointwise
pascalSquare_inv_bottom_top_integral
```

概念的には

```text
(x - δ I)⁻¹ - (x + δ I)⁻¹
  = (2 δ I) * (x² + δ²)⁻¹
```

right/left は vertical-edge orientation factor を含めて次である。

```lean
pascalSquare_inv_right_left_pointwise
pascalSquare_inv_right_left_unweighted_pointwise
pascalSquare_inv_right_left_integral
```

概念的には

```text
I * (δ + y I)⁻¹ - I * (-δ + y I)⁻¹
  = (2 δ I) * (y² + δ²)⁻¹
```

inverse は `Complex.ofReal_inv`、`Complex.I_pow_three` 相当の pinned complex
algebra、`field_simp`、`Complex.ext` で処理した。各 edge の denominator nonzero
は `δ > 0` から直接供給し、pole 上の totalized inverse を使用していない。

## 4. Translated square

任意の pole への companion theorem も closed である。

```lean
pascalRectangleBoundaryIntegral_cauchyKernel_centeredSquare
    {p : ℂ} {δ : ℝ} (hδ : 0 < δ) :
    pascalRectangleBoundaryIntegral (fun z : ℂ => (z - p)⁻¹)
      (p.re - δ) (p.re + δ) (p.im - δ) (p.im + δ) =
      2 * Real.pi * Complex.I
```

各辺を `intervalIntegral.integral_comp_sub_right` で real coordinate translation
し、proof-local function equality で `z - p` を centered edge の形へ変換した。
一般の contour translation theorem は追加していない。

## 5. Gate F and downstream status

XDP-013 の Gate F、すなわち

```lean
pascalRectangleBoundaryIntegral_cauchyKernel_eq_two_pi_I_of_mem_open
```

相当の arbitrary interior-pole rectangle theorem は、この phase では未実装で
ある。必要な next step は、XDP-013 の vertical/horizontal split theorem を
`p.re - δ`, `p.re + δ`, `p.im - δ`, `p.im + δ` で 3×3 に反復適用する有限 algebra
である。center square 以外の 8 block に対して
`pascalRectangleBoundaryIntegral_cauchyKernel_eq_zero_of_not_mem_closed` を適用し、
内部辺を cancellation するところが exact next blocker である。

Gate F をまだ仮定していないため、次も意図的に未実装である。

```text
XDP-012 actual principal-part provider: not realized
finite principal-part sum: not realized
fixed-Xi rectangle residue formula: not realized
circle = rectangle: not realized
XDP-011 explicit-formula skeleton: not realized
```

## 6. No-circularity / no-shortcut audit

一般 residue、winding number、homotopy、contour deformation、`Complex.log` の
branch jump、RH、zero concentration、defect vanishing、prime-side transport、
horizontal decay、`T → ∞` は導入していない。

`sorry`、`admit`、新規 `axiom`、`native_decide`、provider existence の無根拠な
仮定も追加していない。

## 7. Validation

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiRectangleCauchyCharge.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiRectangleCauchyCharge
./lb DkMath.RH
git diff --check
```

主 square theorem、translated-square theorem、scalar theorem の `#print axioms` は
すべて project の通常の `[propext, Classical.choice, Quot.sound]` の範囲で確認した。
新規 source の禁止宣言検索結果は空である。wrapper build に残る既存 unrelated
warning は `DkMath.NumberTheory.ZsigmondyCyclotomicResearch` の
`declaration uses sorry` のみであり、XDP-014 source から分離されている。

## XDP-015 follow-up

後続 XDP-015 で、ここに記録した 3×3 subdivision blocker は解消された。
任意の strictly interior pole に対する
`pascalRectangleBoundaryIntegral_cauchyKernel_eq_two_pi_I_of_mem_open` と、
coordinate-safe principal-part provider の existence theorem が
`PascalCenteredXiRectangleCauchyCharge.lean` に追加されている。XDP-015 の
結果判定は `Strong Green through Gate G` であり、finite principal-part sum の
rectangle transport 以降は別の未閉鎖 API として記録されている。
