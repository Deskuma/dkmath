# XDP-013 — Rectangle one-pole Cauchy charge realization result

作成日: 2026-08-12

## Phase close

判定は `Partial Green` である。

XDP-012 の coordinate mismatch を修正し、ordinary pole bridge、generic
rectangle boundary、有限 subdivision algebra、strict-inside square geometry、
および pole-free rectangle Cauchy–Goursat を theorem として実装した。

一極 charge の最終 `2 * π * I` normalization は未閉鎖であり、provider や
`sorry` で代用していない。残った blocker は Mathlib に residue API がないこと
一般ではなく、正方形四辺の複素 interval integral を実数の
`integral_inv_sq_add_sq` と `arctan` normalization へ分解する局所的な proof
term である。

## Gate 0 — coordinate repair

XDP-012 の
`PascalCenteredXiRectanglePrincipalPartChargeProvider` を次の coordinate-safe
形へ変更した。

```lean
pascalSymmetricRectangleBoundaryIntegral
  (fun s => pascalCenteredXiWeightedPrincipalPart h a
    (pascalOrdinaryToCentered s)) ...
```

旧来の centered principal part を ordinary rectangle に直接渡す contract は
公開 surface に残していない。

## Gate A — ordinary pole bridge

次を Green にした。

```lean
pascalCenteredXiOrdinaryPole
pascalOrdinaryToCentered_sub_eq_sub_ordinaryPole
pascalCenteredXiWeightedPrincipalPart_comp_toCentered_eq_cauchyKernel
```

centered pole `a` と ordinary pole `pascalCenteredToOrdinary a` の差分が exact
に一致する。

## Gates B/C — generic rectangle and subdivision

追加した `pascalRectangleBoundaryIntegral` は Mathlib の rectangle boundary
expression と exact に一致する。symmetric specialization も XDP-009 の
boundary integral へ接続した。

次の有限 subdivision theorem を追加した。

```lean
pascalRectangleBoundaryIntegral_vertical_split
pascalRectangleBoundaryIntegral_horizontal_split
```

いずれも pinned interval-integral additivity が要求する有限辺の
`IntervalIntegrable` を明示的に受け取る。一般 chain complex、polygon library、
winding abstraction、homology framework は導入していない。

## Gate D — strict-inside square

次を実装した。

```lean
pascalRectangle_square_subset_open
exists_pascalRectangle_square_radius
```

open rectangle 内点から四つの side distance の正の minimum の半分を選び、pole
中心の閉正方形を構成できることを示した。

## Gate E1 — pole-free rectangle

```lean
pascalRectangleBoundaryIntegral_cauchyKernel_eq_zero_of_not_mem_closed
```

を pinned `Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`
へ接続した。closed rectangle 上の kernel の連続性と open rectangle 上の
微分可能性は pole の closed-set 外部性から直接供給している。

## Gate E2/E3 — exact blocker

3×3 subdivision を実際の one-pole theorem へ適用するには、次の未閉鎖 lemma が
必要である。

```text
pascalRectangleBoundaryIntegral (fun z => z⁻¹)
  (-δ) δ (-δ) δ = 2 * Real.pi * Complex.I
```

実数側の候補 normalization

```lean
integral_inv_sq_add_sq
```

と `Real.arctan_one` / `Real.arctan_neg` の存在は pinned source で確認した。
ただし、四辺の複素 inverse を odd real part と constant imaginary partへ
分解し、有限 interval integral の線形性と組み合わせる proof term がまだ
閉じていない。このため E2/E3 は `Blocked` と記録する。

これは数学的に charge が不成立という意味ではなく、現在の checkpoint で
未証明の analytic micro-lemma を残しているという意味である。未証明 provider、
axiom、`sorry`、`admit`、`native_decide` は追加していない。

## Gates F–J

Gate E3 が未閉鎖なので、以下は意図的に未実装である。

```text
coordinate-safe provider existence: BLOCKED
finite principal-part sum charge: BLOCKED
fixed-Xi rectangle residue formula: BLOCKED
circle = rectangle: BLOCKED
XDP-011 finite explicit-formula skeleton: BLOCKED
```

XDP-009 の individual-term conditional providers と XDP-012 の regularizer
Green theorem は変更せず保持した。

## No-circularity audit

RH、critical-line concentration、defect vanishing、horizontal energy vanishing、
Weil/Li positivity、prime cutoff limit、`T → ∞` は仮定・結論に含めていない。
finite window の存在も主張していない。

## XDP-014 normalization addendum

XDP-014 により、XDP-013 で `Blocked` としていた局所 square normalization は
次の actual theorem として閉じた。

```lean
pascalRectangleBoundaryIntegral_inv_centeredSquare
pascalRectangleBoundaryIntegral_cauchyKernel_centeredSquare
```

証明は `integral_inv_sq_add_sq`、`Real.arctan_one`、`Real.arctan_neg` と、四辺の
complex inverse の rational normal form を使用する。したがって、旧記録の
「E3 が未閉鎖」という判定は XDP-014 適用前の状態であり、現在の next blocker
は一般 interior-pole rectangle の 3×3 finite subdivision である。

## Validation

次を実行し、成功した。

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiRectangleCauchyCharge.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiRectangleCauchyCharge
./lb DkMath.RH
git diff --check
```

主 theorem の axioms は project の通常の
`[propext, Classical.choice, Quot.sound]` の範囲である。wrapper build には
既存 unrelated warning として `DkMath.NumberTheory.ZsigmondyCyclotomicResearch`
の `declaration uses sorry` が残るが、XDP-013 source 自身には該当宣言がない。
