# XDP-015 — Arbitrary interior-pole rectangle charge / provider closure result

作成日: 2026-08-12

## Phase close

判定は **Strong Green through Gate G** である。

XDP-014 の translated-square charge を、任意の strictly interior pole を持つ
rectangle へ有限 3×3 subdivision で transport した。さらに、centered Xi zero
の ordinary pole が fixed symmetric rectangle の open interior にあることを
same-zero-set contract から示し、XDP-012 の coordinate-safe principal-part
provider を actual theorem として構成した。

## Gate A — arbitrary interior pole

次を実装した。

```lean
pascalRectangleBoundaryIntegral_cauchyKernel_eq_two_pi_I_of_mem_open
    {xL xR yB yT : ℝ} {p : ℂ}
    (hp : p ∈ Set.Ioo xL xR ×ℂ Set.Ioo yB yT) :
    pascalRectangleBoundaryIntegral (fun z : ℂ => (z - p)⁻¹)
      xL xR yB yT = 2 * Real.pi * Complex.I
```

`exists_pascalRectangle_square_radius hp` から得た正の `δ` と四つの strict
margin をそのまま用いた。新しい radius theory は導入していない。

## Gate B — finite 3×3 assembly

次の theorem を追加した。

```lean
pascalRectangleBoundaryIntegral_three_by_three
```

これは二回の vertical split と、三つの vertical strip それぞれへの二回の
horizontal split を反復する有限 assembly である。内部辺の cancellation は
既存 split theorem に委ね、別の contour/polygon abstraction は導入していない。
Cauchy kernel の horizontal / vertical edge interval-integrability は、極の
虚部 / 実部が edge coordinate と異なることから `ContinuousOn.intervalIntegrable`
で供給した。

## Gates C–E — center charge and eight outer charges

3×3 の center block は

```lean
pascalRectangleBoundaryIntegral_cauchyKernel_centeredSquare hδ
```

へ直接接続し `2 * Real.pi * Complex.I` となる。残り 8 block は、実部または
虚部が `δ` の strict margin の外側にあることを named helper で示し、

```lean
pascalRectangleBoundaryIntegral_cauchyKernel_eq_zero_of_not_mem_closed_aux
```

へ接続して `0` とした。これらを finite assembly に代入して Gate A の結論を
得ている。auxiliary theorem は declaration order のため public Gate E1 より
前に置いた Mathlib-backed copy であり、未証明命題の代用ではない。

## Gate F — ordinary pole localization

次を実装した。

```lean
pascalCenteredXiOrdinaryPole_mem_rectangleOpen_of_mem_zeroDiskFinset
```

`mem_centeredXiZeroDiskFinset_iff_mem_ball_of_boundarySafe` と
`W.zero_mem_iff` の same-zero-set / interior contract を使い、
`pascalCenteredToOrdinary` の rectangle membership を
`pascalCenteredXiOrdinaryPole` の symmetric open-rectangle membershipへ
移した。新しい zero localization を仮定していない。

## Gate G — provider realization

次を actual theorem として実装した。

```lean
exists_pascalCenteredXiRectanglePrincipalPartChargeProvider
    (h : ℂ → ℂ) (W : PascalCenteredXiResidueTransportWindow) :
    PascalCenteredXiRectanglePrincipalPartChargeProvider h W
```

`pascalCenteredXiWeightedPrincipalPart_comp_toCentered_eq_cauchyKernel` により
各 edge の integrand を

```text
(-(multiplicity a : ℂ) * h a) * (s - pascalCenteredXiOrdinaryPole a)⁻¹
```

へ変換し、Gate A の charge に定数係数を掛けた。`pascalRectangleBoundaryIntegral_symmetric`
で XDP-012 の symmetric boundary contract と一致させている。

## Gates H–K — explicit boundary and mathematical blocker

以下はこの phase では **未閉鎖** と明記する。

```text
finite principal-part sum rectangle charge: OPEN
fixed-Xi rectangle weighted residue formula: OPEN
circle = rectangle: OPEN
XDP-011 finite explicit-formula skeleton: OPEN
```

理由は、既存 API が finite principal-part sum の circle integrability と
circle integral identityを持つ一方、rectangle の四つの interval integralへ
その有限和を移すための edge-integrability / finite-sum interchange theoremと、
XDP-012 の raw decompositionを ordinary rectangle boundaryへ接続する theoremを
持たないためである。circle theorem を rectangle theoremとして読み替えること、
または未証明 providerを置くことは数学的に正当でない。この未閉鎖は解析 API の
橋渡し不足であり、charge theorem自体の失敗や RH の主張ではない。

`T → ∞`、horizontal decay、prime cutoffとの積分交換、defect vanishing、RH、
一般 residue / winding / homotopy framework は導入していない。

## Validation

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiRectangleCauchyCharge.lean
git diff --check
```

新規 theorem 群は pinned Lean / Mathlib でコンパイルする。新規実装に
`sorry`、`admit`、`axiom`、`native_decide` は追加していない。
