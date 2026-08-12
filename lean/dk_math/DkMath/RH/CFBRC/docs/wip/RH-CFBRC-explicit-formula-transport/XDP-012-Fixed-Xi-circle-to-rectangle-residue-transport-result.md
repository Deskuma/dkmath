# XDP-012 — Fixed-Xi circle-to-rectangle residue transport result

作成日: 2026-08-12

## Phase close

判定は `Partial Green / Gate E Blocked` である。

矩形の pinned Cauchy–Goursat による patched regularizer の消滅と、境界上での
raw regularizer への移送は theorem として閉じた。一方、pinned Mathlib には
矩形内の一極の Cauchy 積分・winding・residue charge を直接与える API がなく、
この checkpoint の範囲で一般 residue framework を新設することも指示されて
いない。そのため one-pole rectangle charge は provider の存在を仮定せず、E3
として明示的に次 checkpoint へ残した。

## 1. Pinned rectangle Cauchy–Goursat API audit

採用した pinned API は次である。

```lean
Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
```

その引数は `f`, opposite corners `z w`, countable exceptional set `s`,
closed rectangle 上の `ContinuousOn`、および open rectangle から `s` を除いた
点での `DifferentiableAt` である。Mathlib の rectangle boundary expression
を XDP-009 の oriented four-edge integral に接続する
`pascalSymmetricRectangleBoundaryIntegral_eq_mathlibBoundary` を追加した。

追加 audit では、pinned revision に one-pole rectangle `sub_inv` / winding /
residue theorem を見つけられなかった。既存の circle principal-part API は
rectangle charge の代用にはならない。

## 2. Stronger residue transport window

`PascalCenteredXiResidueTransportWindow` は既存の
`PascalCenteredXiContourTransportWindow` を拡張し、次を持つ。

```lean
circle_safe : IsPascalCenteredXiBoundarySafeRadius R
rectangle_boundary_safe : IsPascalCenteredXiRectangleBoundarySafe ...
```

後者は right/left/top/bottom の全 edge で
`pascalCenteredRiemannXiKernel (...) ≠ 0` を要求する。closed rectangle は
`uIcc (1 - σ) σ ×ℂ uIcc (-T) T`、open rectangle は対応する `Ioo` product
として定義し、Mathlib の closed/open rectangle との同一性を theorem 化した。

この contract から、closed rectangle 内の Xi zero は
`pascalCenteredXiZeroDiskFinset W.R` に入り、boundary zero は four-edge
safety により排除される。window の存在自体は無条件には主張していない。

## 3. Rectangle regularizer continuity / differentiability

既存の disk regularizer、principal-part sum、raw regularizer、removable patch
を再利用した。追加した generic helper は
`differentiableAt_pascalCenteredXiDiskWeightedRawRegularizer_of_kernel_ne_zero`
で、Xi kernel の nonvanishing と finite zero set 外だけを仮定する。zero point
では既存 patch を使い、totalized `logDeriv` の zero point valueを removable
limit と同一視していない。

ordinary-to-centered translation と合成した regularizer について、closed
rectangle 上の `ContinuousAt` と open rectangle から finite zero set を除いた
点での `DifferentiableAt` を実装した。

## 4. Patched/raw regularizer boundary integral

次の theorem が Green である。

```lean
pascalCenteredXiRectangleIntegral_diskWeightedRegularizer_eq_zero
pascalCenteredXiDiskWeightedRegularizer_eq_raw_on_rectangleBoundary
pascalCenteredXiRectangleIntegral_diskWeightedRawRegularizer_eq_zero
```

最初の theorem は Mathlib の rectangle Cauchy–Goursat API に直接接続し、
exceptional set として ordinary-coordinate image of
`pascalCenteredXiZeroDiskFinset W.R` を用いる。次の theorem は rectangle
boundary safety から patched/raw の pointwise congruence を四辺それぞれに
供給し、最後の theorem は interval-integral congruence で raw boundary integral
の消滅へ移送する。

## 5. One-pole rectangle charge — Gate E

判定は **E3 / Blocked** である。

```lean
structure PascalCenteredXiRectanglePrincipalPartChargeProvider ... where
  principalPart_boundary_eq : ...
```

という named provider の型だけを公開した。provider の存在を `axiom`、`sorry`
または `native_decide` で埋めていない。E1 は pinned API 不在、E2 はこの
checkpoint で新しい一般 residue/homotopy framework を導入する範囲を越えるため、
数学的・スコープ上の境界として残した。

## 6. Finite principal-part sum

Gate E が Blocked のため、rectangle principal-part sum の charge theorem は
意図的に追加していない。provider を受け取るだけで実際の charge を導く形に
偽装しなかった。

## 7. Rectangle weighted Xi residue formula

Gate D までは Green だが、Gate E が未閉鎖なので
`pascalCenteredXiWeightedRectangleMass_eq` 相当の actual residue formula は
この checkpoint では未実装である。

## 8. Circle = rectangle bridge

共通 finite weighted zero moment を介する circle = rectangle theorem は Gate G
に依存するため未実装である。既存の circle theorem
`pascalCenteredXiWeightedOuterContourMass_eq` は変更せず保持した。

## 9. XDP-011 finite explicit-formula skeleton

XDP-011 の finite horizontal-pairing theorem は import 可能なまま保持した。
しかし rectangle residue endpoint が未閉鎖なので、XDP-011 と合成した
`-2πi × finite Xi zero weighted moment` の rectangle explicit-formula skeleton
はこの checkpoint の Green surface に昇格させていない。`T → ∞`、horizontal
term の消去、prime cutoff との極限交換は行っていない。

## 10. XDP-009 conditional provider migration

XDP-009 の decomposed ordinary-zeta / Gamma / elementary term の conditional
providers は削除・変更していない。今回の module は combined fixed-Xi
regularizer の rectangle Cauchy–Goursat だけを追加した。Gate G/H が未成立
なので、combined observable の actual residue theorem への migration は次の
one-pole charge checkpoint に延期する。

## 11. No-circularity audit

この実装は RH、非自明零点の critical-line 集中、defect vanishing、Weil/Li
positivity、prime-side sign theorem を仮定・結論に含めない。same-zero-set は
既存の finite localization contract としてのみ使用した。finite window の
存在も主張していない。

## 12. Build / test / axioms audit

実行結果は次の通りである。

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiExplicitFormulaRectangleResidueTransport.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaRectangleResidueTransport
./lb DkMath.RH
git diff --check
```

上記はすべて成功した。`./lb DkMath.RH` の build log には既存の
`DkMath.NumberTheory.ZsigmondyCyclotomicResearch` の `declaration uses sorry`
警告だけが残り、XDP-012 source の警告はない。

主 theorem の `#print axioms` は次の共通基礎 axioms のみである。

```text
[propext, Classical.choice, Quot.sound]
```

新規 XDP-012 source には `sorry`, `admit`, `axiom`, `native_decide` の宣言を
追加していない。

## 13. XDP-013 migration addendum

XDP-013 の Gate 0 に合わせ、principal-part provider の境界関数を
`fun s => pascalCenteredXiWeightedPrincipalPart h a
(pascalOrdinaryToCentered s)` と明示して、ordinary boundary coordinate と
centered pole coordinate の混同を除去した。この修正は既存 provider の型を
座標安全な形へ狭めるものであり、circle 側の theorem は変更していない。

XDP-013 では Gate A の ordinary-pole bridge、矩形境界の Mathlib adapter、有限
vertical/horizontal subdivision、square の内部包含半径、ならびに pole-free
rectangle の Cauchy--Goursat 消滅までを実装した。これらは
`PascalCenteredXiRectangleCauchyCharge.lean` に収録している。

ただし Gate E2/E3 の最終 charge

```lean
pascalRectangleBoundaryIntegral (fun z => z⁻¹)
  (-δ) δ (-δ) δ = 2 * Real.pi * Complex.I
```

は未閉鎖である。未解決部分は一般の residue/homotopy 理論ではなく、四辺の
複素区間積分を `integral_inv_sq_add_sq` と arctangent の正規化へ正確に還元する
局所的な proof term である。したがって provider の存在、有限 principal-part
sum、rectangle residue formula、circle=rectangle transport、XDP-011 との合成は
この checkpoint では意図的に追加していない。数学的に閉じられない境界を
`sorry` や axiom で隠していない点を明記して、XDP-013 は Partial Green とする。
