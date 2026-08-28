# XDP-017 — Finite right-edge prime-cutoff integral transport result

作成日: 2026-08-13

## Phase close

判定は **Strong Green through Gate G** である。Gate A–G を actual theorem として
実装し、有限 Pascal/von Mangoldt cutoff の weighted right-edge integral を
ordinary-zeta right-edge integralへ `X → ∞` で transport できる API を公開した。
Gate H は指示書どおり XDP-018 へ明示的に残した。

## Gate A — named observables

次を追加した。

```lean
pascalPrimePowerRightEdgeCutoffIntegrand
pascalPrimePowerRightEdgeCutoffIntegral
pascalXiOrdinaryZetaRightEdgeIntegrand
pascalXiOrdinaryZetaRightEdgeIntegral
```

右辺では `h` を
`h (pascalOrdinaryToCentered (pascalSymmetricRectangleRightEdge σ t))` と評価し、
PHZ と ordinary-zeta negative log derivative は ordinary coordinate で評価する。
`Complex.I` は `ds = i dt` の因子として integrand 内に保持した。

## Gate B — weighted pointwise convergence

```lean
tendsto_pascalPrimePowerRightEdgeCutoffIntegrand
```

を追加した。既存の
`tendsto_pascalPrimePowerPHZFiniteUpTo_pascalXiOrdinaryZetaNegLogDeriv_rightEdge`
に constant multiplication を適用し、各固定 `t` の weighted convergence を
actual theorem として閉じた。

## Gate C — vertical absolute majorant

次の API を追加した。

```lean
pascalVonMangoldtVerticalMajorant
norm_pascalVonMangoldt_LSeries_term_rightEdge_eq
summable_pascalVonMangoldtVerticalMajorant
norm_pascalPrimePowerPHZFiniteUpTo_rightEdge_le_verticalMajorant
```

採用した pinned Mathlib API は次のとおり。

```text
LSeries.norm_term_le_of_re_le_re
ArithmeticFunction.LSeriesSummable_vonMangoldt
Summable.norm
norm_sum_le
Summable.sum_le_tsum
```

`LSeries.norm_term_le_of_re_le_re` を実部一致の両方向に適用し、
`‖term (σ + i t) n‖ = ‖term σ n‖` を得た。`n = 0` は L-series の totalized
term に任せ、zero base の `Complex.cpow` を解析していない。従って finite PHZ
の norm bound は `X` と `t` に依存しない。

## Gate D — finite-interval domination

`Differentiable ℂ h` から centered right-edge weight の連続性を構成し、
```text
t ↦ ‖h(z(t))‖ * pascalVonMangoldtVerticalMajorant σ
```
を interval-integrable な dominating real function とした。有限 PHZ integrand
の連続性は finite L-series sum、`continuous_const_cpow`、および
`pascalPrimePowerPHZFiniteUpTo_eq_LSeries_partialSum` から供給した。

## Gate E — finite interval dominated-convergence transport

principal theorem:

```lean
tendsto_pascalPrimePowerRightEdgeCutoffIntegral
```

を追加した。使用した pinned DCT API は

```lean
intervalIntegral.tendsto_integral_filter_of_dominated_convergence
```

である。pointwise Tendsto を積分の外へ rewrite する shortcut は使用せず、
measurability、domination、interval-integrability、a.e. pointwise convergenceを
全て供給した。

## Gate F — finite arithmetic expansion

```lean
pascalPrimePowerRightEdgeCutoffIntegral_eq_vonMangoldt_sum
```

を追加した。`pascalPrimePowerPHZFiniteUpTo_eq_vonMangoldt_sum`、
`vonMangoldt_LSeries_term_eq`、および
`intervalIntegral.integral_finsetSum` により、有限 weighted oscillatory kernel
sumへ展開した。`Complex.cpow` 表現はそのまま保持し、branch・三角関数展開は
導入していない。

## Gate G — residue-window adapter

```lean
tendsto_pascalPrimePowerRightEdgeCutoffIntegral_of_residueTransportWindow
```

を追加した。`W.rectangle.σ`、`W.rectangle.T`、`W.rectangle.hσ` を使い、
XDP-016 の residue windowから ordinary-zeta right-edge componentへ直接適用
できる形にした。

## Gate H — Blocked / deferred

complete decomposed right-edge integralを ordinary-zeta、archimedean、elementary
の三つへ分割するには、後二者の finite-interval integrability contract が必要
である。これは XDP-018 の対象としてコードコメントにも記録し、XDP-017 の
principal closeには含めていない。この未実装は pointwise または finite
ordinary-zeta transport の数学的障害ではなく、明示された phase boundary である。

## Not introduced

```text
T → ∞, horizontal decay, top-horizontal cancellation
prime-side infinite integral exchange
defect vanishing, defect sign, RH, zero classification
new axiom, sorry, admit, native_decide
```

## Axiom / shortcut audit

新規 module 内に `sorry`、`admit`、`axiom`、`native_decide` はない。既存 project
の unrelated warning は別 ledgerとして扱った。主要 theoremの `#print axioms`
では Mathlib標準の論理基盤のみが対象となり、新規の数学的公理は導入していない。

## Validation

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiPrimeRightEdgeTransport.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiPrimeRightEdgeTransport
lake build DkMath.RH
./lb DkMath.RH
git diff --check
```

上記を pinned toolchainで確認する。公開 `DkMath.RH` に新 moduleをimportし、
XDP-017 の right-edge bridgeを通常のRH import surfaceへ接続した。
