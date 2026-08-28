# XDP-016 — Finite rectangle principal-part sum / fixed-Xi residue assembly result

作成日: 2026-08-13

## Phase close

判定は **Ideal Green through Gate H** である。

XDP-015 までに閉じていた一極 rectangle charge と provider existence を、有限
principal-part sum、raw regularizer、fixed-Xi rectangle contribution、centered
outer circle、および XDP-011 finite explicit-formula skeleton へ接続した。すべて
finite height / fixed window の theorem であり、極限や contour deformation は導入
していない。

## Gate 0 — coordinate contract migration

XDP-009 の `PascalExplicitFormulaContourTransportProvider.boundary_integrable`
を coordinate-safe shapeへ修正した。

```lean
PascalSymmetricRectangleBoundaryIntegrable
  (fun s => F (pascalOrdinaryToCentered s))
  W.rectangle.σ W.rectangle.T
```

この構造の構築子利用箇所は repository 内になく、公開 import と全体 build は
通過している。rectangle contribution の centered→ordinary translationと整合
するため、旧 raw-`F` contract は残していない。

## Gate A — rectangle linearity

次を追加した。

```lean
pascalSymmetricRectangleBoundaryIntegrable_add
pascalSymmetricRectangleBoundaryIntegral_add
pascalSymmetricRectangleBoundaryIntegrable_finset_sum
pascalSymmetricRectangleBoundaryIntegral_finset_sum
```

4辺すべての oriented interval-integrability を仮定し、`intervalIntegral.integral_add`
と有限 induction による finite sum 交換を actual theorem として閉じた。vertical
edge の `Complex.I` と left/top の逆向き区間を維持している。

## Gates B–C — one pole and finite principal-part sum

次を実装した。

```lean
pascalCenteredXiRectangleBoundaryIntegrable_weightedPrincipalPart
pascalCenteredXiRectangleBoundaryIntegrable_diskWeightedPrincipalPartSum
pascalCenteredXiRectangleIntegral_diskWeightedPrincipalPartSum_eq
```

XDP-015 の ordinary pole localization、Cauchy-kernel edge helper、coordinate
bridge、および actual provider charge を使用した。有限和を rectangle boundary
integral の外へ移す操作は Gate A の integrability theorem によって証明され、
circle finite-sum theorem を rectangle theorem として読み替えていない。

## Gates D–F — raw regularizer and fixed-Xi rectangle formula

追加した theorem は次である。

```lean
pascalCenteredXiRectangle_edge_mem_closed
pascalCenteredXiRectangleBoundaryIntegrable_diskWeightedRawRegularizer
pascalCenteredXiWeightedNegLogDeriv_comp_toCentered_eq_raw_add_principalPartSum
pascalCenteredXiWeightedRectangleContribution_eq
```

patched regularizer の closed-rectangle continuity と boundary congruenceから raw
edge integrabilityを供給した。ordinary coordinateへ pull backした pointwise raw
decompositionを定義展開と ring で閉じ、raw integral `= 0` と finite principal-part
chargeを additivityで assemblyした。

## Gate G — circle = rectangle

```lean
pascalCenteredXiWeightedRectangleContribution_eq_outerContourMass
```

を追加した。rectangle と circle はそれぞれ同じ

```text
-(2 * π * I) × finite weighted Xi zero moment
```

へ評価してから等置している。この theorem は common finite endpoint による
equalityであり、homotopy / contour deformation theorem ではない。

## Gate H — finite explicit-formula skeleton

```lean
pascalCenteredXiFiniteExplicitFormulaSkeleton
```

を既存の
`pascalCenteredXiRectangleContribution_eq_two_right_decomposed_add_two_top`
と Gate F の formulaから構成した。horizontal termは有限高さのまま残している。

## Not introduced

次は導入していない。

```text
T → ∞
horizontal decay / horizontal term = 0
prime cutoff ↔ interval-integral exchange
defect vanishing
RH / critical-line concentration
new residue, winding, homotopy, polygon, chain-complex framework
sorry, admit, new axiom, native_decide
```

従って XDP-016 の後続 frontier は、right-edge decomposed integralから ordinary
zeta / finite Pascal–von Mangoldt cutoffへ進む arithmetic transportと、別 ledger
としての finite horizontal correction である。

## Validation

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiFiniteRectangleResidueAssembly.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiFiniteRectangleResidueAssembly
lake build DkMath.RH
git diff --check
```

いずれも pinned toolchainで成功した。公開 `DkMath.RH` は新 moduleをimportし、
既存 unrelated warningとして `DkMath.NumberTheory.ZsigmondyCyclotomicResearch`
の `declaration uses sorry` のみが残る。
