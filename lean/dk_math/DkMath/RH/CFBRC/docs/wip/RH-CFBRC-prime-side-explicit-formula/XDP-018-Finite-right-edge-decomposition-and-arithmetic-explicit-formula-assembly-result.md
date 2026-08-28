# XDP-018 — Finite right-edge decomposition / arithmetic explicit-formula assembly result

作成日: 2026-08-13

## Phase classification

判定は **Ideal Green through Gate I** である。

XDP-017 の finite Pascal/von Mangoldt right-edge transportを、XDP-016 の
finite spectral skeletonへ actual に接続した。全 theorem は固定 finite residue
window、固定 finite height `W.rectangle.T` に限定される。

## Gate 0 — pinned API / coordinate audit

使用した主要 API:

```text
IntervalIntegrable.add / sub / congr / mono_fun'
Continuous.intervalIntegrable
intervalIntegral.integral_add
intervalIntegral.integral_sub (available API; not needed in final split proof)
intervalIntegral.tendsto_integral_filter_of_dominated_convergence
LSeries.norm_term_le_of_re_le_re
ArithmeticFunction.LSeriesSummable_vonMangoldt
```

right-edge ordinary pointは常に
`pascalSymmetricRectangleRightEdge σ t`、centered weightは
`h (pascalOrdinaryToCentered s)`、補正項は ordinary point `s` で評価した。
`Complex.I` は XDP-017 と同じく vertical differential factorとして integrand内に
保持した。

## Gate A — named observables

追加した named API:

```lean
pascalXiArchimedeanRightEdgeIntegrand
pascalXiArchimedeanRightEdgeIntegral
pascalXiElementaryRightEdgeIntegrand
pascalXiElementaryRightEdgeIntegral
pascalXiNonPrimeRightEdgeIntegrand
pascalXiNonPrimeRightEdgeIntegral
pascalXiDecomposedRightEdgeIntegrand
pascalXiDecomposedRightEdgeIntegral
```

pointwise algebra:

```lean
pascalXiDecomposedRightEdgeIntegrand_eq_zeta_add_nonPrime
pascalXiNonPrimeRightEdgeIntegrand_eq_archimedean_add_elementary
```

を定義展開と ring で閉じた。

## Gate B — complete decomposed integrability

```lean
pascalCenteredXiRectangleBoundaryIntegrable_weightedNegLogDeriv
intervalIntegrable_pascalXiDecomposedRightEdgeIntegrand
```

を追加した。XDP-016 の raw regularizer と finite principal-part sum の
`PascalSymmetricRectangleBoundaryIntegrable` を加え、既存の pointwise raw-plus-
principal decompositionで fixed-Xi combined observable の boundary integrabilityを
構成した。その right-edge fieldを
`pascalCenteredXiNegLogDeriv_rightEdge_eq_decomposed` で decomposed observableへ
transportした。Gamma derivativeの直接 continuity theoremは仮定していない。

## Gate C — ordinary-zeta limit integrability

XDP-017 に次を追加した。

```lean
intervalIntegrable_pascalXiOrdinaryZetaRightEdgeIntegrand
```

これは cutoff integrandの finite-interval continuity、pointwise Tendsto、縦線上の
von Mangoldt absolute majorantから limitの a.e. strong measurabilityを得て、
`IntervalIntegrable.mono_fun'` で limit integrandの interval integrabilityを証明する。
従って totalized interval integralを理由に integrabilityを省略していない。

## Gate D — non-prime subtraction

```lean
intervalIntegrable_pascalXiNonPrimeRightEdgeIntegrand
pascalXiDecomposedRightEdgeIntegral_eq_zeta_add_nonPrime
```

を追加した。complete decomposed integrandから ordinary-zeta integrandを引き、
pointwise algebraで combined non-prime integrandと同一視した。その後
`intervalIntegral.integral_add` で有限区間 integral splitを閉じた。

## Gate E — elementary direct integrability

```lean
intervalIntegrable_pascalXiElementaryRightEdgeIntegrand
```

を追加した。`rightEdge_factor_nonzero_of_one_lt` から `s ≠ 0`、`s ≠ 1` を得て、
`-1 / s + 1 / (1-s)` の連続性を直接構成し、centered weightとの積および
`Complex.I` を `Continuous.intervalIntegrable` に渡した。

## Gate F — archimedean subtraction / three-term split

```lean
intervalIntegrable_pascalXiArchimedeanRightEdgeIntegrand
pascalXiNonPrimeRightEdgeIntegral_eq_archimedean_add_elementary
```

を追加した。archimedean項は non-prime から elementaryを引いて得た。Gammaℝ の
derivative continuityへ迂回せず、既存の combined fixed-Xi regularity surfaceを
再利用している。これにより三項 splitが成立する。

## Gate G — exact finite four-term identity

```lean
pascalCenteredXiFiniteExplicitFormula_eq_zeta_archimedean_elementary_top
```

を追加した。XDP-016 skeleton、zeta/non-prime split、non-prime/archimedean/
elementary splitを合成し、

```text
-2πi × finite Xi weighted zero moment
= 2 I_zeta + 2 I_arch + 2 I_elem + 2 I_top
```

を exact equalityとして得た。`I_top` は消去せず、`W.rectangle.T` も有限のまま
保持した。

## Gate H — arithmetic approximant Tendsto

```lean
pascalCenteredXiFiniteArithmeticApproximant
tendsto_pascalCenteredXiFiniteArithmeticExplicitFormula
```

を追加した。XDP-017 の residue-window adapterを zeta termに適用し、archimedean、
elementary、top termsの constant Tendstoと加法で、finite arithmetic approximantが
finite Xi zero-moment endpointへ収束することを証明した。これは fixed finite
windowの `X → ∞` theoremであり、`T → ∞` との交換ではない。

## Gate I — finite von Mangoldt expansion

```lean
pascalCenteredXiFiniteArithmeticApproximant_eq_vonMangoldt_sum
```

を追加した。XDP-017 の
`pascalPrimePowerRightEdgeCutoffIntegral_eq_vonMangoldt_sum` を approximantへ
代入し、`Complex.cpow` のまま finite weighted kernel sum surfaceを公開した。
偏角・三角関数展開は導入していない。

## Coordinate / no-circularity audit

新規 theorem に以下を含めていない。

```text
RiemannHypothesis
defect = 0 / defect ≤ 0
critical-line concentration
horizontal term disappearance
T → ∞
Mellin τ → 0 / ε → 0+
prime cutoff と T-limit の交換
Weil/Li positivity
new provider-only Gamma integrability
```

新規 source に `sorry`、`admit`、`axiom`、`native_decide` はない。Gate H/I は
finite height・fixed windowの範囲を越えていない。

## `#print axioms` audit

主要 theorem:

```text
pascalCenteredXiRectangleBoundaryIntegrable_weightedNegLogDeriv
intervalIntegrable_pascalXiDecomposedRightEdgeIntegrand
intervalIntegrable_pascalXiNonPrimeRightEdgeIntegrand
intervalIntegrable_pascalXiElementaryRightEdgeIntegrand
intervalIntegrable_pascalXiArchimedeanRightEdgeIntegrand
pascalCenteredXiFiniteExplicitFormula_eq_zeta_archimedean_elementary_top
tendsto_pascalCenteredXiFiniteArithmeticExplicitFormula
pascalCenteredXiFiniteArithmeticApproximant_eq_vonMangoldt_sum
```

について確認し、新規数学公理はなく、Mathlib標準の `propext`、
`Classical.choice`、`Quot.sound` のみだった。

## Validation

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiFiniteArithmeticExplicitFormula.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiFiniteArithmeticExplicitFormula
lake build DkMath.RH
./lb DkMath.RH
git diff --check
```

を pinned toolchainで実行済みである。`DkMath.RH` に新 moduleをimportし、公開 RH import
surfaceへ接続した。全体 wrapper buildに表示された既存
`DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:147` の `sorry` warningは
XDP-018外の既存 warningとして残る。

## Next exact blocker

XDP-018 の acceptance setは閉じた。次の frontierは、固定 `ε > 0`、固定 `τ`、固定
finite windowの範囲で、既存 Mellin second-difference weightをこの generic
arithmetic approximantへ specializeする XDP-019 である。`τ → 0`、`ε → 0+`、
`T → ∞` はその後も別々に扱う必要がある。
