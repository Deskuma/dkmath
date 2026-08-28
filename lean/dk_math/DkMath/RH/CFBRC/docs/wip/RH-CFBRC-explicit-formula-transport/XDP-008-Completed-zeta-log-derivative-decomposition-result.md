# XDP-008 result: completed-zeta logarithmic-derivative decomposition

XDP-008 の principal acceptance set A--F と H を実装した。対象は
repository 固有の pole-killed completed-zeta kernel の局所
negative-log-derivative decomposition であり、full explicit formula、contour
shift、defect sign、defect vanishing、RH は対象外である。

## 1. Pinned normalization audit

確認した pinned API は次のとおり。

* `pascalRiemannXiKernel s` は
  `s * (1 - s) * completedRiemannZeta₀ s - 1`。
* `pascalRiemannXiKernel_eq_mul_completedRiemannZeta` は
  `s ≠ 0` と `s ≠ 1` の下で
  `pascalRiemannXiKernel s = s * (1 - s) * completedRiemannZeta s`。
* Mathlib の正本関係は

  ```text
  completedRiemannZeta s
    = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)
  ```

  であり、全ての `s` に totalized された等式である。ただし pole point の
  totalized 値は meromorphic cancellation の代用には使っていない。
* `riemannZeta_def_of_ne_zero hs0` は

  ```text
  riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s
  ```

  を与える。`hGamma : Complex.Gammaℝ s ≠ 0` と併せて
  `completedRiemannZeta s = riemannZeta s * Complex.Gammaℝ s` を
  `completedRiemannZeta_eq_riemannZeta_mul_Gamma_of_ne_zero` として固定した。
* `Complex.Gammaℝ s` は
  `π ^ (-s / 2) * Complex.Gamma (s / 2)` で、zero condition は
  `Complex.Gammaℝ_eq_zero_iff` の
  `∃ n, s = -(2 * n)` である。
* pinned API は `Complex.differentiable_Gammaℝ_inv` を提供するが、
  `Gammaℝ` 自体の unrestricted differentiability theorem ではない。
  `hGamma ≠ 0` の局所では inverse をもう一度取ることで
  `DifferentiableAt Complex.Gammaℝ` を得た。
* `logDeriv_mul` は各 factor の pointwise nonzero と
  `DifferentiableAt` を要求する。この hypotheses を decomposition theorem に
  明示している。

## 2. Actual declarations

module:

`DkMath/RH/CFBRC/PascalCenteredXiCompletedZetaLogDerivBridge.lean`

主な declaration は次のとおり。

* `pascalRiemannXiFactorizedKernel`
* `pascalRiemannXiKernel_eventuallyEq_factorized`
* `pascalRiemannXiKernel_logDeriv_eq_factorized`
* `pascalXiOrdinaryZetaNegLogDeriv`
* `pascalXiArchimedeanLogDeriv`
* `pascalXiElementaryLogDerivCorrection`
* `pascalRiemannXiNegLogDeriv_eq_zeta_add_archimedean_add_elementary`
* `pascalCenteredXiNegLogDeriv_eq_uncentered`
* `pascalCenteredXiNegLogDeriv_eq_zeta_add_archimedean_add_elementary`
* `IsPascalCenteredXiLogDerivDecompositionSafeRadius`
* `pascalCenteredXiWeightedNegLogDeriv_eq_decomposed_on_sphere`
* `pascalCenteredXiWeightedOuterContourMass_eq_decomposed`
* `tendsto_pascalPrimePowerPHZFiniteUpTo_pascalXiOrdinaryZetaNegLogDeriv`

## 3. Local derivative transport

単一点の kernel equality を `rw` して derivative を変更する shortcut は使って
いない。`s ≠ 0, 1` から `eventually_ne_nhds` を作り、
`pascalRiemannXiKernel_eventuallyEq_factorized` を構成した。その後
`Filter.EventuallyEq.deriv_eq` と `eq_of_nhds` を使って `logDeriv` を輸送した。

completed zeta と ordinary zeta/Gamma の equality も、Gamma inverse の局所
nonvanishing を作った上で eventual equality として factorized kernel に
transport している。

## 4. Exact decomposition

定義した各項は

```text
ordinary zeta:
  pascalXiOrdinaryZetaNegLogDeriv s = - deriv riemannZeta s / riemannZeta s

archimedean:
  pascalXiArchimedeanLogDeriv s = - logDeriv Complex.Gammaℝ s

elementary:
  pascalXiElementaryLogDerivCorrection s = -1 / s + 1 / (1 - s)
```

従って、`s ≠ 0`、`s ≠ 1`、`riemannZeta s ≠ 0`、
`Complex.Gammaℝ s ≠ 0` のもとで

```text
-logDeriv pascalRiemannXiKernel s
  = pascalXiOrdinaryZetaNegLogDeriv s
    + pascalXiArchimedeanLogDeriv s
    + pascalXiElementaryLogDerivCorrection s
```

である。elementary correction の符号は product rule から Lean 上で導出し、
手計算の符号を theorem target に直接埋め込んでいない。

## 5. Centered transport and safety

`pascalCenteredXiNegLogDeriv_eq_uncentered` は
`deriv_comp_const_add` により
`s = criticalLineCenter + z` を実装した。

`IsPascalCenteredXiLogDerivDecompositionSafeRadius R` は既存の
`IsPascalCenteredXiBoundarySafeRadius R` に加えて、sphere 上で

```text
s ≠ 0 ∧ s ≠ 1 ∧ riemannZeta s ≠ 0 ∧ Complex.Gammaℝ s ≠ 0
```

を要求する。Xi-safe radius だけから個別 zeta/Gamma factor の安全性を推論
していない。

## 6. Weighted boundary and contour status

`pascalCenteredXiWeightedNegLogDeriv_eq_decomposed_on_sphere` は、任意の weight
に対する sphere 上の pointwise `EqOn` を Green にした。

`pascalCenteredXiWeightedOuterContourMass_eq_decomposed` は、三つの個別
`CircleIntegrable` 仮定を明示した conditional contour split として Green である。

無条件の Gate G は Blocked と記録する。理由は、Xi-safe contour が
`h * pascalCenteredXiNegLogDeriv` の regularity を与えても、decomposition 後の
ordinary-zeta、Gamma、elementary の各項が同じ sphere 上で
`CircleIntegrable` であることを自動的には与えないためである。特に Xi kernel
では cancellation 済みでも、分解後の各項では `s = 1`、trivial-zero / Gamma
singularity、`s = 0` の bookkeeping が個別に残る。

## 7. Prime-side hook

`tendsto_pascalPrimePowerPHZFiniteUpTo_pascalXiOrdinaryZetaNegLogDeriv` は既存の
`tendsto_pascalPrimePowerPHZFiniteUpTo_neg_deriv_riemannZeta_div` を
`pascalXiOrdinaryZetaNegLogDeriv` へ thin adapter したもの。von Mangoldt
convergence や Pascal canonical fold は再証明していない。

## 8. XDP-009 preflight audit

次 phase の contour transport では、centered circle `|z| = R` が ordinary
coordinate の `|s - 1/2| = R` になる。右半平面 `1 < s.re` へ移す際には、少なくとも
次を個別に処理する必要がある。

1. ordinary zeta の pole `s = 1`。
2. elementary factor の `s = 0` と `s = 1`。
3. `Complex.Gammaℝ` の zero/pole representation と negative-even points。
4. trivial zeta zeros と Gamma factor の cancellation。
5. Xi contour では安全でも decomposition terms individually singular になり得る点。
6. centered circle から right-half-plane boundary への rectangle/contour transport。

この pinned repository で今回確認できた contour API は
`circleIntegral.integral_congr` と `circleIntegral.integral_add` までである。
XDP-008 では rectangle deformation、meromorphic residue theorem、または
circle-to-Dirichlet-domain transport を導入していない。これらが XDP-009 の
exact missing API / hypotheses である。

## 9. Safety and shortcut audit

RH、defect vanishing、critical-line zero classification、Weil positivity、
horizontal energy、full explicit formula は仮定・import・結論に使っていない。
新規コードに `sorry`、`admit`、`axiom`、`native_decide` はない。principal
declarations の `#print axioms` は標準的な `propext`、`Classical.choice`、
`Quot.sound` のみを表示した。

## 10. Validation

実行対象:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiCompletedZetaLogDerivBridge.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiCompletedZetaLogDerivBridge
./lean-build.sh
./lean-test.sh
git diff --check
```

repository wrapper の build/test は既存 unrelated module の `sorry` warning を
表示するが、XDP-008 の新規 declaration による warning ではない。
