# XDP-019 — Fixed Mellin second-difference arithmetic specialization result

作成日: 2026-08-13

## Phase classification

判定は **Ideal Green through Gate H, with the limit ledger recorded at Gate I**
である。XDP-018 の generic finite arithmetic explicit formula を、固定
`ε > 0`、固定 `τ : ℝ`、固定 finite residue window `W` に対して canonical
Mellin box weightへ specializeした。

この phase では `τ → 0`、`ε → 0+`、`T → ∞`、それらの交換、horizontal 項の消去、
defect/RH 結論を主張していない。

## Gate A — box bridge and admissibility

追加した canonical definition:

```lean
pascalCenteredXiMellinSecondDifferenceWeight
```

追加した theorem:

```lean
pascalCenteredXiMellinSecondDifferenceWeight_differentiable
pascalCenteredXiMellinSecondDifferenceWeight_even
```

`hε : 0 < ε` から、既存の
`centeredMellinBoxApprox_endpoints_ordered`、
`centeredMellinBoxApprox_support_subset`、
`centeredMellinBoxApprox_continuousOn` をそのまま供給し、既存の
`differentiable_centeredMellinSecondDifferenceWeight` と
`centeredMellinSecondDifferenceWeight_centeredMellinBoxApprox_even` を再利用した。
新しい provider assumption は導入していない。

## Gate B — named zero-side observable

```lean
pascalCenteredXiMellinSecondDifferenceZeroMoment
```

は、generic `pascalCenteredXiZeroDiskWeightedMoment` に実際の Mellin weight を
代入した alias である。`z²` momentへ置換していない。

## Gate C — fixed Mellin spectral identity

```lean
pascalCenteredXiMellinFiniteExplicitFormula
```

は XDP-018 の
`pascalCenteredXiFiniteExplicitFormula_eq_zeta_archimedean_elementary_top` を
specializeする。zeta、archimedean、elementary、top の全項に同じ
`pascalCenteredXiMellinSecondDifferenceWeight ε τ` を使い、top 項と有限高さを保持する。

## Gate D/E — arithmetic approximant and fixed-parameter Tendsto

```lean
pascalCenteredXiMellinFiniteArithmeticApproximant
tendsto_pascalCenteredXiMellinFiniteArithmeticExplicitFormula
```

を追加した。後者は任意の fixed `τ`（`τ = 0` を含む）について、`X → ∞` のみを
扱い、同じ specialized finite Xi zero moment endpointへ収束する。

## Gate F — finite von Mangoldt surface

```lean
pascalCenteredXiMellinFiniteArithmeticApproximant_eq_vonMangoldt_sum
```

により、有限 `X` の arithmetic surfaceを公開した。`Complex.cpow` は維持し、
`Complex.arg`、偏角、三角関数展開は導入していない。

## Gate G — nonzero-τ kernel exposure

```lean
pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul
```

は `hτ : τ ≠ 0` の場合だけ、

```text
[(exp(τ z) - 2 + exp(-τ z)) / τ²]
  × centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z
```

を exact に公開する。arithmetic Tendsto theoremへ `τ ≠ 0` を混入させていない。

## Gate H — patched τ = 0 surface

```lean
pascalCenteredXiMellinSecondDifferenceWeight_tau_zero_eq_quadraticWeight
```

は次を固定する:

```text
weight(ε, 0, z)
= z² × centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z
```

これは zero-function theorem ではなく、また `centeredMellinSpectralWeight = 1`
も主張していない。

## Gate I — limit ledger / deliberate boundary

既存の次 API は監査対象として確認したが、XDP-019 の arithmetic formulaへ適用していない。

```lean
tendsto_centeredMellinSecondDifferenceWeight_zero
centeredMellinSpectralWeight_centeredMellinBoxApprox_eq_logAverage
tendsto_centeredMellinSpectralWeight_centeredMellinBoxApprox_one
tendsto_centeredMellinBoxApprox_quadraticWeight
```

従って次は未主張であり、次 phase の境界である:

```text
lim τ→0 と integral/correction の交換
lim ε→0+ の arithmetic formula
top-horizontal 項との ε 極限交換
Mellin limit と X→∞ の交換
```

これらは fixed-parameter specialization だけでは数学的に閉じないため、意図的に
実装していない。

## Scope / shortcut audit

新規 source に contour/residue theorem、RH、defect sign/vanishing、critical-line
concentration、horizontal contribution の消去を追加していない。`sorry`、`admit`、
新規 `axiom`、`native_decide`、`Complex.arg` は使用していない。

## Validation

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinArithmeticSpecialization.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinArithmeticSpecialization
lake build DkMath.RH
./lb DkMath.RH
git diff --check
```

主要 theorem の `#print axioms` を確認し、新規数学公理がないことを確認する。
全体 wrapper に表示される既存 `ZsigmondyCyclotomicResearch.lean:147` の `sorry`
warning は XDP-019 外の既存 warning として ledger に残す。

## Next exact blocker

次は fixed `ε` または `τ` の極限を arithmetic surfaceへ接続する phaseである。
その際も、integral・correction・top 項・`X → ∞` の順序を別々に証明する必要があり、
現時点では極限交換を閉じたことにしない。
