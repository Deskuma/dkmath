# XDP-020 — Tau-zero quadratic arithmetic endpoint / epsilon iterated closure result

作成日: 2026-08-13

## Verdict

判定は **Ideal Green through Gate H** である。XDP-019 の generic Mellin
arithmetic surfaceを `τ := 0` に exact specializeし、各 fixed `ε > 0` で
`X → ∞` を閉じ、その endpointだけを `ε → 0+` で既存 XDP-007 finite
zero-sum theoremへ接続した。

順序は明示的に `lim ε→0+ (lim X→∞ A(ε, X))` である。`X` と `ε` の交換、
joint/product-filter limit、uniform-in-`ε` cutoff convergenceは主張していない。

## Actual definitions and theorems

```lean
pascalCenteredXiMellinQuadraticZeroMoment
pascalCenteredXiMellinSecondDifferenceZeroMoment_tau_zero_eq
pascalCenteredXiMellinQuadraticFiniteExplicitFormula
pascalCenteredXiMellinQuadraticArithmeticApproximant
tendsto_pascalCenteredXiMellinQuadraticArithmeticApproximant
pascalCenteredXiMellinQuadraticArithmeticApproximant_eq_vonMangoldt_sum
tendsto_pascalCenteredXiMellinQuadraticZeroMoment_epsilon
pascalCenteredXiMellinQuadraticArithmeticEndpoint
tendsto_pascalCenteredXiMellinQuadraticArithmeticEndpoint_epsilon
tendsto_pascalCenteredXiMellinQuadraticArithmeticEndpoint_secondContour
pascalCenteredXiMellinQuadraticIteratedLimitCertificate
```

## Gate A/B — exact tau-zero specialization

`pascalCenteredXiMellinQuadraticZeroMoment ε W` は XDP-019 named zero momentの
`τ = 0` aliasである。patched definitionを unfoldし、pointwiseに

```text
H(ε, 0, z) = z² × centeredMellinSpectralWeight
  (centeredMellinBoxApprox ε) z
```

を証明した。fixed-`ε` の四項 finite explicit formulaも公開した。`τ = 0` は
zero functionではなく、`centeredMellinSpectralWeight = 1` ともしていない。

## Gate C/D — fixed-epsilon arithmetic surface

quadratic arithmetic approximantは XDP-019 approximantの `τ = 0` aliasである。
fixed `ε > 0` では `X → ∞` の endpoint convergenceを得た。また finite von
Mangoldt expansionを公開した。`Complex.cpow` は維持し、偏角・`Complex.arg`・
三角関数展開は導入していない。

## Gate E — zero-side epsilon closure

`tendsto_pascalCenteredXiMellinQuadraticZeroMoment_epsilon` は XDP-007 の finite
`Finset` sum theoremを再利用した。zero disk上の finite sumに対する pointwise
convergenceだけで閉じており、right-edge、Gamma/elementary correction、
top-horizontal integralへの `ε → 0+` 交換や dominationは主張していない。

## Gate F/G — arithmetic endpoint and fixed second contour

`pascalCenteredXiMellinQuadraticArithmeticEndpoint` とその `ε → 0+` theoremを
追加した。inner endpointは `-(2πi)` times the quadratic-Mellin zero momentであり、
outer limitは `-(2πi)` times the centered Xi second momentである。

既存の boundary-safe theorem
`pascalCenteredXiSecondOuterContourMass_eq_zeroDiskSecondMoment W.circle_safe`
で targetを rewriteし、fixed second contour massへの Tendstoを得た。新しい contour
calculationは追加していない。

## Gate H — ordered certificate

`pascalCenteredXiMellinQuadraticIteratedLimitCertificate` は、任意の fixed
positive `ε` に対する inner `X → ∞` Tendstoと、outer `ε → 0+` の fixed
second-contour targetを conjunctionとして記録する。reverse order、joint limit、
uniformity、limit exchangeは含まない。

## Deliberate mathematical boundaries

今回閉じていないものは、`τ → 0` integral transport、`X ↔ ε` limit exchange、
joint/product-filter limit、uniform-in-`ε` cutoff convergence、right-edge / Gamma /
elementary / top integrals内の `ε → 0`、`T → ∞`、horizontal contributionの消去、
defect sign/vanishing、critical-line concentration、RHである。これらは fixed finite
zero-side endpoint specializationだけでは数学的に導出できないため、scope外とした。

## Validation

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinQuadraticArithmeticLimit.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinQuadraticArithmeticLimit
lake build DkMath.RH
./lb DkMath.RH
git diff --check
```

上記を pinned toolchainで実行する。主要 theoremの `#print axioms` は標準の
`propext`、`Classical.choice`、`Quot.sound` のみである。新規 sourceには `sorry`、
`admit`、新規 `axiom`、`native_decide`、`Complex.arg` はない。wrapper buildに出る
`ZsigmondyCyclotomicResearch.lean:147` の warningは既存 unrelated warningである。

## Next exact blocker

次段階は ordered second-contour endpointを fixed second-moment defect representation
へ接続すること。ただし defect sign/vanishingやRHの証明は別の数学的 obligationとして
残る。
