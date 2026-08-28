# XDP-021 — Ordered arithmetic fixed-Xi defect representation result

作成日: 2026-08-13

## Verdict

判定は **Ideal Green** である。XDP-020 の quadratic arithmetic surfaceを
fixed-Xi contour normalizationへ移し、固定 `ε > 0` の `X → ∞` と、その endpointの
`ε → 0+` を順序どおりに defect functionalへ接続した。

意味する極限は厳密に

```text
lim ε→0+ (lim X→∞ D(ε, X, W))
  = pascalCenteredXiFixedSecondMomentDefectFunctional W.R
```

である。

## Actual definitions and endpoints

```lean
pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant
pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint
pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint_eq
tendsto_pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant
tendsto_pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint_epsilon
pascalCenteredXiMellinQuadraticArithmeticDefectApproximant
pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint
tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectApproximant
tendsto_pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_epsilon
pascalCenteredXiMellinQuadraticArithmeticDefectIteratedLimitCertificate
pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_eq_vonMangoldt_surface
pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_eq_cf2dRadial_sub_normalized
```

## Gate A — normalization sign audit

The normalized arithmetic observables use exactly `(2 * π * I)⁻¹`. The endpoint
identity is `(2πi)⁻¹ × (-(2πi) × Mε) = -Mε`. The theorem
`pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint_eq` formalizes this
sign and does not use a zero-moment re-expansion.

## Gate B/C — normalized ordered endpoint

At fixed positive `ε`, continuous scalar multiplication transports XDP-020's
arithmetic cutoff Tendsto to the normalized holomorphic approximant. The
`ε → 0+` endpoint is transported to
`pascalCenteredXiFixedHolomorphicSecondContourFunctional W.R` by the existing
safe-radius second-contour theorem.

No uniformity in `ε` and no integral-internal `ε` limit are used.

## Gate D/E/F — arithmetic defect representation

The radial observable is kept fixed:

```lean
pascalCenteredXiFixedRadialSecondMomentFunctional W.R
```

The finite defect approximant subtracts the real part of the normalized
arithmetic holomorphic approximant. Its fixed-`ε` cutoff convergence and
`ε → 0+` endpoint convergence are proved using continuity of `Complex.re` and
fixed real subtraction. The endpoint is exactly
`pascalCenteredXiFixedSecondMomentDefectFunctional W.R`.

## Gate G — ordered certificate

`pascalCenteredXiMellinQuadraticArithmeticDefectIteratedLimitCertificate` records
the inner `X → ∞` convergence for every fixed positive `ε` and the outer
`ε → 0+` convergence to the fixed defect. It does not assert reverse order,
joint/product-filter convergence, uniform convergence, or limit exchange.

## Gate H — finite von Mangoldt surface

`pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_eq_vonMangoldt_surface`
exposes the finite defect as fixed radial observable minus the real part of the
normalized XDP-020 finite von Mangoldt surface. `Complex.cpow` remains intact;
no `Complex.arg`, argument, or trigonometric expansion is introduced.

## Gate I — CF2D compatibility

`pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_eq_cf2dRadial_sub_normalized`
rewrites only the fixed radial side to the existing CF2D radial mass on
`W.circle_safe`. This is a target compatibility theorem, not an arithmetic sign
theorem.

## Sign and scope ledger

The finite approximants have no proved sign. The existing endpoint theorem may
provide the known nonnegativity of the fixed defect, but it is not used to infer
nonnegativity, nonpositivity, or eventual behavior of the prime-side finite
approximants.

Still open by design: finite arithmetic defect sign, fixed defect `≤ 0`, fixed
defect `= 0`, `X ↔ ε` exchange, joint limit, uniform-in-`ε` convergence, ε-limits
inside right-edge/Gamma/elementary/top integrals, `T → ∞`, horizontal-term
disappearance, `R → ∞`, critical-line concentration, and RH. The independent
sign mechanism remains the next mathematical blocker.

## Validation

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiArithmeticDefectRepresentation.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiArithmeticDefectRepresentation
lake build DkMath.RH
./lb DkMath.RH
git diff --check
```

主要 theorem の `#print axioms` は標準の `propext`、`Classical.choice`、
`Quot.sound` のみである。新規 sourceには `sorry`、`admit`、新規 `axiom`、
`native_decide`、`Complex.arg` はない。wrapper buildに出る既存
`ZsigmondyCyclotomicResearch.lean:147` の warningは unrelated warningとして分離する。
