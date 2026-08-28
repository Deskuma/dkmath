# GWSS-001T-B Mellin-family transfer report

Date: 2026-08-20

## Classification

`MELLIN-FAMILY-RANK-UNRESOLVED`

Part B was attempted only after the actual-window certificate in Part A was
completed.

## Checked source surface

The existing exact nonzero-`τ` theorem is

```text
pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul
```

It exposes the factor

```text
(exp (τ z) - 2 + exp (-τ z)) / τ²
```

times `centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z`.  The
existing theorem
`tendsto_centeredMellinSpectralWeight_centeredMellinBoxApprox_one` gives the
pointwise limit of this spectral factor to `1` along positive `ε`.

The new finite-window theorem is:

```text
eventually_pascalCenteredXiMellinSpectralWeight_ne_zero_on_actual_window
```

For every fixed radius `R`, it proves eventual simultaneous nonvanishing of
the spectral factor for every `z` in the finite actual Xi carrier.  The proof
uses only pointwise convergence to `1` and finite intersection of eventual
statements; it contains no `T → ∞` argument.

## Remaining gap

No exact finite `τ`-jet, `τ`-derivative, finite evaluation matrix, analytic
separation theorem, or Vandermonde reduction was added.  Consequently the
finite-window spectral-factor nonvanishing theorem is not promoted to a
statement that the Mellin `τ`-family spans all squared-orbit selectors.  The
old fixed-observable countermodel therefore cannot be used to classify the
full Mellin family as redundant, and no such claim is made here.
