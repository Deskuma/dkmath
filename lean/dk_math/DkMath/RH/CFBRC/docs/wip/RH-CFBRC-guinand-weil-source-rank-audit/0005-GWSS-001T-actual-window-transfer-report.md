# GWSS-001T-A actual-window transfer report

Date: 2026-08-20

## Classification

`ACTUAL-WINDOW-EVEN-POLYNOMIAL-ORBIT-SEPARATION-FOUND`

The actual carrier is used directly as
`pascalCenteredXiZeroDiskFinset R`.  No quotient carrier, negative-zero
closure, or unproved Xi symmetry is assumed.

## Implemented certificate

For a finite carrier `S : Finset ℂ` and target `z`, the module defines

```text
U_{S,z}(w) = ∏ a ∈ S, if a² ≠ z² then (w² - a²) else 1
L_{S,z}(w) = U_{S,z}(w) / U_{S,z}(z).
```

The checked Lean results are:

- `gwssSquaredOrbitSelectorUnnormalized_even`;
- `gwssSquaredOrbitSelectorUnnormalized_differentiable`;
- `gwssSquaredOrbitSelector_denominator_ne_zero` (in fact without a carrier
  membership hypothesis);
- `gwssSquaredOrbitSelector_eq_zero_of_sq_ne` on carrier points;
- `gwssSquaredOrbitSelector_eq_one_of_sq_eq` on carrier points;
- `gwssSquaredOrbitSelector_even` and
  `gwssSquaredOrbitSelector_differentiable`.

The actual-window transfer theorem is:

```text
pascalCenteredXiZeroDiskWeightedMoment_actualSquaredOrbitSelector
```

It evaluates the actual weighted moment as the multiplicity sum over the
actual carrier points satisfying `a ^ 2 = z ^ 2`.

## Boundary

This is a finite algebraic source-rank certificate.  It does not assert RH,
critical-line location, horizontal-term decay, limit exchange, prime-side
sign, fixed-Xi defect vanishing, or any positivity statement.
