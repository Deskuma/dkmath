# Wallis-Cosmic Final Chain

The formal bridge now has three pointwise-equal finite real sequences:

```text
((centralRatioQ m * mirrorOddRatioPartialQ m : Q) : R)
  = ((wallisPartialQ m : Q) : R)
  = ((cosmicPartialQ m : Q) : R)
```

The finite module proves the algebraic equalities over `Q`.
The limit module coerces them to `R` and reuses Mathlib's Wallis theorem:

```text
((wallisPartialQ m : Q) : R) -> Real.pi / 2
```

Therefore the proof-note expression also converges:

```text
central binomial ratio * mirror product
  = finite Wallis product
  = finite cosmic gap product
  -> Real.pi / 2
```

## Conditional product caveat

The infinite-product theorem in Lean is an ordered / conditional product:

```text
HasProd factor (Real.pi / 2) (SummationFilter.conditional Nat)
```

For `Nat`, this is exactly the classical exhaustion by `Finset.range m`.
This matches the usual Wallis partial products.

The default `HasProd` in Mathlib is unordered / unconditional.  We do not
claim that stronger form here.  An unconditional Wallis-Cosmic product would
require a separate absolute or log-product summability argument.
