# DkMath.Analysis Initial Layer

## Purpose

`DkMath.Analysis` does not reconstruct or replace Mathlib's real numbers.
It introduces a DkMath interpretation of exact gaps, residuals, correction
kernels, and interval filling, then connects that interpretation to Mathlib.

The first implementation checkpoint has two routes.

```text
Route A:
  exact algebraic identities over commutative rings and semirings,
  followed by an explicit bridge to Mathlib real analysis.

Route B:
  exact rational intervals as a computational substrate for a future DkReal.
```

## Module Boundary

```text
DkMath.Analysis.Basic
  common namespace and dependency boundary

DkMath.Analysis.GapGN
  analysis-oriented wrapper around the existing cosmic-formula GN

DkMath.Analysis.CosmicResidual
  absolute residual, two-point drift, common bias, and beam perturbation

DkMath.Analysis.ErrorKernel
  exact observed/base/error correction

DkMath.Analysis.GapFill
  affine interval scan, powered fill, endpoint identity, and real order theorem

DkMath.Analysis.RealBridge
  specialization to Real and Mathlib Continuous / Set.MapsTo

DkMath.Analysis.DkReal.Interval
  rational GapInterval, width, nonnegative power image, and exact width formula
```

## Canonical Kernel Bridge

The existing cosmic-formula kernel has argument order:

```lean
DkMath.CosmicFormulaBinom.GN d delta base
```

The analysis-facing wrapper uses:

```lean
gapGN d base delta
```

and is definitionally the same value:

```lean
gapGN d base delta = DkMath.CosmicFormulaBinom.GN d delta base
```

The fundamental exact identity is:

```lean
pow_add_sub_pow_eq_delta_mul_gapGN :
  (base + delta)^d - base^d = delta * gapGN d base delta
```

No limit and no truncated Taylor expansion is involved.

## Residual Versus Drift

The quadratic cosmic gap is:

```lean
cosmicGap x u = (x + u)^2 - x * (x + 2*u)
```

The implementation proves:

```lean
cosmicGap_eq_sq :
  cosmicGap x u = u^2

cosmicResidual_eq_zero :
  cosmicResidual x u = 0

cosmicDrift_eq_zero :
  cosmicDrift x y u = 0
```

A common additive bias has nonzero absolute residual but zero two-point drift.
The API therefore keeps these two observations separate.

## Exact Error Correction

For an observation `base + err`:

```lean
observedGapError_eq_err_mul_gapGN :
  observedGapError d base err = err * gapGN d base err

exactCorrection :
  (base + err)^d - err * gapGN d base err = base^d
```

This retains the complete finite power difference.

## Gap Filling

The interval scan is:

```lean
gapLine u₁ u₂ t = u₁ + t * (u₂ - u₁)
gapFill d u₁ u₂ t = (gapLine u₁ u₂ t)^d
```

Its endpoint difference is:

```lean
gapFill_endpoint_sub_eq :
  gapFill d u₁ u₂ 1 - gapFill d u₁ u₂ 0
    = (u₂ - u₁) * gapGN d u₁ (u₂ - u₁)
```

For real nonnegative ordered endpoints, the implementation proves that the
whole powered scan stays in the powered endpoint interval. The real bridge also
proves continuity in `t`.

## Rational Interval Prototype

`GapInterval` contains exact rational endpoints:

```lean
structure GapInterval where
  lo : Rat
  hi : Rat
  le_lo_hi : lo <= hi
```

For a nonnegative interval, `powNonneg` maps both endpoints through a natural
power while preserving order. Its width satisfies:

```lean
GapInterval.powNonneg_width_eq :
  (I.powNonneg d hlo).width
    = I.width * gapGN d I.lo I.width
```

This is the initial computational basis for `DkReal`. Nested interval
sequences, convergence, and evaluation into Mathlib's real numbers are deferred
to later checkpoints.
