# GNPC-005 report

## Outcome

Outcome A — the degree-three dual GN kernel has a verified quadratic-form, trace-one norm, centered-square, and target-characterization API.

The validated chain is:

```text
GN 3 u x = u^2 + 3*u*x + 3*x^2
          = (x+u)^2 + (x+u)*x + x^2
          = trace-one norm at s = -1
4 * GN 3 u x = u^2 + 3*(2*x+u)^2
GN 3 u x = p ↔ 4*p = u^2 + 3*(2*x+u)^2
```

The quadratic form is additive/polynomial coordinate data, not a multiplicative factorization of a prime.

## Reconnaissance

The existing cubic theorem was found in `DkMath/NumberTheory/ZsigmondyCyclotomic.lean`, namespace `DkMath.NumberTheory.GcdNext`:

```lean
lemma GN_three_explicit (x u : ℕ) :
    GN 3 x u = x ^ 2 + 3 * x * u + 3 * u ^ 2
```

It was not imported because that owner carries the heavy Zsigmondy/cyclotomic application dependency. The new owner proves the dual-oriented expansion locally from:

```lean
DkMath.CosmicFormulaBinom.GN_eq_sum
```

Existing neutral trace-one declarations found:

```lean
DkMath.NumberTheory.TraceOneQuadratic.norm
DkMath.NumberTheory.TraceOneQuadratic.traceOneNorm_neg_one
DkMath.NumberTheory.TraceOneQuadratic.four_mul_traceOneNorm_eq_discriminant
```

Existing FLT-local related bridges found:

```lean
DkMath.FLT.GN_three_sub_eq_traceOneNorm_negOne
DkMath.FLT.eisensteinNorm_shift_eq_traceOneNorm_negOne
```

They were not imported or modified. No existing direct dual-coordinate, centered-square, or centered-residual declaration was found.

## Owner and changed files

New thin owner:

```text
DkMath/NumberTheory/GNThreeQuadratic.lean
```

Imports:

```lean
import DkMath.CosmicFormula.CosmicFormulaBinom
import DkMath.NumberTheory.TraceOneQuadratic
```

Changed files for this checkpoint:

```text
DkMath/NumberTheory/GNThreeQuadratic.lean
docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-005.md
```

No FLT bridge, aggregator, or existing GN declaration was modified.

## Final theorem surface

```lean
theorem DkMath.NumberTheory.GN_three_dual_explicit (u x : ℕ) :
    DkMath.CosmicFormulaBinom.GN 3 u x =
      u ^ 2 + 3 * u * x + 3 * x ^ 2

theorem DkMath.NumberTheory.GN_three_eq_discriminant_neg_three_form (u x : ℕ) :
    DkMath.CosmicFormulaBinom.GN 3 u x =
      (x + u) ^ 2 + (x + u) * x + x ^ 2

theorem DkMath.NumberTheory.GN_three_eq_traceOneNorm_negOne (u x : ℕ) :
    ((DkMath.CosmicFormulaBinom.GN 3 u x : ℕ) : ℤ) =
      DkMath.NumberTheory.TraceOneQuadratic.norm
        (⟨((x + u : ℕ) : ℤ), (x : ℤ)⟩ :
          DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt (-1))

theorem DkMath.NumberTheory.four_mul_GN_three_eq_centered_square (u x : ℕ) :
    4 * DkMath.CosmicFormulaBinom.GN 3 u x =
      u ^ 2 + 3 * (2 * x + u) ^ 2

theorem DkMath.NumberTheory.GN_three_eq_target_iff_centered_square
    {p u x : ℕ} :
    DkMath.CosmicFormulaBinom.GN 3 u x = p ↔
      4 * p = u ^ 2 + 3 * (2 * x + u) ^ 2

theorem DkMath.NumberTheory.GN_three_one_eq_target_iff_centered_square
    {p x : ℕ} :
    DkMath.CosmicFormulaBinom.GN 3 1 x = p ↔
      4 * p = 1 + 3 * (2 * x + 1) ^ 2
```

## Centered residual

The residual API was added:

```lean
def DkMath.NumberTheory.GNThreeCenteredResidual (p u x : ℤ) : ℤ :=
  3 * (2 * x + u) ^ 2 + u ^ 2 - 4 * p

theorem DkMath.NumberTheory.GN_three_eq_target_iff_centeredResidual_eq_zero
    {p u x : ℕ} :
    DkMath.CosmicFormulaBinom.GN 3 u x = p ↔
      GNThreeCenteredResidual (p : ℤ) (u : ℤ) (x : ℤ) = 0
```

For positive prime-target degree-three representations, GNPC-004 supplies `3 ∣ p - 1`; GNPC-005 adds the coordinate shell. No classification follows.

## Regression anchors

The mandatory anchor is verified:

```lean
example : DkMath.CosmicFormulaBinom.GN 3 2 1 = 13
```

The optional fixed unit-slice failure is also verified:

```lean
example : ¬ ∃ x : ℕ, DkMath.CosmicFormulaBinom.GN 3 1 x = 13
```

Thus `(u,x) = (2,1)` represents `13`, while the fixed `u = 1` slice does not.

## Validation

```text
lake build DkMath.NumberTheory.GNThreeQuadratic
```

Result: success (`Build completed successfully (8668 jobs).`) with no Lean warnings. The new module contains no `sorry` or `axiom`; `git diff --check` was run successfully.

## Deferred items

- classification of primes represented by `a^2 + a*b + b^2`;
- quadratic reciprocity, representation equivalences, and class-number/UFD theory;
- cyclotomic or primitive-prime/Zsigmondy extensions;
- general `d > 3` centered normal forms;
- real/complex square-root geometry;
- ABC, FLT, Legendre, and RH applications;
- repository-wide relocation of the existing FLT bridges.

The checkpoint stops at the exact degree-three quadratic/norm/centered-square characterization.
