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
  nested rational interval representations, representation equivalence,
  and the quotient-backed nonnegative commutative semiring DkNNRealQ.
```

Route B is an algebraic checkpoint, not a completeness theorem for all real
numbers. It constructs a computable representation and quotient without
selecting a value in Mathlib's `Real`.

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
  first bridge to Real and Mathlib Continuous / Set.MapsTo

DkMath.Analysis.TaylorBridge
  zero-increment coefficient, difference quotient, limit, and HasDerivAt bridge

DkMath.Analysis.DkReal.Interval
  DkReal.GapInterval, width, nonnegative power image, and exact width formula

DkMath.Analysis.DkReal.Basic
  nested rational intervals with widths tending to zero

DkMath.Analysis.DkReal.Pow
  computable pointwise power approximations for nonnegative DkReal values

DkMath.Analysis.DkReal.PowBound
  finite-sum gapGN bounds and the completed nonnegative power map

DkMath.Analysis.DkReal.Arithmetic
  computable interval addition, nonnegative multiplication, and stagewise
  semiring laws

DkMath.Analysis.DkReal.Equiv
  vanishing interval separation, representation setoid, endpoint convergence,
  and additive, nonnegative multiplicative, and natural-power congruence

DkMath.Analysis.DkReal.DkNNReal
  nonnegative wrapper with proof-free arithmetic operations and semiring laws
  modulo representation equivalence

DkMath.Analysis.DkReal.DkNNRealQ
  quotient-backed nonnegative type with Zero / One / Add / Mul / Pow and
  a canonical NatCast and CommSemiring instance

DkMath.Analysis.DkReal.Order
  asymptotic lower-endpoint order, Equiv compatibility, PartialOrder,
  ordered-semiring compatibility, and totality research boundary

DkMath.Analysis.DkReal.CanonicalOrder
  subtraction-free extraction of a nonnegative Gap representation,
  ExistsAddOfLE, and CanonicallyOrderedAdd

DkMath.Analysis.DkReal.Semantic
  noncomputable lower-endpoint supremum in Mathlib Real, interval membership,
  and monotone endpoint convergence

DkMath.Analysis.DkReal
  public entry point for the computable approximation layer
```

The closure of nonnegative `DkReal` values under natural powers and its
computability significance are recorded in
[`DkReal-Nonnegative-Power-Milestone.md`](DkReal-Nonnegative-Power-Milestone.md).
The completed quotient-semiring checkpoint is summarized in
[`DkNNRealQ-CommSemiring-Checkpoint.md`](DkNNRealQ-CommSemiring-Checkpoint.md).
The internal totality route is analyzed in
[`DkNNRealQ-Totality-Research.md`](DkNNRealQ-Totality-Research.md).
The next strict-order kernel is designed in
[`DkNNRealQ-StrictGap-Design.md`](DkNNRealQ-StrictGap-Design.md).

`RealBridge` remains the home of continuity and interval mapping. The separate
`TaylorBridge` now connects `gapGN` to difference quotients and `HasDerivAt`
without mixing those concerns into the basic real bridge.

## Next Independent Layers

The algebraic Route B checkpoint is closed. The next layers should remain
separate:

```text
Order:
  PartialOrder is implemented via vanishing positive lower-endpoint defect
  addition, multiplication, and natural-power monotonicity are proved
  zero is least
  IsOrderedRing packages semiring-level ordered compatibility
  totality is proved and exported through Std.Total
  canonical additive order is proved by nonnegative Gap extraction
  strict order is designed as finite positivity of the extracted Gap
  direct linear order structure remains open
  use a semantic bridge only as an independent cross-check

BridgeNNReal / BridgeReal:
  semanticValue now selects the lower-endpoint supremum
  uniqueness and representative independence are proved
  DkNNRealQ evaluation and semiring operations are preserved
  canonical order preservation is proved by additive Gap extraction
  the semantic map is bundled as a semiring homomorphism to Real
  CF2D q2 and unit kernels are transported coordinatewise to Real
  transported kernels act on real vectors and preserve q2
  their coordinates satisfy the real Pythagorean identity
  transported actions compose through real-side kernel products
  every real q2 level set is stable under transported actions
  real-side conjugation makes each transported action bijective
  each q2 level set therefore carries a transported automorphism
  finite iterates and forward orbits retain the same q2 value
  periodic points use Mathlib IsPeriodicPt
  finite action order makes every level-set point periodic
  minimal periods divide all known return times and finite action orders
  source-level star and KernelFamily wait for signed DkReal arithmetic
  treat order reflection as a separate heavier task
  compare semantic equality with DkReal.Equiv
```

The order should not be defined by choosing arbitrary quotient
representatives. The semantic bridge should not be imported by the computable
core merely to obtain an order.

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

`DkReal.GapInterval` contains exact rational endpoints:

```lean
namespace DkMath.Analysis.DkReal

structure GapInterval where
  lo : Rat
  hi : Rat
  le_lo_hi : lo <= hi
```

For a nonnegative interval, `powNonneg` maps both endpoints through a natural
power while preserving order. Its width satisfies:

```lean
DkReal.GapInterval.powNonneg_width_eq :
  (I.powNonneg d hlo).width
    = I.width * gapGN d I.lo I.width
```

The first `DkReal` carrier is now also present:

```lean
structure DkReal where
  interval : Nat -> DkReal.GapInterval
  nested : forall n,
    (interval n).lo <= (interval (n + 1)).lo
      and (interval (n + 1)).hi <= (interval n).hi
  width_tends_zero :
    Tendsto (fun n => (interval n).width) atTop (nhds 0)
```

Rational values embed as constant singleton interval sequences through
`DkReal.ofRat`. Evaluation into Mathlib's real numbers remains deferred to a
later semantic bridge.

The nested interval API also includes arbitrary-stage control:

```lean
DkReal.lo_mono
DkReal.hi_antitone
DkReal.interval_subset_of_le
DkReal.width_succ_le_width
```

These lemmas provide the order foundation needed by a future evaluation map and
interval arithmetic.

## Taylor And Derivative Bridge

The center value of the exact gap kernel is:

```lean
gapGN_zero :
  gapGN d base 0 = d * base^(d - 1)

gapGN_succ_zero :
  gapGN (d + 1) base 0 = (d + 1) * base^d
```

The successor form avoids natural-number truncated subtraction in the displayed
exponent.

Over the reals, `gapGN` is identified with the existing cosmic
`powerKernel`. This yields:

```lean
continuous_gapGN
tendsto_gapGN_zero
powerDifferenceQuotient_eq_gapGN_of_ne_zero
tendsto_powerDifferenceQuotient_zero
hasDerivAt_pow_via_gapGN
```

The logical direction remains:

```text
exact algebraic factorization
  -> exact gap kernel
  -> zero-increment coefficient and limit
  -> Mathlib HasDerivAt bridge
```

The derivative is not used to define the kernel.

`hasDerivAt_pow_from_gapGN_limit` now makes the last step explicit. It passes
the punctured limit of `powerDifferenceQuotient` directly to the general
cosmic-kernel derivative criterion. The canonical
`hasDerivAt_pow_via_gapGN` theorem delegates to this direct proof rather than
to an already completed power derivative theorem.

## Nonnegative DkReal Power Approximations

The computable layer keeps all real-number semantic choices outside `DkReal`.
Nonnegativity is expressed by rational lower endpoints:

```lean
DkReal.Nonnegative x := forall n, 0 <= (x.interval n).lo
```

The stagewise power approximation is:

```lean
DkReal.powNonnegApprox d x hx n
  = (x.interval n).powNonneg d (hx n)
```

The implementation proves:

```lean
DkReal.nonnegative_of_initial_lo
DkReal.powNonnegApprox_lo_le_succ_lo
DkReal.powNonnegApprox_succ_hi_le_hi
DkReal.powNonnegApprox_nested
DkReal.powNonnegApprox_width_nonneg
DkReal.powNonnegApprox_interval_subset_of_le
DkReal.powNonnegApprox_width_eq
```

Thus natural powers preserve the nested interval structure for nonnegative
approximations. The width formula is exact:

```text
powered width
  = original width * gapGN d lowerEndpoint originalWidth
```

A bounded `gapGN` sequence now gives the powered width limit:

```lean
DkReal.tendsto_powNonnegApprox_width_zero_of_gapGN_bounded
```

and therefore constructs a completed powered value:

```lean
DkReal.powNonnegOfGapGNBounded
```

The finite-sum layer now proves that the sequence

```text
gapGN d (lower endpoint at n) (width at n)
```

is bounded for a nested nonnegative `DkReal`.

The proof proceeds through:

```lean
DkReal.gapGN_nonneg_of_nonneg
DkReal.gapGN_le_of_nonneg_of_le
DkReal.gapGN_le_initial_hi
DkReal.gapGN_bounded_on_nonnegative_nested
```

The uniform upper bound is the exact rational value

```text
gapGN d initialUpperEndpoint initialUpperEndpoint
```

rather than a prematurely normalized closed form. This keeps the proof directly
aligned with the finite `GN_eq_sum` expansion.

Combining this bound with the conditional constructor yields the completed,
computable map:

```lean
DkReal.powNonneg
```

Thus natural powers of nonnegative nested rational approximations are again
`DkReal` values, with no `noncomputable` declaration in the DkReal layer.

`TaylorBridge` and `RealBridge` may use noncomputable real-number operations.
The `DkReal` files remain computational and use rational interval data only.
