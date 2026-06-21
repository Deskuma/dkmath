# DkNNRealQ Strict Gap Design

## Design Rule

The implementation should begin with the complete outer identity and fill its
known components:

```text
Big = (Core + Beam) + Gap.
```

For additive order at degree one:

```text
Big  = y
Core = x
Beam = 0
Gap  = z
y    = x + z
```

`CanonicalOrder.lean` has already constructed this nonnegative Gap.
Strict order is therefore not a new comparison mechanism. It is the remaining
question about the extracted Gap:

```text
Gap collapses to zero:
  x = y

Gap opens positively at finite precision:
  x < y
```

## Known Body

The following parts are complete:

- asymptotic order `Le`;
- totality;
- finite left/right separation;
- canonical Gap extraction;
- `x <= y` iff `exists z, y = x + z`.

These form the known Body of the next proof.

## Missing Difference Kernel

The strict kernel should connect three equivalent observations:

```text
Order:
  Le x y and not Le y x

Geometry:
  exists n, x.interval(n).hi < y.interval(n).lo

Extracted Gap:
  exists n, 0 < (gapOfLe x y hxy).interval(n).lo
```

The middle form is the finite Core--Gap separation. The last form says that
the canonical Gap universe has become observably positive.

## Implementation Status

```text
[done] DkReal.not_le_of_leftSeparatedAt
[done] representative strictness iff finite left separation
[done] DkNNReal.Lt := Le x y and not Le y x
[done] DkNNReal.lt_iff_exists_leftSeparatedAt
[done] positive lower endpoint of gapOfLe iff finite separation
[done] quotient strict-order characterization
[done] strict addition at a sufficiently precise later stage
[done] finite positivity of a nonnegative wrapper
[done] positivity of a product by stage alignment
[done] positive-factor strict multiplication through the canonical Gap
[done] `IsStrictOrderedRing` interface
[decision] retain `PartialOrder` plus `Std.Total`; do not install `LinearOrder`
```

The representative theorem now precedes every strict ordered-semiring
typeclass. It is the mathematical kernel; a typeclass will only package its
later quotient consequences.

## Interface Decision

Mathlib's `IsStrictOrderedRing` fits this quotient without adding inverses or
linear-order structure. Additive cancellation follows from totality and strict
addition; the multiplication fields are exactly the positive-factor Gap
transformation proved above.

Mathlib's `LinearOrder` requires decidable `<=`, `<`, and equality. Totality as
a proposition does not supply a terminating comparison algorithm for
asymptotic interval representations. The public structure therefore remains:

```text
PartialOrder
Std.Total (· <= ·)
IsOrderedRing
IsStrictOrderedRing
CanonicallyOrderedAdd
```

Clients may select classical decidability locally when algorithmic comparison
is not required.

## Arithmetic Interpretation

Addition preserves the strict Gap after refinement:

```text
(x + a) + z = (y + a).
```

At a fixed stage the interval width of `a` can hide the observed separation.
The proof therefore fixes a positive separation `epsilon` and advances until
`width(a) < epsilon`; strict separation is then visible again.

Multiplication transforms it:

```text
y = x + z
y * a = x * a + z * a.
```

If `a = 0`, the transformed Gap collapses. If `0 < a`, positivity of the Gap
persists: positive lower endpoints of `z` and `a` are aligned at a common
later stage, so the lower endpoint of `z * a` is positive. This is the exact
branch distinction required before a strict ordered-semiring interface can be
considered.

## Boundary

No semantic real evaluation is needed for this design. No subtraction
operation is needed on `DkNNRealQ`. The only subtraction remains finite
rational endpoint observation inside the Gap kernel.
