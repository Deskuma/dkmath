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

## Proposed Lean Sequence

```text
1. DkReal.not_le_of_leftSeparatedAt
2. DkReal.lt_iff_exists_leftSeparatedAt
3. DkNNReal.Lt := Le x y and not Le y x
4. DkNNReal.lt_iff_exists_leftSeparatedAt
5. positive lower endpoint of gapOfLe iff finite separation
6. quotient strict-order characterization
7. strict addition
8. positive-factor strict multiplication
```

The representative theorem should precede any strict ordered-semiring
typeclass. It is the actual mathematical kernel; the typeclass is only its
later packaging.

## Arithmetic Interpretation

Addition preserves the strict Gap:

```text
(x + a) + z = (y + a).
```

Multiplication transforms it:

```text
y = x + z
y * a = x * a + z * a.
```

If `a = 0`, the transformed Gap collapses. If `0 < a`, positivity of the Gap
should persist. This is the exact branch distinction required before
`IsStrictOrderedRing` can be considered.

## Boundary

No semantic real evaluation is needed for this design. No subtraction
operation is needed on `DkNNRealQ`. The only subtraction remains finite
rational endpoint observation inside the Gap kernel.
