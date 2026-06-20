# DkNNRealQ Totality Research

## Status

The internal totality experiment is implemented and accepted by Lean. No
direct `LinearOrder` is claimed yet.

The current computable core already provides:

```text
DkNNRealQ:
  CommSemiring
  PartialOrder
  IsOrderedRing
  zero_le
  add_le_add
  mul_le_mul
  pow_le_pow
```

Every pair now satisfies

```lean
x <= y ∨ y <= x.
```

## Cosmic Interpretation

For two representations

```text
X(n) = [x.lo(n), x.hi(n)]
Y(n) = [y.lo(n), y.hi(n)],
```

the pair is observed inside a common comparison universe.

- **Core:** the rational endpoint observations locating each shrinking value;
- **Gap:** interval width and pairwise interval separation;
- **comparison Big:** the hull containing both stage intervals.

This comparison Big is a geometric explanatory object. It is not definitionally
the algebraic `DkMath.CosmicFormula.CoreBeamGap.Big`.

The current order defect

```text
max(0, x.lo(n) - y.lo(n))
```

is the positive part of the directed Core displacement. `x <= y` means that
this protrusion disappears as precision increases.

## Main Finding

The workspace contains a stronger route than selecting the sign of an
unspecified real limit. Nested interval geometry gives the following
comparison.

### Separated Left

Suppose for some stage `n`:

```text
x.hi(n) < y.lo(n).
```

For every later `m >= n`, nestedness gives

```text
x.lo(m) <= x.hi(m) <= x.hi(n)
                         < y.lo(n) <= y.lo(m).
```

Hence `orderDefect x y m = 0` eventually, so `Le x y`.

### Separated Right

The symmetric condition

```text
y.hi(n) < x.lo(n)
```

gives `Le y x`.

### Merge

If neither strict separation occurs at any stage, then for every `n`:

```text
x.lo(n) <= y.hi(n)
y.lo(n) <= x.hi(n).
```

The intervals overlap, so their rational `separation` is zero at every stage.
Therefore `Equiv x y`, and `equiv_le` supplies both order directions.

This route uses only:

- rational endpoint order;
- closed interval validity;
- nestedness;
- the existing separation-based equivalence.

It does not require evaluation into Mathlib's `Real` or `NNReal`.

## Implemented Lean Checkpoints

```text
GapInterval:
  Overlaps
  separation_eq_zero_iff_overlaps

DkReal:
  LeftSeparatedAt / RightSeparatedAt
  leftSeparatedAt_persistent
  rightSeparatedAt_persistent
  le_of_leftSeparatedAt / le_of_rightSeparatedAt
  equiv_of_forall_overlaps
  le_of_not_exists_leftSeparatedAt
  le_total_repr

DkNNRealQ:
  le_total
  Std.Total (· <= ·)
```

No abstract `HasBigGapTotality` axiom was needed.

The final proof is stronger and shorter than the explanatory three-state
picture:

```text
if exists n, x.hi(n) < y.lo(n):
  x <= y
else:
  y.lo(n) <= x.hi(n) for every n
  defect(y,x,n) <= width(x,n)
  therefore y <= x
```

The Merge state remains useful for interpretation and is represented by
`equiv_of_forall_overlaps`.

## Relation To The Hint

The hint correctly identifies:

- the two-universe comparison;
- the common shrinking Gap;
- positive and negative directed Core defects;
- the Merge state.

The refinement from workspace exploration was correct: totality requires no
new sign-selection principle. Nestedness turns a finite witnessed separation
into a permanent orientation, while absence of left separation bounds the
reverse defect by a vanishing width.

## Semantic Cross-Check

A future noncomputable bridge may map representatives to `NNReal` and prove:

```text
x <= y ↔ eval x <= eval y.
```

That theorem would independently validate totality and order correctness.
It should not be imported into the computable core merely to obtain
`LinearOrder`.

## Independent Open Questions

Totality does not settle canonical order. The statement

```text
x <= y ↔ ∃ z, y = x + z
```

requires constructing a nonnegative difference representation and should be
treated separately.

Strict order also needs its own analysis. In particular, strict monotonicity
and cancellation must not be inferred solely from `IsOrderedRing`.
