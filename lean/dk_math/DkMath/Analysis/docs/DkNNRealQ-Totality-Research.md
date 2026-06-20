# DkNNRealQ Totality Research

## Status

This is a pre-implementation report. No `LinearOrder` is claimed.

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

The remaining question is whether every pair satisfies

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
unspecified real limit. Nested interval geometry suggests the following
trichotomy.

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

## Proposed Lean Checkpoints

The implementation should proceed in small lemmas.

```text
GapInterval:
  separation_eq_zero_iff_overlap
  strict separation orientations are exclusive

DkReal:
  leftSeparated persists under later stages
  rightSeparated persists under later stages
  Le of one witnessed left separation
  Equiv of overlap at every stage

DkNNRealQ:
  representative le_total
  quotient le_total
  LinearOrder decision only after verification
```

Suggested proposition names are provisional:

```lean
GapInterval.Overlaps
DkReal.LeftSeparatedAt
DkReal.RightSeparatedAt
DkReal.le_of_leftSeparatedAt
DkReal.equiv_of_forall_overlaps
DkNNRealQ.le_total
```

Avoid adding an abstract `HasBigGapTotality` axiom while the concrete interval
proof remains available.

## Relation To The Hint

The hint correctly identifies:

- the two-universe comparison;
- the common shrinking Gap;
- positive and negative directed Core defects;
- the Merge state.

The refinement from workspace exploration is that totality may not require a
new sign-selection principle. Nestedness turns a finite witnessed separation
into a permanent orientation, while absence of either separation forces
stagewise overlap.

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
