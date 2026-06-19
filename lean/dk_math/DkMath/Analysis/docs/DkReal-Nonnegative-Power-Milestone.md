# DkReal Nonnegative Natural-Power Milestone

## Observation

The first substantial operation on `DkReal` is now complete: every
nonnegative `DkReal` approximation is closed under natural powers.

This checkpoint is notable because the construction concerns real-number
approximations but the operation itself does not require `noncomputable`.
It acts only on exact rational endpoints and carries proofs that the resulting
interval sequence remains nested and has width tending to zero.

This is not yet a claim that the full real field has been reconstructed.
It is a precise closure result for the representation currently implemented.

## Representation

A `DkReal` is represented by nested closed rational intervals

```text
I_n = [a_n, b_n]
```

whose widths

```text
w_n = b_n - a_n
```

tend to zero. A nonnegative `DkReal` additionally satisfies `0 <= a_n` at
every stage.

For a natural exponent `d`, the stagewise power operation is

```text
[a_n, b_n] |-> [a_n^d, b_n^d].
```

Because the power map is monotone on the nonnegative rationals, nestedness is
preserved by exact order reasoning.

## Width Principle

The decisive identity is the finite algebraic factorization

```text
b_n^d - a_n^d
  = w_n * gapGN d a_n w_n,
```

where `b_n = a_n + w_n`. The kernel `gapGN` is a finite binomial sum, not a
derivative or an infinite expansion.

Nestedness and nonnegativity give the fixed bounds

```text
0 <= a_n <= b_0,
0 <= w_n <= b_0.
```

Every term of `gapGN` is nonnegative and coordinatewise monotone on this
quadrant. Therefore

```text
0 <= gapGN d a_n w_n <= gapGN d b_0 b_0.
```

Thus the powered width is a sequence tending to zero multiplied by a uniformly
bounded sequence. It also tends to zero. This proves that the powered interval
sequence is again a `DkReal`.

## Why `noncomputable` Is Unnecessary Here

The construction never selects a real number from the nested intervals. It
does not:

- invoke completeness of `Real`;
- choose a limit point;
- quotient Cauchy data;
- evaluate a `DkReal` as a Mathlib `Real`;
- use a derivative or mean-value theorem to estimate the power map.

Instead, each output interval is computed from rational input endpoints by a
finite natural power. The proof fields certify the global convergence
invariant, but they do not change the executable endpoint data.

The distinction is architectural:

```text
computable representation layer:
  rational intervals + finite algebra + convergence certificates

semantic bridge layer:
  interpretation in Mathlib Real + continuity + derivatives
```

The semantic bridge may legitimately use `noncomputable`, because extracting
or identifying an abstract real value can require classical completion
machinery. The present `DkReal` power operation does not cross that boundary.

## Lean Realization

The implementation is divided into four mathematical steps:

1. `gapGN_nonneg_of_nonneg` proves positivity of the exact correction kernel.
2. `gapGN_le_of_nonneg_of_le` proves coordinatewise monotonicity.
3. `gapGN_bounded_on_nonnegative_nested` obtains a uniform bound from the
   initial interval.
4. `powNonneg` packages the powered intervals as a new `DkReal`.

The public simplification rules record the expected exact cases:

```lean
powNonneg_ofRat_interval
powNonneg_zero_interval
powNonneg_one_interval
```

No approximation error is hidden in these statements. Embedded rationals
remain singleton intervals, the zeroth power is the singleton at one, and the
first power returns the original interval at every stage.

## Research Significance

This checkpoint isolates a useful formalization principle:

> An operation on real-like objects can remain computable when it is defined
> on finite observations and its analytic obligation is carried separately as
> a proof of preservation of the representation invariant.

For natural powers on the nonnegative domain, the exact cosmic-formula kernel
provides precisely the finite correction factor needed to transport vanishing
width. Real analysis appears later as an interpretation of this construction,
not as a prerequisite for defining it.

The next tests of this principle, addition and nonnegative multiplication, are
now implemented in `DkMath.Analysis.DkReal.Arithmetic`. Addition needs no sign
restriction; multiplication currently remains on the nonnegative quadrant so
that endpoint multiplication is order preserving. These operations establish
the computational core needed for a future nonnegative ordered-semiring API,
before introducing a semantic map to Mathlib's `Real`.

## Nonnegative Computable Semiring Core

The arithmetic layer now proves the expected semiring laws at every finite
observation stage:

```lean
add_assoc_interval
add_comm_interval
add_zero_interval
zero_add_interval
mulNonneg_assoc_interval
mulNonneg_comm_interval
mulNonneg_one_interval
one_mulNonneg_interval
left_distrib_interval
right_distrib_interval
```

These statements identify the rational intervals produced at a fixed stage.
They do not use the raw structure equality of `DkReal`. This distinction is
essential: two different nested interval sequences may eventually represent
the same real number without being definitionally equal as Lean structures.

Consequently, no `Add`, `Mul`, or semiring typeclass instance is introduced
yet. The implementation has a computable nonnegative semiring core at the
observation level, but a formal algebraic structure should wait until the
representation equivalence has been chosen and its congruence properties have
been proved.

Candidate equivalence principles include persistent interval intersection,
vanishing separation between two approximations, or equality after a future
evaluation map into Mathlib's `Real`. These formulations are not
interchangeable by definition, so selecting one is a mathematical design
decision rather than a routine API addition.
