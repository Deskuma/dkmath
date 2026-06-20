# DkNNRealQ Ordered Algebra Checkpoint

## Result

The first algebraic and ordered-algebra checkpoint of Route B is complete.

```text
DkNNRealQ = Quotient DkNNReal.equivSetoid
```

is a Lean `CommSemiring` with `PartialOrder` and the semiring-level
`IsOrderedRing` predicate. Its representatives are nonnegative nested rational
interval sequences of vanishing width. Two representatives are identified
when their interval separation tends to zero.

## Constructive Boundary

The following data remain in the computable representation layer:

- rational interval endpoints;
- nestedness and width convergence certificates;
- addition and nonnegative multiplication;
- natural powers;
- representation equivalence;
- quotient operations and natural-number casts.

No point of Mathlib's `Real` or `NNReal` is selected. In particular, the
`DkReal` / `DkNNRealQ` computable core contains no `noncomputable`
declaration.

## Algebraic Meaning

The wrapper `DkNNReal` carries nonnegativity proofs. The quotient `DkNNRealQ`
removes representation dependence. Consequently, laws formerly stated modulo
`DkNNReal.Equiv` become ordinary equality and support the standard Mathlib
commutative-semiring API.

The natural-number cast is the equivalence class of the constant singleton
interval sequence:

```text
n |-> class of the sequence k |-> [n,n].
```

## Established Order Surface

The order is defined by the vanishing positive lower-endpoint defect:

```text
x <= y  iff  max(0, x.lo(n) - y.lo(n)) -> 0.
```

The implementation establishes:

- `PartialOrder DkNNRealQ`;
- zero as the least quotient value;
- monotonicity of addition and nonnegative multiplication;
- monotonicity of natural powers;
- Mathlib's semiring-level `IsOrderedRing DkNNRealQ`.

This checkpoint does not establish:

- totality or a `LinearOrder`;
- canonical order by additive differences;
- strict ordered-semiring structure;
- completeness;
- decidable equality;
- representation of every `NNReal`;
- a semantic equivalence with Mathlib's `NNReal` or `Real`;
- signed multiplication or a ring structure.

## Next Independent Designs

### Totality

The preferred internal route uses the finite geometry of nested closed
intervals. For two representations, exactly one of the following explanatory
states should control the proof:

```text
SeparatedLeft:
  at some stage x.hi < y.lo, hence x <= y;

SeparatedRight:
  at some stage y.hi < x.lo, hence y <= x;

Merge:
  neither separation occurs, so every stage overlaps and x ~ y.
```

Nestedness makes either strict separation persistent. The Merge branch has
stagewise separation zero and therefore gives `Equiv`. This is the current
candidate for proving totality without evaluating into `Real`.

See
[`DkNNRealQ-Totality-Research.md`](DkNNRealQ-Totality-Research.md).

### Semantic Bridge

A separate bridge may select the unique real point represented by a nested
interval sequence. It must prove:

```text
Equiv x y -> eval x = eval y
eval 0 = 0
eval 1 = 1
eval (x + y) = eval x + eval y
eval (x * y) = eval x * eval y
```

Such a bridge may be `noncomputable`; that declaration must remain outside the
computable core. It should validate, rather than define, the internal order.
