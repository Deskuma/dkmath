# Task 046: Return to the Trigonometric Real-Analysis Route

## Policy

`LinearOrder` and decidable comparison are deferred. The current public order
surface remains `PartialOrder + Std.Total + IsStrictOrderedRing`.

PowerSwap comparison research is complete enough to resume later, but it is
not on the critical path for the trigonometric real-analysis layer.

## Current Main Line

CF2D Phase 1 already supplies the algebraic source of the trigonometric
coordinate identities. The next main-line requirement is a semantic bridge
from the Route B interval representation to Mathlib real analysis:

```text
DkReal representation
  -> unique Mathlib Real value
  -> representative independence
  -> DkNNRealQ semantic map
  -> arithmetic and order preservation
  -> analytic CF2D consumers
```

## Checkpoints

1. Define the semantic value of a `DkReal` representation.
2. Prove that it belongs to every approximation interval.
3. Prove uniqueness of a real point belonging to every interval.
4. Prove invariance under `DkReal.Equiv`.
5. Lift the map to `DkNNRealQ`.
6. Prove zero, one, addition, multiplication, power, and order bridge laws.
7. Reassess which CF2D Phase 2 theorem should consume this bridge first.

## Current Implementation Step

`DkMath.Analysis.DkReal.Semantic` implements the lower-endpoint supremum,
boundedness, interval membership, width convergence, uniqueness, monotone
endpoint convergence, and invariance under `DkReal.Equiv`.

Quotient descent and the first algebraic bridge are now complete:

```text
DkNNRealQ.semanticValue
semanticValue_zero
semanticValue_one
semanticValue_add
semanticValue_mul
semanticValue_pow
semanticValue_mono
```

No global decidable comparison or `LinearOrder` instance is needed.

The next semantic obligations are order reflection and the first analytic
consumer. Order reflection should remain independent of decidable comparison:

```text
semanticValue x ≤ semanticValue y -> x ≤ y
```

The first CF2D consumer is now implemented in
`DkMath.Analysis.DkReal.SemanticCF2D`:

```text
semanticVec
semanticValue_q2
semanticValue_q2_eq
semanticUnitKernel
```

The next consumer should use the transported real `UnitKernel` in an analytic
CF2D theorem. Order reflection remains a separate, heavier task.
