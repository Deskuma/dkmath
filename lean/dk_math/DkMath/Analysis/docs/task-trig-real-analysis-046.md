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
semanticUnitKernel_sq_add_sq
semanticAct
semanticAct_q2
semanticKernelProduct
semanticAct_comp
semanticActLevel
semanticActLevel_comp
semanticInverseKernel
semanticInverseAct
semanticAct_bijective
semanticInverseActLevel
semanticActLevel_bijective
semanticActEquiv
semanticActLevelEquiv
semanticAct_iterate_q2
semanticOrbit
semanticOrbit_q2
semanticLevelOrbit
SemanticPeriodic
SemanticLevelPeriodic
SemanticFiniteOrder
semanticFiniteOrder_iff
semanticFiniteOrder_of_dvd
semanticMinimalPeriod
semanticPeriodic_iff_minimalPeriod_dvd
semanticMinimalPeriod_dvd_of_finiteOrder
```

The transported kernel now acts on real CF2D vectors and preserves `q2`.
Subtraction appears only after transport to `Real`; it is not added to the
nonnegative source semiring.

Two transported actions compose through the product of their real unit
kernels, and every real `q2` level set is stable under the transported action.
No source-level kernel product is asserted.

Real-side conjugation supplies an inverse kernel. Consequently each
transported action is a bijection of the real CF2D plane and restricts to a
bijection of every `q2` level set. The inverse generally leaves the first
quadrant and is therefore not reflected back into the nonnegative source.

The actions are bundled as equivalences. Their finite iterates remain
bijective, and every forward orbit has constant `q2`. A level-set orbit is the
same plane orbit viewed with its invariant carried in the type.

Periodicity uses Mathlib's `Function.IsPeriodicPt`. Level-set periodicity is
equivalent to periodicity of the underlying plane point. Finite action order
means that one iterate is the identity on the whole plane; this makes every
point of every level set periodic.

The period argument of `SemanticPeriodic` is neither required to be positive
nor minimal. `semanticMinimalPeriod` uses Mathlib's convention: it is the
least positive period for a periodic point and zero otherwise. Periodicity is
equivalent to divisibility by this minimal period. Every point's minimal
period divides any finite action order, and finite action order propagates to
all multiples.

The next structural boundary is source-level `Vec.star` and `KernelFamily`.
Both require signed arithmetic. They should wait for a signed DkReal layer
rather than forcing subtraction into `DkNNRealQ`. Until then, further work can
remain on the real side, for example classifying fixed points or finite-order
actions. Order reflection remains a separate, heavier task.
