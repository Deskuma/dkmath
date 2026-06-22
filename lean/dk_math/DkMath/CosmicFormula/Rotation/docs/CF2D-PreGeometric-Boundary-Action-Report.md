# CF2D Pre-Geometric Boundary Action

## Research Consolidation Report

## Status

This report records the current theorem-level result before a Euclidean circle
or angle parameter is introduced. It is source material for a future paper,
not a finished paper.

The formal implementation is in:

```text
DkMath.Analysis.DkReal.SemanticCF2D
```

## Primary Result

The primary result is not a theorem about a 90-degree rotation. It is a theorem
about a boundary-preserving action with exact order four.

For a transported nonnegative unit kernel with semantic core zero:

```text
semantic core = 0
semantic beam = 1
kernel product has exact order 4
plane action has exact order 4
every nonzero point has minimal period 4
the zero point is fixed
```

The pointwise orbit is:

```text
(x,y)
  -> (-y,x)
  -> (-x,-y)
  -> (y,-x)
  -> (x,y).
```

This orbit is established entirely by coordinate algebra.

## Boundary Before Geometry

At the current formal layer, `q2` is a boundary detector:

```text
q2(x,y) = x^2 + y^2
```

Its level sets are conserved by the action. The development has not yet
declared that the coordinates are orthogonal Euclidean axes, that these level
sets are circles, that an angle parameter exists, or that a full turn is
measured by 360 degrees. Those are additional structures and conventions, not
hidden assumptions in the exact-order proof.

## The Five-Part Mechanism

The result comes from five interacting components.

1. **Boundary detection:** `q2 = rho2` selects a conserved level set.
2. **Kernel composition:** `star` defines composition of kernels.
3. **Action representation:** `act_star` transfers multiplication to actions.
4. **Faithfulness:** the action on the unit vector recovers the kernel.
5. **Semantic root selection:** source nonnegativity removes inadmissible roots.

The preservation equation alone does not produce the classification. The
product, action, faithfulness, and semantic boundary are all essential.

## Low-Order Classification

The current formal classification is:

```text
power 1 = identity  iff core = 1
power 2 = identity  iff core = 1
power 3 = identity  iff core = 1
power 4 = identity  iff core = 1 or core = 0
exact order 4       iff core = 0
```

The first nonidentity finite-order case in the transported first quadrant is
the semantic kernel `(0,1)`. Its intermediate real-side powers leave the first
quadrant:

```text
(0,1)^2 = (-1,0)
(0,1)^3 = (0,-1)
(0,1)^4 = (1,0).
```

This explains why multiplication is performed after transport to `Real`
rather than being forced into the nonnegative source.

## Theorem Map

The principal Lean declarations are:

```text
semanticAct_q2
semanticAct_comp
unitKernel_eq_one_of_act_eq_id
semanticKernelPower_act
semanticKernelFiniteOrder_iff
semanticKernelFiniteOrder_four_iff_core_eq_one_or_zero
semanticExactKernelOrderFour_iff_core_eq_zero
semanticExactKernelOrderFour_iff_exactActionOrderFour
semanticExactActionOrderFour_iff_core_eq_zero
semanticAct_of_core_eq_zero
semanticAct_twice_of_core_eq_zero
semanticAct_thrice_of_core_eq_zero
semanticMinimalPeriod_eq_four_of_core_eq_zero_of_ne_zero
```

## Euclidean Interpretation Comes Later

After choosing the standard Euclidean interpretation of `Real x Real`, `q2`
becomes squared radius, its level sets become circles, and the coordinate
action can be read as a quarter-turn.

The bridge should be stated in this direction:

```text
pre-geometric algebraic structure
  -> Euclidean model
  -> familiar circle and angle terminology
```

The Euclidean model recognizes the existing algebraic behavior. It does not
create or justify the exact-order theorem retroactively.

## Claims And Non-Claims

The current implementation establishes:

```text
a q2-preserving real action;
faithful representation of real-side kernel powers;
low-order finite-order classification;
an exact-order-four nonidentity boundary action;
minimal point period four away from the origin.
```

It does not yet establish:

```text
a source-level signed kernel group;
a reconstructed angle parameter;
topological classification of the level sets;
continuity or differentiability of an angle map;
a bundled equivalence with Euclidean rotation;
a complete classification of all finite-order transported kernels.
```

## Publication Readiness

The central observation is suitable for a research paper:

```text
circle-like four-phase behavior is already present in a smaller algebraic
boundary-action structure, before circles and angles are introduced.
```

A finished paper should still add:

1. an abstract definition of the boundary-action structure;
2. a theorem separating algebraic assumptions from semantic root selection;
3. a Euclidean interpretation theorem in a separate section;
4. comparison with complex multiplication and rotation matrices;
5. a precise novelty statement relative to existing formalizations;
6. a reproducible theorem dependency table.

The result is beyond a speculative note, but the correct present artifact is a
research consolidation report and theorem package before a full manuscript.
