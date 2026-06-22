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
SemanticFixed
semanticFixed_iff_minimalPeriod_eq_one
SemanticPositiveFiniteOrder
SemanticIdentityKernel
semanticIdentityKernel_iff_core_eq_one
semanticFixed_iff_eq_zero_of_not_identity
semanticKernelPower
semanticKernelPower_act
unitKernel_eq_one_of_act_eq_id
SemanticKernelFiniteOrder
semanticKernelFiniteOrder_iff
semanticKernelPower_one
semanticKernelPower_two_core
semanticKernelPower_two_beam
semanticKernelPower_three_core
semanticKernelPower_three_beam
semanticKernelPower_four_core
semanticKernelPower_four_beam
semanticKernelFiniteOrder_one_iff_identity
semanticKernelFiniteOrder_one_iff_core_eq_one
semanticKernelFiniteOrder_two_iff_identity
semanticKernelFiniteOrder_two_iff_core_eq_one
semanticKernelFiniteOrder_three_iff_identity
semanticKernelFiniteOrder_three_iff_core_eq_one
semanticKernelFiniteOrder_four_iff_core_eq_one_or_zero
semanticUnitKernel_beam_eq_one_of_core_eq_zero
semanticKernelFiniteOrder_four_of_core_eq_zero
not_semanticKernelFiniteOrder_one_of_core_eq_zero
not_semanticKernelFiniteOrder_two_of_core_eq_zero
not_semanticKernelFiniteOrder_three_of_core_eq_zero
SemanticExactKernelOrderFour
semanticExactKernelOrderFour_iff_core_eq_zero
SemanticExactActionOrderFour
semanticExactKernelOrderFour_iff_exactActionOrderFour
semanticExactActionOrderFour_iff_core_eq_zero
semanticExactActionOrderFour_of_core_eq_zero
semanticAct_of_core_eq_zero
semanticAct_twice_of_core_eq_zero
semanticAct_thrice_of_core_eq_zero
not_semanticPeriodic_one_of_core_eq_zero_of_ne_zero
not_semanticPeriodic_two_of_core_eq_zero_of_ne_zero
not_semanticPeriodic_three_of_core_eq_zero_of_ne_zero
semanticMinimalPeriod_eq_four_of_core_eq_zero_of_ne_zero
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

Fixed points use Mathlib's `Function.IsFixedPt`: they are exactly period-one
points and exactly points of minimal period one. The origin is fixed by every
transported action. `SemanticPositiveFiniteOrder` adds positivity to an
exhibited finite action order; it does not claim minimality of that order.

The first fixed-point classification is complete. For a transported
first-quadrant unit kernel, semantic core coordinate one forces beam zero and
therefore the neutral kernel. An identity kernel fixes every point; every
nonidentity transported kernel fixes exactly the origin. The proof uses only
the Pythagorean kernel identity and the determinant of the fixed-point linear
system.

Finite-order classification now has an algebraic real-side formulation.
`semanticKernelPower r n` is the repeated product of the transported unit
kernel, formed only in `UnitKernel Real`. Its action is exactly the `n`th
iterate of `semanticAct r`. Since a real unit kernel is recovered by applying
its action to the multiplicative unit vector, the action is faithful.
Consequently:

```text
semanticKernelPower r n = UnitKernel.one Real
  iff
(semanticAct r)^[n] = id
```

This closes the bridge between kernel product order and finite action order
without defining multiplication, subtraction, or inverses in the nonnegative
source.

The first low-order classification is also complete. Product order dividing
one is equivalent to semantic identity and to semantic core coordinate one.
For transported first-quadrant kernels the same is true of product order
dividing two. A general real unit kernel would also admit `(-1, 0)` as a
square root of the neutral kernel, but coordinatewise transport from
`DkNNRealQ` makes both semantic coordinates nonnegative and excludes that
case. Thus no nonidentity transported kernel has order two.

Low-power coordinate formulas are now exposed as a reusable algebraic API:

```text
power 2 core = C^2 - S^2
power 2 beam = 2*C*S
power 3 core = C^3 - 3*C*S^2
power 3 beam = 3*C^2*S - S^3
```

These are finite CF2D product expansions, not invocations of double-angle or
triple-angle theorems. The order-two classification now consumes the
quadratic core formula rather than reopening the recursive product
definition. The cubic formulas provide the next input for classifying product
order dividing three under the transported first-quadrant constraints.

Product order dividing three is now classified as well. The cubic beam
equation factors into:

```text
S = 0
or
S^2 = 3*C^2
```

The first branch gives the neutral kernel. In the second branch the
unit-square equation gives `C^2 = 1/4` and `S^2 = 3/4`; nonnegativity gives
`C = 1/2`, and the cubic core equation then contradicts identity. Therefore
orders dividing one, two, or three all force semantic identity. This concerns
order dividing the displayed integer, not an assertion of exact order.

Order dividing four is the first classification with a nonidentity branch.
The fourth-power core polynomial, together with the square of the unit
equation, forces `C^2*S^2 = 0`. Coordinate nonnegativity then gives:

```text
semanticKernelPower r 4 = one
  iff
C = 1 or C = 0
```

The `C = 1` branch is identity. In the `C = 0` branch, the unit equation and
`S >= 0` force `S = 1`, so the transported kernel is `(0,1)`. Thus the
first-quadrant restriction excludes nontrivial orders two and three but admits
the quarter-turn kernel.

Exact order four is now recorded explicitly. `SemanticExactKernelOrderFour`
requires the fourth power to be neutral and excludes neutrality of powers
one, two, and three. It is equivalent to semantic core zero. The same
hypothesis determines semantic beam one, so the exact-order branch is
precisely the transported real kernel `(0,1)`. This also confirms that its
intermediate real-side powers need not remain in the transported first
quadrant, which is why kernel multiplication remains confined to the real
side.

The same exact-order statement now holds for the plane action. Exact kernel
order four is equivalent to exact action order four, and both are equivalent
to semantic core zero. This is where the strength of the CF2D addition law
becomes explicit:

```text
unit-square preservation
  constrains every kernel to the unit locus

associative star product and act_star
  turn repeated addition of phase into finite kernel multiplication

faithfulness of the action
  recovers kernel equality from equality of plane actions
```

The preservation law alone would not classify finite order. The classification
comes from preservation, the addition/product law, faithful action, and the
first-quadrant semantic boundary acting together.

The conceptual order is boundary first, action second, geometry later.
`q2` initially acts as a boundary detector for conserved level sets; it has
not yet been identified with Euclidean squared radius. The exact-order-four
action is therefore proved before any circle, orthogonality, angle, full-turn,
or degree convention exists. After choosing the standard Euclidean model, the
same algebraic action can be read as a quarter-turn. That geometric reading is
a model of the theorem, not an ingredient of its proof.

The boundary action now has an explicit coordinate orbit without geometric
terminology:

```text
(x,y)
  -> (-y,x)
  -> (-x,-y)
  -> (y,-x)
  -> (x,y)
```

For every nonzero vector this sequence has minimal period four. The origin is
fixed, so exact order of the action as a function must remain distinct from
the minimal period of each point. Again, the four-step algebraic return is the
primary theorem; interpreting the displayed orbit as motion around a circle
comes later.

The next structural boundary is source-level `Vec.star` and `KernelFamily`.
Both require signed arithmetic. They should wait for a signed DkReal layer
rather than forcing subtraction into `DkNNRealQ`. Until then, further work can
remain on the real side, for example classifying low product orders through
explicit semantic coordinate identities. Order reflection remains a separate,
heavier task.
