# PCK-009 campaign closeout report

## Final outcome

The Primitive Conservation Kernel campaign is complete at its finite,
bounded square-world boundary. The theorem graph is consolidated, the
generic abstraction question has been audited, and the relevant public
aggregators now expose the stable owner modules.

The final classifications are:

    PCK-CAMPAIGN: COMPLETE
    FINITE-SQUARE-PRIME-CLOSURE: COMPLETE
    COARSE-TO-FINE-CERTIFICATION: COMPLETE
    PRIMITIVE-CONSERVATION-DICHOTOMY: COMPLETE
    PRIMORIAL-PRODUCT-BRIDGE: COMPLETE
    CANONICAL-30-WORLD-REGRESSION: COMPLETE

    GENERIC-PRIMITIVE-KERNEL: NOT-YET-JUSTIFIED
    DKMATH-LIB-GNOMON: CANDIDATE / SEPARATE CAMPAIGN

    LEGENDRE: NOT PROVED BY PCK
    RH: NOT ADDRESSED BY PCK

The starting branch was
`wip/number-theory-primitive-conservation-kernel-260903-v0`.
The starting HEAD was
`17e58f7ffb670dda8dea928374518704224a5036`
(`docs(PCK): add PCK-009 campaign closeout audit instructions`).
The worktree was clean at the start.

## PCK-009 changes

The PCK-009 implementation changes are limited to public-surface updates and
this closeout report:

- `DkMath/NumberTheory/Primitive.lean`
  - Exports `SquarePrimeExpansion` and
    `PrimitiveConservationKernel`; its docstring now names the finite square
    expansion and nested old-or-one-fresh facade.
- `DkMath/NumberTheory/PrimorialUniverse.lean`
  - Exports `SquareBodyBridge` and documents that `ThirtySquareWorld` remains
    a separate concrete regression module.
- `DkMath/CosmicFormula.lean`
  - Exports `SquareGnomon` and adds the minimal public-surface description.
- `docs/dev/NumberTheory-PrimitiveConservationKernel-260903-v0/report-011-closeout.md`
  - Added this report.

No theorem was duplicated in an aggregator. `ThirtySquareWorld` was kept
concrete and was not made public by default. `HalfUnitZeroConjugate` remains a
direct-import algebraic coordinate layer.

## Campaign source inventory

The source files added or modified by the campaign, including the files
owned by earlier checkpoints, are:

- `DkMath/CosmicFormula/HalfUnitZeroConjugate.lean`
- `DkMath/CosmicFormula/SquareGnomon.lean`
- `DkMath/NumberTheory/Primitive/SquareBody.lean`
- `DkMath/NumberTheory/Primitive/SquarePrimeExpansion.lean`
- `DkMath/NumberTheory/Primitive/PrimitiveConservationKernel.lean`
- `DkMath/NumberTheory/PrimorialUniverse/SquareBodyBridge.lean`
- `DkMath/NumberTheory/PrimorialUniverse/ThirtySquareWorld.lean`

The campaign reports are `report-002.md` through `report-010.md`; this file
is the closeout report for PCK-009.

## Checkpoint theorem graph

Each layer is classified by its role in the graph.

### PCK-001 — new real algebraic owner

Owner: `DkMath.CosmicFormula.HalfUnitZeroConjugate`.

    zeroConjugateUniverse_eq_mul
    zeroConjugateUniverse_eq_zero_iff
    zeroConjugateUniverse_reflection

This is focused half-unit zero-conjugate algebra. It is independent of the
prime, primorial, Legendre, and analytic routes.

### PCK-002 — thin arithmetic lemma

Owner: `DkMath.NumberTheory.Primitive.SquareBody`.

    squareBody_mono

This is the monotonic nesting bridge for the natural square Body.

### PCK-002G — new degree-two algebraic owner

Owner: `DkMath.CosmicFormula.SquareGnomon`.

    squareGnomonKernel_eq_GTail
    squareGnomon_eq_mul_two_mul_add
    core_add_squareGnomon_eq_next_square
    bodyN_two_add_squareGnomon
    bigN_two_step_fixedGap
    squareGnomonKernel_step
    squareGnomon_step
    squareGnomon_scale

This freezes the generic degree-two Gnomon/GN vocabulary and its exact
finite algebraic identities.

### PCK-003 — thin coarse-to-fine adapter

Owner: `DkMath.NumberTheory.Primitive.SquareBody`.

    prime_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody

It composes `squareBody_mono` with the existing complete-support
certification theorem.

### PCK-004 — thin self-fresh adapter

Owner: `DkMath.NumberTheory.Primitive.SquareBody`.

    freshPrimeDirection_self_of_supportDisjointFrom_primeScalesUpTo_coarse_of_le_fine_squareBody

It packages the certified escaping point itself as the fresh prime direction.

### PCK-005 — finite semantic construction

Owner: `DkMath.NumberTheory.Primitive.SquarePrimeExpansion`.

    squarePrimeExpansion
    mem_squarePrimeExpansion_iff
    squarePrimeExpansion_eq_primeScalesUpTo_squareBody

This is an exact finite closure operator and equality, not an unbounded prime
generation algorithm.

### PCK-006 — thin product-anchor adapter

Owner: `DkMath.NumberTheory.PrimorialUniverse.SquareBodyBridge`.

    finitePrimeBasis_subset_primeScalesUpTo_product
    prime_of_supportDisjointFrom_productClosure_of_le_fine_squareBody

It connects a finite generating basis to its product anchor and then to the
complete canonical prime closure.

### PCK-007 — concrete regression

Owner: `DkMath.NumberTheory.PrimorialUniverse.ThirtySquareWorld`.

    primeBasis235_subset_primeScalesUpTo_thirty
    primeScalesUpTo_thirty_eq
    squareBody_thirty
    squarePrimeExpansion_thirty_eq_primeScalesUpTo_960
    prime_of_supportDisjointFrom_thirtyClosure_of_le_fine_squareBody
    fortyNine_basis_vs_completeClosure_firewall

This records the concrete `{2, 3, 5} -> 30 -> 960` regression and the 49
basis-versus-closure firewall.

### PCK-008 — semantic facade

Owner: `DkMath.NumberTheory.Primitive.PrimitiveConservationKernel`.

    primitiveConservationKernel_dichotomy_of_le_fine_squareBody

It applies `squareBody_mono` and the existing bounded old-or-one-fresh split.
It adds no generic structure and reproves no factorization law.

## Dependency direction

The source dependency graph is:

    HalfUnitZeroConjugate
      -> independent real algebra

    CosmicFormulaBinom
      -> SquareGnomon
      -> CosmicFormula public aggregator

    PrimitiveDirection + FinitePrimeWorld + CosmicFormulaBinom
      -> SquareBody
        -> SquarePrimeExpansion
        -> PrimitiveConservationKernel

    FinitePrimeSynchronization + SquarePrimeExpansion
      -> SquareBodyBridge
        -> ThirtySquareWorld
      -> PrimorialUniverse public aggregator

    SquareBody + SquarePrimeExpansion + PrimitiveConservationKernel
      -> Primitive public aggregator

The public aggregators depend on owner modules; no owner was changed to import
its aggregator. The Legendre modules consume the SquareBody interface, while
the Collatz Gnomon owner consumes the separate SquareGnomon vocabulary.

## Generic PrimitiveKernel audit

Repository reconnaissance found the exact interface

    PrimeScaleGeneratedBy
    FreshPrimeDirection
    bounded cofactor
    unique fresh direction
    squareBody bound

in the generic direction layer, the SquareBody owner, and downstream square
and Legendre consumers. The Legendre consumer is a specialization of the
same square-Body theorem, not an independent non-square realization. The
generic GN bridge uses `FreshPrimeDirection`, but does not provide the full
bounded-cofactor, unique-fresh, square-Body law package. No second independent
domain with the same exact laws was found.

Therefore the abstraction is deferred:

    GENERIC-PRIMITIVE-KERNEL: NOT-YET-JUSTIFIED

No `PrimitiveKernel` structure, class, definition, equivalent record, or
generic theorem family was created. Extraction should wait until a second
independent non-square consumer exists with the same laws and without forced
square semantics.

## Gnomon promotion audit

The current status is:

    DKMATH-LIB-GNOMON: CANDIDATE / SEPARATE CAMPAIGN

The evidence is the existing generic owner
`DkMath.CosmicFormula.SquareGnomon`, its independent vocabulary consumer
`DkMath.Collatz.GnomonEvaluation`, and the exact GN/GTail, square-growth,
fixed-Gap, kernel-increment, area-increment, and scaling identities.

Promotion was not part of PCK-009. A future promotion requires a dedicated
audit of canonical names and namespace, Collatz bridge direction,
import-cycle freedom, and whether the algebra should remain square-specific
or move to a more general Gnomon owner. No file was renamed or moved.

## Final finite mathematical architecture

For complete-support certification, if

    q ≤ P
    1 < m ≤ squareBody q
    SupportDisjointFrom (primeScalesUpTo P) m

then `m` is prime and is itself a fresh direction above the complete old
world.

The exact finite closure is:

    squarePrimeExpansion P = primeScalesUpTo (squareBody P)

For a finite prime basis `S`, the coarse product bridge is:

    S ⊆ primeScalesUpTo (finitePrimeBasisProduct S)

The basis is not identified with the complete closure.

For the Primitive Conservation Kernel, if

    q ≤ P
    0 < m ≤ squareBody q

then either `m` is entirely generated by `primeScalesUpTo P`, or

    m = p * k

with one unique fresh prime `p > P`, positive old-generated `k ≤ P`, and
`Nat.Coprime p k`. The fresh direction is controlled to depth one in this
split. Old-generated cofactors may still contain repeated old prime powers.

## Preserved firewalls

- The generating basis is not the complete closure:
  `{2, 3, 5} != primeScalesUpTo 30`; the concrete witness is the 49 firewall.
- Wheel or PHZ survival against a generating basis is candidate-seat
  information, not primality.
- `FreshPrimeDirection` records one fresh prime divisor; it is weaker than
  `SupportDisjointFrom`, which excludes every old prime direction.
- “Primitive” is not universal squarefreeness. PCK-008 controls only the
  selected fresh direction to depth one; old cofactors can have repeated old
  prime powers.
- PCK-005 is an exact finite equality, not an unbounded prime algorithm or an
  asymptotic efficiency claim.
- PCK is not Legendre: it does not prove that every interval between
  consecutive squares contains a prime.
- PCK is not RH: it supplies no zeta, Xi, PHZ analytic, CFBRC, zero-derived
  provider, or RH theorem.

## Verification matrix

All required focused owners passed:

| Module | Result |
|---|---|
| `DkMath.CosmicFormula.SquareGnomon` | success, 8666 jobs |
| `DkMath.NumberTheory.Primitive.SquarePrimeExpansion` | success, 8669 jobs |
| `DkMath.NumberTheory.Primitive.PrimitiveConservationKernel` | success, 8669 jobs |
| `DkMath.NumberTheory.PrimorialUniverse.SquareBodyBridge` | success, 8672 jobs |
| `DkMath.NumberTheory.PrimorialUniverse.ThirtySquareWorld` | success, 8673 jobs |

The changed public aggregators also passed:

| Module | Result |
|---|---|
| `DkMath.NumberTheory.Primitive` | success, 8677 jobs |
| `DkMath.NumberTheory.PrimorialUniverse` | success, 8702 jobs |
| `DkMath.CosmicFormula` | success, 8745 jobs |

`git diff --check` passed. A trailing-whitespace audit over the changed
source and report files passed.

The three final public load-bearing theorem axiom checks were:

    squarePrimeExpansion_eq_primeScalesUpTo_squareBody
    primitiveConservationKernel_dichotomy_of_le_fine_squareBody
    prime_of_supportDisjointFrom_productClosure_of_le_fine_squareBody

Each reported only:

    propext, Classical.choice, Quot.sound

The campaign source audit found no `sorry`, `admit`, `native_decide`, or
project `axiom` declarations, and no forbidden RH, CFBRC, zeta, Xi, PHZ, or
analytic import in the campaign owner files.

## Remaining future work and readiness

The campaign boundary is ready for consolidation as a finite theorem and
public-surface package. Future work is separate from PCK-009:

1. Gnomon library promotion and resolution-refinement audit.
2. Use PCK as an arithmetic provider inside the Legendre work.
3. Investigate higher-degree analogues only after identifying an exact bounded
   replacement for `squareBody`.
4. Continue RH/CFBRC work on its independent provider frontier.

These items are not part of the PCK theorem graph. PCK-009 closes the current
campaign at the finite square-world and primitive-conservation boundary.
