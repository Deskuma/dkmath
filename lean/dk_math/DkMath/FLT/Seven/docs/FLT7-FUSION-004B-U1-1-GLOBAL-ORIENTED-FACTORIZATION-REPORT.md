# FLT7-FUSION-004B U1.1 global oriented prime factorization report

Date: 2026-07-30

Execution mode: ULTRA

Active phase: U1

Event: U1.1

Starting commit: `53dea79086b7bd1a861df9fbc2e8adc901a995e5`

Ending commit: this U1.1 Event commit

## Completed Lean facts

The concrete degree-six carrier now has an explicit order-three ring
automorphism:

```text
SevenCyclotomicDegreeSixInt.rotateEquiv
```

It extends `SevenRealCubicInt.rotateEquiv`, sends `zeta` to `zeta^2`, has
third iterate equal to the identity, and commutes with quadratic conjugation:

```text
rotateEquiv_ofReal
rotateEquiv_zeta
rotateEquiv_three
rotateEquiv_star.
```

For every canonical supported rational prime, Lean defines the three
transported evaluations and their quadratic conjugates:

```text
cyclicEval
cyclicKernel
cyclicConjugateEval
cyclicConjugateKernel.
```

The degree-six rotation cycles the three oriented kernels and separately
cycles their three conjugates. Quadratic conjugation exchanges the two
kernels at every phase. Their contractions are exactly the corresponding
existing real-cubic Galois kernels:

```text
PrimeSupport.cyclicKernel_comap_ofReal
PrimeSupport.cyclicConjugateKernel_comap_ofReal.
```

The N1 exact fibre equality transports to every phase:

```text
PrimeSupport.map_galoisKernel_eq_cyclicPrimePair
PrimeSupport.map_galoisKernelPower_eq_cyclicPairPower.
```

The latter retains the unchanged exponent
`padicValNat q (family.cell p)`.

Finally, `globalCyclicOrientedFactorIdeal` is the finite product of those
phase-indexed pair powers. It is cycled by the degree-six rotation, fixed by
quadratic conjugation, and satisfies the exact all-three-load theorem:

```text
globalCyclicOrientedFactorIdeal_eq_span_ofReal_load
```

or, for every `i : Fin 3`,

```text
globalCyclicOrientedFactorIdeal family p i
  = Ideal.span {ofReal (family.load p i)}.
```

These results and the unchanged N2 launchpad are bundled in
`GlobalOrientedPrimeFactorizationPacket`.

## New module

`SevenRamifiedFusionGlobalOrientedPrimeFactorization.lean`

The module is imported by the public `DkMath.FLT.Seven` facade.

## Mathematical interpretation

U1.1 no longer keeps the real order-three action and degree-six orientation
as unrelated layers. The explicit lift gives a coherent

```text
three real phases x two quadratic orientations
```

indexing of all six primes. Exact extension, exponents, support, and routing
provenance are preserved at every phase, and each complete finite product is
the correct mapped principal load ideal.

This construction uses the concrete quadratic carrier directly. It does not
identify it with the full ring of integers and does not assume unique
factorization or principality of the individual oriented primes.

## Exact remaining obligation

Event U1.2 must determine the exact multiplicity of the phase-selected primes
in the actual linear carriers:

```text
signedRightRoot - zeta * signedLeftRoot
signedRightRoot - zetaInv * signedLeftRoot.
```

The total multiplicity must include both routed loads and the residual
seventh-power contribution. The prime above seven must be treated separately
from the nonramified quotient-prime support.

This Event does not claim:

- carrier-prime valuation ownership;
- load-times-seventh-power residual extraction;
- principality of an oriented half ideal;
- an element-level seventh-power decomposition;
- a primitive additive Fermat chart;
- strict decrease, descent closure, or FLT7.

## Build verification

The focused module build and the public facade build succeeded. The new
module contains no `sorry`, explicit `axiom`, or `native_decide`. Printed
axiom dependencies are limited to the standard
`propext`, `Classical.choice`, and `Quot.sound`.

## Outcome

Outcome A: U1.1 is complete, public, and provenance preserving.

Next selected Event:

```text
ULTRA / U1.2 — oriented carrier valuation ownership
```
