# FLT7-FUSION-004B global oriented launchpad completion report

Date: 2026-07-30

Execution mode: NORMAL

Active phase: N2

Starting commit: `3b8aa9c3bd932f06c7bb9fae0e0278608515a198`

Ending commit: this N2 checkpoint commit

## Completed Lean facts

For either row-two load family and every member `s` of its existing canonical
`PrimeSupport`, Lean now provides:

- `s.cyclotomicAddress`, obtained from the existing gcd-load address and its
  canonical `mu_7` ratio;
- `s.orientedKernelPower`;
- `s.conjugateKernelPower`;
- `s.orientedPairPower`.

The local extension theorem is:

```text
Ideal.map ofReal s.kernelPower = s.orientedPairPower.
```

After unfolding the definitions, this is precisely

```text
map(ofReal, realKernel^padicValNat(q,cell))
  =
orientedKernel^padicValNat(q,cell)
  * conjugateKernel^padicValNat(q,cell).
```

The exponent and rational-prime support are inherited unchanged from the
real-cubic global factorization.

For distinct members of `PrimeSupport`, the resulting conjugate pair powers
are pairwise comaximal. Their finite product is
`globalDegreeSixOrientedFactorIdeal`, and Lean proves:

```text
map(ofReal, globalLoadFactorIdeal)
  = globalDegreeSixOrientedFactorIdeal

globalDegreeSixOrientedFactorIdeal
  = map(ofReal, span {load})

globalDegreeSixOrientedFactorIdeal
  = span {ofReal load}.
```

These facts are bundled in the canonical
`DegreeSixOrientedLoadFactorizationPacket`.

## New module

`SevenRamifiedFusionDegreeSixOrientedLoadFactorization.lean`

The module is imported by the public `DkMath.FLT.Seven` facade.

## Mathematical interpretation

N1 split one extended real prime into its two conjugate degree-one primes.
N2 applies that equality to every exact prime power in the already proved
finite real-load factorization. It supplies a global ideal-level oriented
factorization without reselecting primes, ratios, or exponents.

The proof only uses:

- the existing real-cubic finite factorization;
- N1 exact conjugate-prime fibre equality;
- preservation of products and powers by `Ideal.map`;
- preservation of coprimality by the ideal map homomorphism.

No degree-six unique factorization or number-field identification is used.

## Exact remaining obligation

The next frontier is not another load-factorization equality. It is valuation
ownership for the two actual linear carriers:

```text
signedRightRoot - zeta * signedLeftRoot
signedRightRoot - zetaInv * signedLeftRoot.
```

The launchpad does not yet determine the exact multiplicity of every oriented
prime in the first carrier or every conjugate prime in the second carrier.
Consequently it does not yet prove a load-times-seventh-power ideal
factorization for either linear carrier.

This checkpoint does not claim:

- that the degree-six carrier is the full ring of integers;
- PID or class number one;
- principality of the individual oriented primes;
- element-level seventh-power extraction;
- a primitive additive Fermat chart;
- strict decrease;
- descent closure;
- FLT7.

## Outcome

Outcome A: the global oriented launchpad is implemented and public.

Next recommended execution mode and phase:

```text
ULTRA / U1, beginning with Event U1.1 review and U1.2 valuation ownership
```

This recommendation is not activation. The operator must explicitly select
ULTRA / U1 before work continues.
