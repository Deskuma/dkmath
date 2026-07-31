# FLT7-FUSION-004B U1.2 oriented carrier valuation ownership report

Date: 2026-07-30

Execution mode: ULTRA

Active phase: U1

Event: U1.2

Starting commit: `bdae8f834d716a56bfd1d40dfae0c220cbdd5a5a`

Ending commit: this U1.2 Event commit

## Completed Lean facts

The concrete degree-six carrier is now proved to be an integral domain:

```text
SevenCyclotomicDegreeSixInt.ringIsDomain.
```

The proof embeds it into the quadratic algebra over the fraction field of the
real cubic domain and proves the defining quadratic irreducible there.  This
is a domain proof for the concrete carrier; it does not identify the carrier
with a full ring of integers.

The prime above seven is explicit:

```text
ramifiedUniformizer = 1 - zeta
ramifiedPrime = Ideal.span {ramifiedUniformizer}.
```

Its residue map is a surjective homomorphism to `ZMod 7`, so the kernel is
maximal.  Lean proves

```text
ofReal eisensteinAxis = zetaInv * ramifiedUniformizer^2
ofReal 7 = ramifiedUniformizer^6 * ramifiedSevenUnit
```

with `ramifiedSevenUnit` a unit.  Each of the two linear carriers belongs to
`ramifiedPrime` but not to `ramifiedPrime^2`; its ramified multiplicity is
therefore exactly one.

For the unramified layer, `QuotientPrimeSupport` contains every rational prime
dividing the absolute signed `quotientRoot`, not only primes already present
in one of the two routed load cells.  Each support prime receives its
canonical real kernel and the two degree-six orientations.

For every support prime `s` and every natural exponent `k`, Lean proves the
exact cutoffs

```text
carrier ∈ s.orientedKernel^k
  ↔ k ≤ s.quotientExponent

conjugateCarrier ∈ s.conjugateKernel^k
  ↔ k ≤ s.quotientExponent,
```

where

```text
s.quotientExponent =
  padicValNat s.1 (Int.natAbs quotientRoot).
```

The opposite orientation is excluded already at the first power.  The proof
of the upper cutoff multiplies by the conjugate carrier, contracts the
extended real ideal through the faithfully flat quadratic algebra, removes
the ramified axis using coprimality, and applies the exact real-core cutoff.

The full phase-zero real factor product is reconstructed exactly:

```text
globalRealCoreFactorIdeal
  = Ideal.span {realPairCore 0}.
```

Its degree-six extension splits into the complete oriented and conjugate
halves.  After adjoining one ramified-prime factor to each half, Lean obtains
the two predicted carrier factors:

```text
globalOrientedCarrierFactorIdeal
globalConjugateCarrierFactorIdeal.
```

Their product equals the product of the two carrier principal ideals.  The
individual lower factorizations leave two residual ideals `J` and `K`.
Integral-domain cancellation forces `J*K = top`; hence `J = top` and
`K = top`.  This closes the two exact global equalities:

```text
globalOrientedCarrierFactorIdeal_eq_span_carrier
globalConjugateCarrierFactorIdeal_eq_span_conjugateCarrier.
```

The principal conclusions and all local cutoffs are bundled in

```text
globalCarrierValuationOwnershipPacket.
```

## New modules

```text
SevenRamifiedFusionCyclotomicDegreeSixDomain.lean
SevenRamifiedFusionCyclotomicRamifiedPrime.lean
SevenRamifiedFusionOrientedCarrierValuationOwnership.lean
```

The ownership module is imported by the public `DkMath.FLT.Seven` facade.

## Mathematical interpretation

The choice of orientation is no longer only a local load address.  Every
prime dividing the complete quotient root is owned by exactly one of the two
linear carriers, with its complete ordinary exponent.  The prime above seven
is separately accounted for at exact exponent one.  No unidentified ideal
factor remains in either carrier principal ideal.

This includes residual-only primes and therefore supplies the full input
needed for U1.3.  It also preserves the original routed-load exponents, since
they embed into the same canonical full support.

## Exact remaining obligation

For each full-support prime, the already proved integer norm ledger predicts

```text
quotientExponent
  = load21Exponent + load22Exponent + 7 * residualExponent.
```

Event U1.3 must lift this equality pointwise to the oriented and conjugate
finite ideal products and prove

```text
carrier ideal
  = ramified prime * loaded half ideal * residual half ideal^7
```

and its conjugate.  It must then expose the exact principality and unit data
required to pass from ideals to elements.

This Event does not claim:

- a generator for either oriented half ideal;
- a seventh-power unit-class criterion;
- an element-level carrier power decomposition;
- a primitive additive Fermat chart;
- strict decrease, descent closure, or FLT7.

## Build verification

The focused ownership-module build and the public facade build succeeded.
The three new modules contain no `sorry`, explicit `axiom`, or
`native_decide`.  Printed axiom dependencies are limited to the standard
`propext`, `Classical.choice`, and `Quot.sound`.

## Outcome

Outcome A: U1.2 is complete with exact local valuation cutoffs and exact
global principal-ideal ownership for both conjugate carriers.

Next selected Event:

```text
ULTRA / U1.3 — seventh-power residual ideal extraction
```
