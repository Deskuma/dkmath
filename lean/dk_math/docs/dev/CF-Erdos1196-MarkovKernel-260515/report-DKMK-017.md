# DKMK-017: report

DKMK-017 is the route-validation chapter for analytic input sources.

The chapter started from the DKMK-016 route:

```text
GeometricBudgetSource
+ first-band bound
+ uniform decay
+ increment nonnegativity
  -> DyadicBandAnalyticEstimate
  -> TruncationEnvelopeEstimate
  -> finite-step route
```

The goal was not to prove the final logarithmic analytic estimate.  The goal
was to make the remaining analytic inputs concrete enough that a real
`Nat -> Rat` source could pass through the existing DkMath hitting machinery.

## 1. Source surface

DKMK-017A-F organized the caller-facing source surface.

The accepted standard route is:

```text
ratio : Rat
error : Real

0 <= (ratio : Real)
(ratio : Real) < 1

(increment 0 : Real) <= (1 + error) * (1 - (ratio : Real))

forall k, k <= K -> 0 <= increment k
forall k, k < K -> increment (k + 1) <= ratio * increment k

  -> TruncationEnvelopeEstimate
```

This reduced the source obligations to:

```text
hbaseBudget
hinc_nonneg
hdecay
```

without requiring callers to manipulate `Finset.range`, geometric sums, or
intermediate source packages directly.

## 2. Candidate discovery

DKMK-017H searched the existing PrimitiveSet / SourceMassTruncation area.

No concrete dyadic-band `increment : Nat -> Rat` source was already exposed.
Existing concrete candidates were finite or sample-shaped, such as
`Bool -> Rat`, and existing dyadic routes still took `increment : Nat -> Rat`
as external input.

The chosen test source was therefore:

```lean
def geometricIncrement (base ratio : Rat) (k : Nat) : Rat :=
  base * ratio ^ k
```

## 3. Geometric route validation

DKMK-017I introduced `geometricIncrement` and proved:

```text
0 <= base, 0 <= ratio
  -> forall k, 0 <= geometricIncrement base ratio k

geometricIncrement base ratio 0 = base

geometricIncrement base ratio (k + 1)
  = ratio * geometricIncrement base ratio k
```

It also connected the source to:

```text
FirstBandDecayBudgetSource
TruncationEnvelopeEstimate
```

assuming the first-band budget:

```text
(base : Real) <= (1 + error) * (1 - (ratio : Real))
```

## 4. Canonical budget

DKMK-017J specialized the test source to:

```text
base = 1 - ratio
```

Under:

```text
0 <= ratio
(ratio : Real) < 1
0 <= error
```

Lean closes the first-band budget internally and reaches:

```text
TruncationEnvelopeEstimate
  (Finset.range (K + 1))
  (fun k : Nat => x * 2^k)
  (geometricIncrement base ratio)
  error
```

## 5. Finite-step route connection

DKMK-017K checked that the envelope is consumed by the existing finite-step
route.

The route now reaches:

```text
base = 1 - ratio
0 <= ratio
(ratio : Real) < 1
0 <= error
PrimitiveOn A
  -> weightedHitMass A <= 1 + error
```

through:

```text
geometricIncrement
  -> canonical first-band budget
  -> TruncationEnvelopeEstimate
  -> finiteStepTailNatMassSpace
  -> quotient-path weightedHitMass bound
```

## 6. Decision

DKMK-017 is route-validation complete.

The geometric source is accepted as a canonical test source.  It is not the
final analytic/logarithmic source for Erdos #1196, but it proves that the
transport path is live:

```text
concrete Nat -> Rat increment
  -> truncation envelope
  -> finite-step tail mass
  -> quotient-path hitting bound
```

## 7. Next branch

Stop adding convenience wrappers for the geometric test source unless they
remove real friction.

The next branch should identify a meaningful analytic replacement source:

```text
logarithmic source
capacity-derived source
dyadic band mass estimate
quotient-path local decay source
```

The next main question is:

```text
what should replace geometricIncrement as the analytic source?
```
