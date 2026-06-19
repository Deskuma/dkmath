# DKMK-018: report

DKMK-018 is the analytic source replacement chapter.

DKMK-017 validated that a concrete rational source can travel through:

```text
TruncationEnvelopeEstimate
  -> finiteStepTailNatMassSpace
  -> quotient-path weightedHitMass bound
```

using `geometricIncrement` as a route-validation source.

DKMK-018 replaced that toy source with the first meaningful analytic source:

```text
PrimePowerWitnessProvider.logCapacityKernelRealWeightProvider
```

The result is an end-to-end route from the log-capacity Real provider to the
finite-step weighted-hit estimate.

## 1. Initial type gap

The chapter started from the type mismatch:

```text
LogCapacityKernel / RealLog source : Real-valued weights
DKMK-017 finite-step route         : Rat-valued increments
```

The question was not whether the log-capacity weights are nonnegative or
sub-probability.  Those facts already existed on the Real side.

The question was:

```text
Can a Real-valued analytic source certify the existing Rat route?
```

## 2. Real majorant bridge

DKMK-018B introduced the core bridge:

```lean
TruncationEnvelopeEstimate.ofRealMajorant
TruncationEnvelopeEstimate.ofRealWeightProviderMajorant
DyadicBandAnalyticEstimate.ofRealMajorant
```

This proved that a rational increment can remain the finite-step source while
a Real-valued analytic provider supplies the upper envelope:

```text
increment : i -> Rat
majorant  : i -> Real

0 <= increment i
(increment i : Real) <= majorant i
sum majorant <= 1 + error
  -> TruncationEnvelopeEstimate
```

Therefore no Real-native finite-step mass refactor was needed.

## 3. Log-capacity provider attachment

DKMK-018C attached the concrete source:

```lean
PrimePowerWitnessProvider.logCapacityKernel_truncationEnvelope_of_ratMajorizedIncrement
PrimePowerWitnessProvider.logCapacityKernel_truncationEnvelope_zeroIncrement
```

The main surface kept the rationalization policy external:

```text
increment : Nat -> Rat
0 <= increment q
(increment q : Real) <=
  (logCapacityKernelRealWeightProvider n I hI hn).weight q
  -> TruncationEnvelopeEstimate I threshold increment error
```

The zero-increment theorem was the smoke test proving the concrete provider
could pass through the bridge.

## 4. Positive rational under-approximation

DKMK-018D solved the generic rationalization problem for positive Real weights:

```lean
RealWeightProvider.exists_positive_rat_below
RealWeightProvider.positiveRatIncrementBelow
RealWeightProvider.positiveRatIncrementBelow_pos
RealWeightProvider.positiveRatIncrementBelow_le_weight
RealWeightProvider.truncationEnvelope_of_positiveRatIncrementBelow
```

The key result is:

```text
forall i in P.index, 0 < P.weight i
  -> exists a selected increment with
       0 < increment i
       (increment i : Real) <= P.weight i
```

and that selected rational increment feeds the existing
`TruncationEnvelopeEstimate` route.

## 5. Log-capacity positivity

DKMK-018E proved that the log-capacity provider satisfies the strict positivity
condition on its selected index:

```lean
PrimePowerWitnessProvider.logCapacityKernelRealWeightProvider_weight_pos
PrimePowerWitnessProvider.logCapacityKernel_truncationEnvelope_positiveRatIncrementBelow
```

The proof uses the witness-provider structure directly:

```text
q in I
  -> Nat.Prime (basePrimeOf q)
  -> 1 < basePrimeOf q
  -> 0 < log (basePrimeOf q)

hn : 1 < n
  -> 0 < log n

therefore:
  0 < log (basePrimeOf q) / log n
```

No positive-support restriction was needed.

## 6. End-to-end weighted-hit connection

DKMK-018F connected the source replacement route to the DKMK-017 endpoint:

```lean
PrimePowerWitnessProvider.logCapacityKernel_finiteStepTail_weightedHitMass_le_one_add_error
```

For a global log-capacity state `s`, it fixes:

```text
n := s.1
I := IOf s.1
```

then runs:

```text
LogCapacityKernel Real provider
  -> strict positive Real weights
  -> positive Rat under-approximation
  -> TruncationEnvelopeEstimate
  -> finiteStepTailNatMassSpace
  -> quotient-path weightedHitMass bound
```

The final bound is:

```text
weightedHitMass A <= 1 + error
```

for primitive `A`.

## 7. Decision

DKMK-018 is complete as the first analytic source replacement milestone.

The chapter answered the initial question:

```text
Can a Real-valued analytic source replace the geometric test source while
still using the existing Rat finite-step route?
```

Answer:

```text
Yes.  The LogCapacityKernel Real provider can be converted to a positive Rat
under-approximation and carried through to the quotient-path weighted-hit
bound.
```

## 8. Non-goals

DKMK-018 did not add:

```text
new asymptotic analysis
Mertens theorem
big-O route
new finite-step Real mass route
new positive-support filter
new threshold selection policy
```

The theorem added in DKMK-018F is intentionally a wrapper: it records the
successful composition of existing route components.

## 9. Next branch

Two natural next directions remain.

API simplification:

```text
The 018F theorem is strong but exposes a long expression involving
s.1, IOf s.1, and positiveRatIncrementBelow.
```

A façade theorem could package this as a shorter caller-facing source route.

Analytic source expansion:

```text
Test whether other Real sources, such as RealLog or dyadic-band providers,
can use the same Real-majorant / positive-rational bridge.
```

The next chapter should choose one of these rather than extending DKMK-018
with more wrappers.
