# FLT7-FUSION-004B U1.3 seventh-power residual ideal extraction report

Date: 2026-07-30

Execution mode: ULTRA

Active phase: U1

Event: U1.3

Starting commit: `88b27e10`

Ending commit: this U1.3 Event commit

## Completed Lean facts

Lean chooses a canonical natural residual root from the already proved
two-cell seventh-power factor:

```text
row2ResidualNormRoot
quotientRoot_natAbs_eq_row2Loads_mul_residualNormRoot_pow.
```

The exact natural identity is

```text
Int.natAbs quotientRoot
  = c21 * c22 * row2ResidualNormRoot^7.
```

All three factors are nonzero.  Applying `padicValNat` gives, for every prime
`q`,

```text
padicValNat q (Int.natAbs quotientRoot)
  = padicValNat q c21
      + padicValNat q c22
      + 7 * padicValNat q row2ResidualNormRoot.
```

The first U1.3 module records the corresponding real-pair ideal identity and
its extension to the degree-six carrier.  At this intermediate level the
residual is deliberately the complete conjugate-pair ideal:

```text
RealPairLoadedPowerSplit.span_realPairCore_eq_loads_mul_residual_pow
RealPairLoadedPowerSplit.carrierIdealPair_eq_ramified_sq_mul_loadHalves_mul_residualPair_pow.
```

The second module performs the oriented extraction.  Every routed-cell prime
is embedded canonically into `QuotientPrimeSupport`.  The embedding preserves
the canonical `mu_7` address and both degree-six kernels.  Lean then proves
that extending a cell product to the full quotient-root support only inserts
unit factors:

```text
globalOrientedFullSupportLoadHalfIdeal_eq_globalCyclicOrientedHalfIdeal
globalConjugateFullSupportLoadHalfIdeal_eq_globalCyclicConjugateHalfIdeal.
```

The combined full-support load products are therefore exactly the existing
phase-zero load halves:

```text
globalOrientedLoadedHalfIdeal_eq_orientedLoadedHalfIdeal
globalConjugateLoadedHalfIdeal_eq_conjugateLoadedHalfIdeal.
```

The explicit residual halves are

```text
globalOrientedResidualIdeal
globalConjugateResidualIdeal,
```

whose local exponent at `q` is
`padicValNat q row2ResidualNormRoot`.  The pointwise exponent identity lifts
to both complete unramified products:

```text
globalOrientedCoreHalfIdeal_eq_loaded_mul_residual_pow
globalConjugateCoreHalfIdeal_eq_loaded_mul_residual_pow.
```

After adjoining the already proved exact ramified factor, this gives the
principal carrier identities

```text
Ideal.span {carrier}
  = globalOrientedLoadedCarrierIdeal
      * globalOrientedResidualIdeal^7

Ideal.span {conjugateCarrier}
  = globalConjugateLoadedCarrierIdeal
      * globalConjugateResidualIdeal^7.
```

Quadratic conjugation exchanges the oriented and conjugate loaded halves and
the two residual halves.  The completed identities are exposed in the compact
U1.3 packet.

## New modules

```text
SevenRamifiedFusionLoadedResidualIdealBridge.lean
SevenRamifiedFusionSeventhPowerResidualIdealExtraction.lean
```

The final extraction module is imported by the public `DkMath.FLT.Seven`
facade.

## Mathematical interpretation

No quotient-root prime is omitted.  The two inherited routing cells account
for their exact non-seventh-power exponents, and all remaining multiplicity is
the seventh multiple attached to one explicit residual half ideal.  The
orientation selected in U1.2 is preserved throughout, and quadratic
conjugation supplies the other carrier without a second arbitrary choice.

Thus the U1.3 question has a positive ideal-level answer:

```text
carrier ideal = explicit loaded ideal * seventh-power ideal.
```

## Exact remaining obligation and selected route

An equality of ideals does not itself provide element witnesses.  U1.4 needs:

- principality of the concrete degree-six carrier;
- a generator of each residual ideal;
- a generator of each ramified loaded carrier ideal;
- an exact associated-unit treatment;
- compatibility with quadratic conjugation.

The selected narrow route is a surjective integral power-basis map from the
ring of integers of the seventh cyclotomic field onto the concrete carrier.
Principality transports along this surjection, so a full ring-of-integers
equivalence is unnecessary.  The associated unit may be absorbed into the
chosen load generator; it must not be assumed to be a seventh power.

This Event does not claim:

- concrete principality or a carrier PID instance;
- an element-level carrier equation;
- that either routed load cell is a seventh power;
- that an arbitrary unit is a seventh power;
- a primitive additive Fermat chart;
- strict decrease, descent closure, or FLT7.

## Build verification

The focused builds of both new modules and the public facade build succeeded.
The new modules contain no `sorry`, explicit `axiom`, or `native_decide`.
Printed axiom dependencies are limited to the standard `propext`,
`Classical.choice`, and `Quot.sound`.

## Outcome

Outcome A: U1.3 is complete with the exact oriented and conjugate
load-times-seventh-power carrier-ideal decompositions.

Next selected Event:

```text
ULTRA / U1.4 — element-level oriented power or exact obstruction
```
