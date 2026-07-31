# FLT7-FUSION-004B U1.6 strict-descent failure-boundary report

Date: 2026-07-31

Execution mode: ULTRA

Active phase: U1

Event: U1.6

Starting commit: `2dc8423e`

Ending commit: this U1.6 Event commit

## Completed Lean facts

The inherited ramified extraction contains two explicit natural carriers:

```text
internalDepthFourCarrier
outerDepthFiveCarrier.
```

They are the absolute integer coordinates of the extracted quadratic inner
root and the immediately preceding ramified summit root.  Lean proves:

```text
padicValNat_internalDepthFourCarrier :
  padicValNat 7 internalDepthFourCarrier = 4

padicValNat_outerDepthFiveCarrier :
  padicValNat 7 outerDepthFiveCarrier = 5

internalDepthFourCarrier_strictly_decreases :
  padicValNat 7 internalDepthFourCarrier
    < padicValNat 7 outerDepthFiveCarrier.
```

This is an exact seven-adic depth comparison.  It is not a comparison of the
ordinary sizes of the two natural numbers.

The exact counterexample receiver is named:

```text
InternalDepthFourCounterexampleReconstructionObligation p :=
  ∃ x y z (route : AwayValuationTransferPacket x y z),
    route.carrier = internalDepthFourCarrier p.
```

An `AwayValuationTransferPacket` already contains a positive primitive natural
FLT7 counterexample, its away normal form, its exceptional carrier, and its
valuation-transfer equation.  No desired conclusion is inserted as a
typeclass, axiom, or inhabited provider.

The corresponding strict candidate displays the same data together with the
depth inequality.  Lean proves:

```text
internalDepthFourCounterexampleReconstructionObligation_iff_strictDescentCandidate.
```

Hence the inequality is automatic once the carrier reconstruction is
available; it is not an additional arithmetic obligation.

Conditionally on the receiver, Lean exposes the actual counterexample stored
in the route:

```text
exists_strict_awayCounterexample_of_internalDepthFourReconstruction.
```

The final packet:

```text
strictDescentFailureBoundary
```

combines the exact depths `4` and `5`, their strict comparison, the
nonexistence of the visible signed-endpoint Fermat chart, and the equivalence
between reconstruction and the displayed strict candidate.

## New module

```text
SevenRamifiedFusionStrictDescentFailureBoundary.lean
```

The module is imported by the public `DkMath.FLT.Seven` facade.

## Mathematical interpretation

The strict seven-adic inequality sought at U1.6 was already latent in the
ramified quadratic extraction.  The missing theorem is not a bound.  It is
the construction of a new primitive away counterexample whose exceptional
carrier is the extracted depth-four coordinate.

The U1.5 cyclotomic element equation does not construct such a packet.  Its
norm and coordinate ledgers lose additive or phase information, the visible
signed chart is impossible, and the residual generator has a nontrivial
`mu_7` gauge.

Even an inhabitant of the named receiver would establish only this
conditional ramified-to-away route comparison.  Recursive descent still
requires an indexed state transition proving that the old ramified state and
new away route carry successive values of one well-founded counterexample
measure.

## Exact remaining obligation

The next mathematical development must:

1. construct a `mu_7`-invariant additive chart extractor or a canonical phase
   normalization;
2. prove its Fermat identity, nonvanishing, primitivity, signed-to-natural
   normalization, and original terminal provenance;
3. use it to inhabit
   `InternalDepthFourCounterexampleReconstructionObligation`;
4. construct the indexed ramified-to-away state/measure bridge needed for
   recursive closure.

This Event does not claim:

- ordinary magnitude or height decrease;
- an inhabitant of the reconstruction obligation;
- `AwayDescentClosureProvider`;
- recursive descent;
- terminal contradiction;
- FLT7.

## Build verification

The focused U1.6 module build and public facade build succeeded.  The module
contains no `sorry`, `admit`, explicit `axiom`, or `native_decide`.  Printed
axiom dependencies are limited to the standard `propext`,
`Classical.choice`, and `Quot.sound`.

The user additionally confirmed that the complete project build succeeds.
The reported `sorry` warnings occur only in pre-existing, known research
modules outside this checkpoint.

## Outcome

Outcome C: the strict internal seven-adic depth drop is proved, and the exact
remaining counterexample reconstruction and recursive state/measure
obligations are isolated.

Next recommended execution mode and phase:

```text
NORMAL / N3 — stabilization and checkpoint recovery
```
