# FPTC-010 report — public facade and bounded closeout

## A. Campaign result

```text
Outcome A — PRIME TRACEONE PUBLIC FACADE AND BOUNDED CLOSEOUT GREEN
```

The final checkpoint adds an import-only public facade, facade-only API and
axiom audits, calibrated p=3/p=5/p=7 regression checks, and this bounded
closeout report. It does not alter the completed FLT3/FLT5 endpoints and does
not import the historical broad `DkMath.FLT` aggregator.

| checkpoint | status | exact bounded result |
|---|---|---|
| FPTC-000 | Outcome A | Structurally discharged the p=7 TraceOne class-group torsion hypothesis using the existing Euclidean/PID carrier. |
| FPTC-001 | Outcome A | Added the neutral finite class-group coprimality criterion. |
| FPTC-002 | Outcome A | Added arbitrary-power TraceOne integer-coordinate recurrence and coordinate theorem. |
| FPTC-003 | Outcome A | Added the arbitrary-power TraceOne core-image landing iff under nonzero norm. |
| FPTC-004 | Outcome A | Added the generic imaginary residual coordinate receiver, leaving its class-group hypothesis explicit. |
| FPTC-005 | Outcome A | Closed the generic p=3 stripped-packet endpoint in the existing Eisenstein unit sectors. |
| FPTC-006 | Outcome A | Established the Golden/TraceOne p=5 carrier bridge, explicit five-sector system, and generic sector endpoint. |
| FPTC-007 | Outcome C | Isolated the prime-discriminant class-number coprimality frontier; no uniform class-number theorem was proved. |
| FPTC-008 | Outcome B | Closed the real `Fin p` receiver and base-norm obstruction, while isolating the p=5 packet bridge frontier. |
| FPTC-009 | Outcome A | Added explicit primitive-counterexample routing into the ramified packet branch or the away simultaneous-power split. |
| FPTC-010 | Outcome A | Exported the bounded architecture through `DkMath.FLT.Prime` and passed the final audits and regressions. |

The B and C outcomes are intentionally retained: they record genuine
frontiers, not failed attempts to be relabelled as completed contradictions.

## B. Strongest checked generic architecture

The public facade is:

```text
DkMath.FLT.Prime
  -> CounterexampleRouting
  -> AdicPowerSplit
  -> TraceOne coordinate-coprime / stripped-ideal packet
  -> conditional ideal-power and class-group bridge
  -> arbitrary-power TraceOne coordinates and landing iff
  -> imaginary coordinate receiver
  -> p=3 and p=5 sector receivers
  -> real Fin p receiver and base-norm obstruction
```

Its exact import surface is:

```text
DkMath.FLT.Prime.CounterexampleRouting
DkMath.FLT.Prime.AdicPowerSplit
DkMath.FLT.Prime.PrimeTraceOneCoordinateCoprime
DkMath.FLT.Prime.PrimeTraceOneStrippedIdeal
DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
DkMath.FLT.Prime.PrimeTraceOneClassGroupClosure
DkMath.FLT.Prime.PrimeTraceOneCoordinateReceiver
DkMath.FLT.Prime.PrimeTraceOneThreeSectorClosure
DkMath.FLT.Prime.PrimeTraceOneFiveSectorClosure
DkMath.FLT.Prime.PrimeTraceOneRealSectorReceiver
```

The facade remains thin and import-only. The p=7 specialized packet is used
only by the calibration test, so the public facade does not pull in the
historical specialized FLT7 stack.

The front-end route is explicit:

```text
PrimitivePrimeCounterexample
  |-- p ∣ (z-y)  -> PrimeAdicFactorPacket p (z-y) y x
  |                 -> existing conditional TraceOne packet architecture
  `-- p ∤ (z-y)  -> gcd(z-y, GTail) = 1
                    -> z-y = a^p and GTail = b^p
                    -> separate away-branch frontier
```

The route does not assert `p ∣ z-y`, and the away branch is not declared
contradictory. The facade is an import/discovery boundary only; it introduces
no new theorem that combines the branches.

## C. Calibrated checked results

The calibration audit passes through the public facade. “Unconditional” here
means that the displayed calibrated structural theorem does not retain an
explicit class-group premise; it does not assert existence of a counterexample
packet or a final FLT contradiction.

### p=3

The audit checks:

```text
signedPrimeParameter 3 = -1
EisensteinInt = TraceOneInt (-1)
classGroupPTorsionFreeAt (TraceOneInt (-1)) 3
eisensteinCubeUnitPowerSectorSystem
eisensteinCubeUnitPowerSectorSystem_complete
exists_eisensteinSector_mul_cube_of_primeTraceOneStrippedIdealPacket_three
```

Thus the generic p=3 stripped-packet endpoint lands in an explicit existing
cube sector. This is the structural generic sector closure, not a replacement
for or a black-box invocation of the specialized final FLT3 proof.

### p=5

The audit checks:

```text
signedPrimeParameter 5 = 1
GoldenInt ≃+* TraceOneInt 1
classGroupPTorsionFreeAt (TraceOneInt 1) 5
goldenTraceOneFifthUnitPowerSectorSystem
exists_goldenSector_mul_fifth_of_primeTraceOneStrippedIdealPacket_five
exists_goldenSector_powCoords_of_primeTraceOneStrippedIdealPacket_five
exists_realSector_mul_pow_with_baseNorm_not_dvd
```

The five Golden sectors and the real coordinate/base-norm receiver are
kernel-checked for an existing generic stripped packet. No generic nonzero
sector is eliminated, and no specialized FLT5 final theorem is imported into
the facade. The packet-to-Golden transport is therefore a checked bridge at
the current structural endpoint, not a completed p=5 contradiction.

### p=7

The audit checks:

```text
signedPrimeParameter 7 = -2
classGroupPTorsionFreeAt (TraceOneInt (-2)) 7
exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket_seven
SevenAdicCounterexamplePacket.toPrimeAdicFactorPacket
```

The p=7 class-group premise is discharged structurally, and the existing
stripped packet reaches the generic imaginary exact/coordinate receiver. The
specialized Seven packet is checked to produce the same generic
`PrimeAdicFactorPacket` target; the specialized FLT7 contradiction remains
outside this facade closeout.

The cheap parameter regressions `signedPrimeParameter 11 = -3` and
`signedPrimeParameter 13 = 3` also pass. They do not discharge the corresponding
generic class-group hypotheses.

## D. Remaining blockers

1. For the generic imaginary `p % 4 = 3` family, the required
   `classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p` still
   needs the prime-discriminant class-number coprimality result isolated in
   FPTC-007.
2. For the real p=5 route, a sufficiently strong generic stripped-packet to
   specialized Golden arithmetic bridge is still required before any generic
   nonzero-sector elimination can be claimed.
3. The away branch currently ends at the coprime simultaneous p-th-power split
   of `z-y` and `GTail`; no checked theorem makes that branch contradictory.
4. No generic coordinate permutation/orientation theorem has been proved for
   all odd primes.

## E. Explicit non-claims

This campaign closeout is not a proof of general FLT. In particular, it does
not claim:

```text
general FLT for all exponents
uniform class number one or uniform class-group p-coprimality
uniform real-sector elimination
an unconditional p=5 nonzero-sector contradiction
an away-branch contradiction
```

The facade records the strongest checked architecture while preserving these
semantic boundaries.

## F. Validation and audits

The following targets passed under Lean 4.34:

```text
lake build DkMath.FLT.Prime
lake build DkMathTest.FLT.Prime.PrimeFacadeApiAudit
lake build DkMathTest.FLT.Prime.PrimeClosureCalibrationAudit
lake build DkMathTest.FLT.Prime.PrimeFacadeAxiomAudit
lake build DkMath.FLT.Prime.CounterexampleRouting
lake build DkMath.FLT.Prime.PrimeTraceOneRealSectorReceiver
lake build DkMath.FLT.Prime.PrimeTraceOneThreeSectorClosure
lake build DkMath.FLT.Prime.PrimeTraceOneFiveSectorClosure
git diff --check
```

The facade-only API audit confirms the public names for primitive routing,
adic packets, arbitrary-power landing, the p=3/p=5/p=7 receivers, and the
real-sector receiver. The facade axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound` for representative public
theorems. Apart from the intentional `#print axioms` commands in the axiom
audit, no fresh `sorry`, `sorryAx`, `admit`, or `unsafe` marker, and no project
axiom, occurs in the newly added FPTC-010 production/API/calibration files.

The build may replay legacy warnings from unrelated provider/research files,
including an existing `sorry` in `ZsigmondyCyclotomicResearch.lean`; that
legacy contamination is not imported by the public facade and is not counted
as a fresh FPTC-010 source defect.

The campaign ROADMAP now records FPTC-009 as Outcome A, FPTC-010 as Outcome A,
FPTC-007 as Outcome C, and FPTC-008 as Outcome B. This is the terminal
FPTC-010 closeout; no harder theory is opened here.
