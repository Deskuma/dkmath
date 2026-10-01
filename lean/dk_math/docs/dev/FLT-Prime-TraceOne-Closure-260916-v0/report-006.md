# FPTC-006 report — p=5 Golden/TraceOne sector closure

## Outcome

**Outcome A — P5 GOLDEN/TRACEONE GENERIC SECTOR CLOSURE GREEN**

Statuses:

- `FPTC-P5-GOLDEN-TRACEONE-RING-EQUIV-GREEN`
- `FPTC-P5-EXPLICIT-GOLDEN-SECTOR-SYSTEM-GREEN`
- `FPTC-P5-CLASSGROUP-DISCHARGED-GREEN`
- `FPTC-P5-GENERIC-SECTOR-CLOSURE-GREEN`

The implementation is on branch `research/FLT-Prime-TraceOne-Closure-260916-v0`.
The scope is the structural p=5 bridge and the generic stripped-ideal endpoint.
It does not prove an FLT5 contradiction, eliminate a nonzero sector, or identify
the real-sector system with the transported golden system.

## Implemented declarations

`DkMath/FLT/Five/TraceOneBridge.lean` now contains the coordinate-preserving
inverse `traceOneToGolden` and the ring equivalence
`goldenTraceOneRingEquiv : GoldenInt ≃+* TraceOneInt 1`.  Coordinate inverse,
addition, multiplication, conjugation, norm, powers, and the golden unit
generator map were checked.  The norm statement uses the existing
`goldenNorm_eq_traceOneNorm_one` theorem; no second norm definition was added.

`DkMath/FLT/Prime/PrimeTraceOneFiveSectorClosure.lean` adds
`goldenTraceOneFifthUnitPowerSectorSystem`, with `Sector := Fin 5` and
representatives transported from the actual golden units
`goldenPhi ^ i.val`.  Its completeness proof pulls an actual
`TraceOneInt 1` unit back through the ring equivalence, applies the existing
`goldenUnitClassesModFifth`, and transports the resulting fifth-power equation
back.  The unit predicate is the existing
`goldenUnit_iff_isUnit`, so the explicit system has one coherent unit API.

The same file adds the representative compatibility theorem
`goldenTraceOneFifthUnitPowerSectorSystem_rep_apply` and
`classGroupPTorsionFreeAt_traceOneOne_five`.  The latter is discharged
structurally: `RingEquiv.euclideanDomain` transports the existing golden
Euclidean-domain instance, after which the existing principal-ideal bridge
gives the class-group condition.  The transported Euclidean and domain
instances are theorem-local; no global instance diamond is introduced.

Finally,
`exists_goldenSector_mul_fifth_of_primeTraceOneStrippedIdealPacket_five`
composes the generic
`exists_sector_mul_pow_of_primeTraceOneStrippedIdealPacket` theorem with the
explicit p=5 system and the structural class-group proof.  The dependent
carrier is handled by the newly added neutral normalization theorem
`signedPrimeParameter_five : signedPrimeParameter 5 = 1` in
`DkMath/NumberTheory/PrimeQuadraticDiscriminant.lean` and a local carrier
transport.  This is only a normalization/transport lemma, not a new arithmetic
claim.

## API and boundary audit

The implementation uses the existing Lean 4.34 APIs
`RingEquiv.euclideanDomain`, `EuclideanDomain.instIsPrincipalIdealRing`,
`EuclideanDomain.instIsDomain`, `MulEquiv.isDomain`, `Units.map`,
`Units.coe_map`, `IsUnit.mul_iff`, and `isUnit_pow_iff`.  An initial probe
confirmed that `RingEquiv` has no `map_one'` structure field in this toolchain;
the inherited map-one law is used instead.

The generic real branch remains the existing
`traceOnePrimeRealFinSectorSystem`, whose type is
`UnitPowerSectorSystem (TraceOneInt (signedPrimeParameter p)) p`.  This report
only audits its p=5 carrier normalization and does not assert an equality or
reindexing with the explicit golden `Fin 5` system.  The specialized
`SignedGoldenSectorArithmetic` zero-sector/descent APIs are not imported or
invoked by the production endpoint; the packet-to-golden residual correspondence
needed for a later specialized argument remains outside this checkpoint.

## Audits and validation

The following focused builds passed:

```text
lake build DkMath.FLT.Five.TraceOneBridge
lake build DkMath.FLT.Five.GoldenEuclidean
lake build DkMath.FLT.Five.GoldenUnitClassification
lake build DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
lake build DkMath.FLT.Prime.PrimeTraceOneFiveSectorClosure
lake build DkMathTest.FLT.Prime.PrimeTraceOneFiveSectorClosureApiAudit
lake build DkMathTest.FLT.Prime.PrimeTraceOneFiveSectorClosureAxiomAudit
```

The API audit checks the public declarations, inherited algebraic operations,
the p=5 representative equations, and the generic endpoint.  The axiom audit
reports only standard Lean/Mathlib dependencies:

```text
goldenTraceOneRingEquiv: [propext]
goldenTraceOneRingEquiv_map_goldenNorm: [propext, Quot.sound]
goldenTraceOneFifthUnitPowerSectorSystem_complete: [propext, Classical.choice, Quot.sound]
classGroupPTorsionFreeAt_traceOneOne_five: [propext, Classical.choice, Quot.sound]
exists_goldenSector_mul_fifth_of_primeTraceOneStrippedIdealPacket_five:
  [propext, Classical.choice, Quot.sound]
```

No project-specific axiom, `sorry`, `admit`, or `unsafe` declaration was added
in the production implementation.  `git diff --check` and the corresponding
no-index checks for new files are part of the closeout audit.  The only reported
build diagnostics are existing dependency linter warnings plus two harmless
theorem-local instance-style warnings in the p=5 endpoint.

## Non-goals preserved

This checkpoint establishes a generic structural sector closure statement only.
It does not claim prime existence, Goldbach, a uniform provider, global class
number information beyond the transported PID fact, sector elimination, or the
final FLT5 theorem.
