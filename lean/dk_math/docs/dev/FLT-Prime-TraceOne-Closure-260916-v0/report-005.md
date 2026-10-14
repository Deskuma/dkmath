# FPTC-005 report — p=3 generic TraceOne/Eisenstein sector closure

## Outcome

```text
Outcome A — GENERIC P=3 EISENSTEIN SECTOR CLOSURE GREEN
```

The existing FLT3/Eisenstein sector system is now composed with the branch-
independent generic prime endpoint at `p = 3`.  The carrier alignment is
definitionally `EisensteinInt = TraceOneInt (-1)`, and the existing theorem
`signedPrimeParameter_three` supplies the parameter normalization.

No FLT3 re-proof, duplicate carrier equivalence, new unit-sector system,
coordinate contradiction, or general FLT theorem was implemented.

## Repository and scope audit

Work was performed on
`research/FLT-Prime-TraceOne-Closure-260916-v0`.  The attached instruction was
treated as the bounded implementation contract, separate from the user's
request.  The specified FLT3 substrate, Euclidean, unit-sector, bridge,
generic conditional endpoint, class-group bridge, and unit-power APIs were
read before editing.

The import direction for the new production module is:

```text
DkMath.FLT.Three.EisensteinLibBridge
        ↓
DkMath.FLT.Prime.PrimeTraceOneThreeSectorClosure
        ↓
DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
```

The new module imports no completed FLT3 contradiction theorem and does not
modify the existing neutral or FLT3 carrier infrastructure.

## Exact API evidence

The focused audit is
`DkMathTest/FLT/Prime/PrimeTraceOneThreeSectorClosureApiAudit.lean`.  The
current declarations confirmed by `#check` and synthesis are:

```text
DkMath.FLT.Three.EisensteinInt := TraceOneInt (-1)

DkMath.FLT.Three.traceOneInt_signedPrimeParameter_three_type :
  TraceOneInt (signedPrimeParameter 3) = TraceOneInt (-1)

DkMath.NumberTheory.PrimeQuadraticDiscriminant.signedPrimeParameter_three :
  signedPrimeParameter 3 = -1

EuclideanDomain (TraceOneInt (-1))
IsPrincipalIdealRing (TraceOneInt (-1))

DkMath.FLT.Three.eisensteinCubeUnitPowerSectorSystem :
  UnitPowerSectorSystem (TraceOneInt (-1)) 3

DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt_of_isPrincipalIdealRing

DkMath.FLT.Prime.exists_sector_mul_pow_of_primeTraceOneStrippedIdealPacket
```

The local regressions establish that `EisensteinInt` is definitionally the
same carrier, the signed parameter computes to `-1`, Euclidean/PID structure
is synthesized, the class-group condition follows structurally, and the
existing sector system has the exact generic type required by the prime
endpoint.

No carrier equivalence or theorem-level cast was necessary beyond the
existing `signedPrimeParameter_three` normalization in the final specialization.

## Implemented production API

The new module is
`DkMath/FLT/Prime/PrimeTraceOneThreeSectorClosure.lean`.

The structural class-group theorem is:

```lean
theorem classGroupPTorsionFreeAt_traceOneNegOne_three :
    classGroupPTorsionFreeAt (TraceOneInt (-1)) 3
```

It is exactly the neutral principal-ideal bridge applied to the existing
Euclidean-domain instance:

```text
EuclideanDomain (TraceOneInt (-1))
  -> IsPrincipalIdealRing (TraceOneInt (-1))
  -> classGroupPTorsionFreeAt (TraceOneInt (-1)) 3
```

The main p=3 endpoint is:

```lean
theorem exists_eisensteinSector_mul_cube_of_primeTraceOneStrippedIdealPacket_three
    (... P0 P Q) :
    ∃ sector : EisensteinUnitSector, ∃ delta : EisensteinInt,
      Q.residual =
        (eisensteinCubeUnitPowerSectorSystem.rep sector : EisensteinInt) *
          delta ^ 3
```

Its proof calls the existing generic theorem
`exists_sector_mul_pow_of_primeTraceOneStrippedIdealPacket`, supplies
`eisensteinCubeUnitPowerSectorSystem`, discharges `3 ≠ 2` by `norm_num`, and
supplies the structural class-group theorem.  The final equality is normalized
with `signedPrimeParameter_three`.

Status:

```text
FPTC-P3-CLASSGROUP-DISCHARGED-GREEN
FPTC-P3-GENERIC-SECTOR-CLOSURE-GREEN
```

## Next coordinate-consumer boundary audit

The natural next use of `traceOne_pow_core_landing_iff` would set

```text
alpha = Q.residual
beta  = Eisenstein representative
r     = 3
```

This was not added to production.  The existing sector representatives are
units, so their norm is nonzero immediately from unit status; however, the
current FLT3 sector API does not expose a dedicated uniform theorem that every
representative has TraceOne norm exactly `1` at the generic receiver boundary.
Moreover, the sector endpoint already provides the relevant factorization, so
the coordinate receiver would not add a contradiction without a further
arithmetic argument.  Deferring it preserves the instruction's required
Outcome A and avoids duplicating Eisenstein arithmetic.

## Failed probes and adapter decision

The initial theorem-shape probe used the generic output carrier directly in a
normalized `EisensteinInt` conclusion.  Lean required the equality to be
elaborated first at `TraceOneInt (signedPrimeParameter 3)`; the final proof
therefore retains the generic equality in a typed `show` and then applies
`simpa [signedPrimeParameter, signedPrimeDiscriminant]`.

No second carrier equivalence, coordinate conversion, or unit-sector system
was introduced.  The existing `EisensteinLibBridge` was sufficient.

## Axiom audit

The focused audit is
`DkMathTest/FLT/Prime/PrimeTraceOneThreeSectorClosureAxiomAudit.lean`.
The expected output is:

```text
classGroupPTorsionFreeAt_traceOneNegOne_three depends on axioms:
[propext, Classical.choice, Quot.sound]

exists_eisensteinSector_mul_cube_of_primeTraceOneStrippedIdealPacket_three
depends on axioms:
[propext, Classical.choice, Quot.sound]
```

No DkMath-defined axiom, `sorry`, `sorryAx`, `admit`, or `unsafe` declaration
was added.

## Validation

The required focused builds are:

```text
lake build DkMath.FLT.Three.EisensteinLibBridge
lake build DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
lake build DkMath.FLT.Prime.PrimeTraceOneThreeSectorClosure
lake build DkMathTest.FLT.Prime.PrimeTraceOneThreeSectorClosureApiAudit
lake build DkMathTest.FLT.Prime.PrimeTraceOneThreeSectorClosureAxiomAudit
```

The report is completed after all listed builds pass, `git diff --check` and
no-index whitespace checks produce no diagnostics, and the repository-standard
forbidden-source scan finds no forbidden declaration in the new Lean files.

## Explicit boundary and next frontier

The reusable result now available is:

```text
p=3 PrimeTraceOne stripped ideal packet
  -> existing generic principalization/sector endpoint
  -> existing Eisenstein cube unit sector
  -> explicit Eisenstein sector × cube factorization
```

This checkpoint does not prove the FLT3 contradiction, eliminate any sector,
derive a coordinate obstruction, add p=5 integration, route a generic FLT
counterexample, or claim general FLT.
