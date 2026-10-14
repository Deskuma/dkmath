# FLT7TC-005R9 — Direct second-case cyclotomic launchpad and μ₇-unit phase frontier

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-014.md` was treated as the bounded implementation
contract, separately from the user's request.  This checkpoint constructs the
direct degree-six factor from the existing
`PrimitiveCounterexampleRamifiedProvenance`.  It does not construct a second
summit, enter the historical signed-root routing packet as a bypass, or claim
FLT7.

## Direct factor and concrete norm

The focused audit module
`DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicSecondCaseAudit` defines
`directLinearFactor r` using the same stored summit:

```text
η = ofReal (endpointLeft) - ζ * ofReal (endpointRight).
```

The thin packet
`PrimitiveCounterexampleDirectCyclotomicSecondCasePacket.ofProvenance` retains
the source-indexed provenance and exact factor equality.  The direct relative
norm is expanded as

```text
L² - (α - 1) L R + R²
```

and the full concrete norm is its `SevenRealCubicInt.norm`.  The kernel-checked
theorem `directCyclotomicNorm_eq_cyclotomicSeven` identifies it with the
classical seventh cyclotomic kernel.  Thus the answer to question 1 is **yes**:

```text
directCyclotomicNorm η = 7 * residualRoot^7.
```

The implementation also proves the division-free identities

```text
(L - R) * directCyclotomicNorm η = L^7 - R^7
(L - R) * directCyclotomicNorm η = distinguished^7.
```

## Ideal and PID frontier

The answer to question 2 is **no**.  No direct proof was found for

```text
Ideal.span {η} = ramifiedPrime * I^7.
```

The norm identity is deliberately not promoted to ideal-exponent ownership.
Consequently question 3 is **not applicable**: no new PID element equation was
derived.  Question 4 remains the precise missing step: the ramified-prime
valuation and all nonramified ideal exponents of the actual `η` must still be
proved from the current provenance.

Because no concrete associated load/unit was produced, the answer to question
5 is **not yet**: there is no honest reduction to a pure `μ₇` phase.  Question
6 is likewise **not yet**: no phase-selection congruence was asserted.

## TraceOne comparison and axioms

Question 7: **no checked implication or equivalence** between this direct norm
launchpad and `CubicGapSeventhShapeReceiver` was found.  The current result is
therefore a source-level direct norm surface, not a receiver normalization.

Question 8: **no `sorryAx` occurs in the decisive new theorem surfaces**.  The
focused axiom audit reports only ordinary foundations (`propext`,
`Classical.choice`, and/or `Quot.sound`) for:

- `directLinearFactor_mul_star`;
- `directCyclotomicNorm_eq_cyclotomicSeven`;
- `directLinearFactor_norm_product_identity`;
- `directLinearFactor_norm_product_eq_distinguished_pow`;
- `directCyclotomicNorm_eq_seven_mul_residual_pow`.

The public `DkMath.FLT.Seven` facade was not extended, because the ideal packet
and phase normalization are not established.

## Outcome

**Outcome C — DIRECT NORM GREEN; IDEAL RAMIFIED-LOAD OWNERSHIP IS THE PRECISE
FRONTIER.**

The remaining target is the direct ideal identity for the actual linear factor,
followed only then by PID extraction and a concrete associated-unit/μ₇ phase
audit.  No unconditional FLT7 conclusion follows from this checkpoint.

## Validation

The following focused builds completed successfully:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicSecondCaseAudit
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicSecondCaseAuditApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicSecondCaseAuditAxiom
```

The new production and audit sources contain no `sorry`, `admit`, `unsafe`, or
project `axiom` declarations.  No speculative facade export was added.
