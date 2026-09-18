# FLT7TC-005R15 — Explicit CM conjugation transport and torsion phase kill

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-020.md` was used as the bounded implementation
contract, separately from the user's request. The implementation stays on the
explicit CM API path and does not add a `Star` instance to the abstract ring of
integers.

## Implementation

The new production module is
`DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicCMTorsionPhase.lean`.
Because the exact-power result is now unconditional and stable, this module
is also exported by the `DkMath.FLT.Seven` facade.

Part A is checked through the existing
`ringOfIntegersToRingEquiv`. The chosen cyclotomic generator is transported by
Mathlib's explicit `ringOfIntegersComplexConj`, both maps are compared on the
integral power-basis generator, and the concrete result is

```text
E (ringOfIntegersComplexConj K x) = star (E x).
```

The unit-level coherence

```text
E_units (unitsComplexConj K U) = starUnit (E_units U)
```

is also proved. The abstract seventh-cyclotomic torsion order is checked as
`NumberField.Units.torsionOrder K = 14`.

For an arbitrary concrete unit of quadratic norm one, the CM transport gives
the inverse conjugation relation and proves `delta ^ 28 = 1`. The actual R13
phase has the stronger checked identity
`(delta / starUnit delta) ^ 14 = 1`.

Part C is proved independently of FLT provenance. From a full `(7)`
congruence, the proof writes `delta = 1 + 7*a`, obtains the geometric sum
vanishing from `delta ^ 28 = 1`, and linearizes powers modulo the principal
ideal `(49)`. The sum is congruent to `28` modulo `(49)`, while the explicit
first coordinate of the carrier excludes `28 ∈ (49)`. This proves

```lean
unit_eq_one_of_pow_twentyEight_eq_one_of_sub_one_mem_sevenIdeal
```

without enumerating roots of unity.

Part D is now unconditional. The existing R13 conditional 2/7 Bézout
arguments are reused to provide:

- `RelativeNormOneScalarUnitAtSeven`;
- the actual associated unit as a seventh power;
- `directCyclotomicPhaseQuotient r 1 = gamma ^ 7`;
- `directLinearFactor r = ramifiedUniformizer * gamma ^ 7`.

## Downstream audit

The clean FLT7 source was searched after the exact direct-factor equation was
made unconditional. Existing consumers establish orbit, ideal-ownership, and
norm identities, but no receiver-free theorem consumes the exact equation to
produce a primitive contradiction. The first missing result is therefore an
explicit clean bridge from

```text
directLinearFactor r = ramifiedUniformizer * gamma ^ 7
```

to the primitive FLT7 contradiction. The historical
`CubicGapSeventhShapeReceiver` route was not used, and no circular specialized
contradiction theorem was introduced.

## Outcome

**Outcome A — CM TORSION PHASE KILLED; DIRECT CHOSEN QUOTIENT EXACT SEVENTH POWER GREEN.**

This checkpoint does not claim a clean downstream contradiction or an
unconditional public FLT7 theorem.

## Validation

The focused production, facade, API, and axiom builds were run:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicCMTorsionPhase
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicCMUnitPhase
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicCMTorsionPhaseApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicCMTorsionPhaseAxiom
```

The decisive theorem axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. The implementation and audit
sources contain no `sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom`.
