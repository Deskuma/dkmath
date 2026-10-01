# FLT7TC-005R10 — Direct cyclotomic ideal ownership from the six-phase orbit

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This checkpoint starts from the checked R9 source-level launchpad:

```text
PrimitiveCounterexampleRamifiedProvenance
  -> eta = L - zeta R
  -> N(eta) = 7 * residualRoot^7
```

The task is to lift this exact source-level norm statement to the direct ideal statement

```text
Ideal.span {eta} = ramifiedPrime * I^7
```

for some ideal `I` of `SevenCyclotomicDegreeSixInt.Ring`, without passing through
`RamifiedSignedRootRoutingPacket`, the historical receiver, or any theorem containing
`sorryAx`.

Do not attempt the final `mu_7` unit normalization until the ideal packet is actually
kernel-checked.

## 1. Read first

Read at least:

- `PrimeTraceOneDirectCyclotomicSecondCaseAudit.lean`
- `PrimeTraceOnePrimitiveRamifiedProvenance.lean`
- `SevenRamifiedFusionCyclotomicDegreeSixCarrier.lean`
- `SevenRamifiedFusionCyclotomicConjugatePrimePair.lean`
- `SevenRamifiedFusionCyclotomicRamifiedPrime.lean`
- `SevenRamifiedFusionGlobalOrientedPrimeFactorization.lean`
- `SevenRamifiedFusionOrientedCarrierValuationOwnership.lean`
- `SevenRamifiedFusionCyclotomicDegreeSixNorm.lean` or the module defining `sixPhaseProduct` / `cyclotomicNormHom`
- the generic Dedekind/copime-power extraction lemmas in `DkMath.FLT.Kummer.CyclotomicPrincipalization`

Reuse small generic lemmas where honest. Do not reuse a historical theorem whose input already
contains `RamifiedSignedRootRoutingPacket` merely to manufacture the desired direct packet.

## 2. Preferred new module

Create a focused module such as

```text
DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicIdealOwnership.lean
```

Keep the previous R9 audit module unchanged except for imports if necessary.

## 3. First mandatory result: exact ramified-prime multiplicity one

For the actual direct factor

```text
eta = ofReal L - zeta * ofReal R
```

prove directly from current provenance:

```text
eta ∈ ramifiedPrime
eta ∉ ramifiedPrime^2
```

Prefer a shallow generalization of the checked historical proof
`cyclotomicDegreeSixCarrier_not_mem_ramifiedPrime_sq`.

The intended arithmetic is:

```text
eta = (L - R) + (1 - zeta) * R
```

and the summit gives a very high `7`-divisibility of `L-R`, while
`endpointRight_not_seven_dvd` gives `R != 0 mod 7`.

It is acceptable to define a direct ramified tail / quotient analogous to the historical
one, but it must depend only on the current summit/provenance. The quotient after extracting
one `ramifiedUniformizer` should reduce to `R` under `ramifiedEval`, proving that no second
uniformizer divides it.

Do not infer exact multiplicity one from the integer norm alone.

## 4. Six Galois phases

Use the existing order-three rotation and quadratic star on
`SevenCyclotomicDegreeSixInt.Ring` to package the six conjugate phases of `eta`.

Prefer reusing the existing `sixPhaseProduct` machinery for arbitrary elements rather than
reimplementing a six-term polynomial expansion.

Prove the direct specialization conceptually equivalent to

```text
sixPhaseProduct eta = ofReal (7 * residualRoot^7).
```

Every phase should have the same exact ramified-prime multiplicity one, by transport through
the ring automorphisms (or by a common direct theorem).

## 5. Strip the common ramified prime

Construct six direct stripped factors/ideals after removing exactly one copy of
`ramifiedPrime` from each phase.

A preferred element-level shape is

```text
phase_i eta = ramifiedUniformizer * stripped_i
```

with

```text
stripped_i ∉ ramifiedPrime.
```

Then set

```text
J_i := Ideal.span {stripped_i}.
```

Avoid ideal quotient/division unless it materially simplifies the proof; the explicit
uniformizer quotient is preferred because the prime is principal and exact multiplicity one
is already known.

Use the existing identity expressing integer `7` as a unit times
`ramifiedUniformizer^6` to prove the stripped product ideal identity

```text
prod_i J_i = Ideal.span {(residualRoot : Ring)} ^ 7
```

or an exactly equivalent principal-ideal statement.

Do not cancel a nonzero ideal by an unsupported algebraic simplification; use existing
cancellation/invertibility APIs or cancel the nonzero uniformizer at element level first.

## 6. Pairwise coprimality of stripped phase ideals

This is the decisive nonramified ownership step.

Prove that distinct stripped phase ideals are pairwise coprime.

The intended classical argument is:

- a prime ideal common to two distinct cyclotomic linear factors divides their difference;
- the difference is a root-of-unity difference times the endpoint `R`;
- a prime dividing a root-of-unity difference lies over `7`;
- endpoint coprimality excludes a nonramified common prime coming from `R`;
- after stripping the unique `ramifiedPrime`, no common prime remains.

Reuse the generic Kummer common-prime / `zeta-1` lemmas if they specialize cleanly to the
concrete carrier. Otherwise prove the smallest concrete degree-six version.

Do not assume that distinct principal factors are automatically coprime.
Do not infer pairwise coprimality from the product norm.

## 7. Seventh-power ideal extraction

Once the stripped family is pairwise coprime and its product is a seventh power ideal, use
the existing generic Dedekind theorem for pairwise-coprime power extraction.

For the original oriented phase, derive

```text
∃ I : Ideal SevenCyclotomicDegreeSixInt.Ring,
  Ideal.span {directLinearFactor r} =
    SevenCyclotomicDegreeSixInt.ramifiedPrime * I^7
```

Name the packet/theorem so the source `PrimitiveCounterexampleRamifiedProvenance` and same
summit remain visible.

If convenient, package:

```lean
structure PrimitiveCounterexampleDirectCyclotomicIdealPacket ... where
  rootIdeal : Ideal Ring
  span_linearFactor_eq :
    Ideal.span {directLinearFactor r} = ramifiedPrime * rootIdeal ^ 7
```

Do not erase the source provenance.

## 8. Optional PID calibration only after §7

Only if §7 is green, use the concrete PID to obtain the exact element-level consequence.
A safe target is

```text
eta = loadElement * beta^7
span {loadElement} = ramifiedPrime
```

or equivalently

```text
eta = unit * ramifiedUniformizer * beta^7.
```

Retain the associated unit explicitly.

Do **not** claim the unit is a seventh power.
Do **not** attempt to choose a `mu_7` phase unless a new checked theorem justifies it.
The next checkpoint may audit that phase.

## 9. Compare with the current TraceOne receiver

Report whether the new direct ideal packet:

1. is genuinely upstream of `CubicGapSeventhShapeReceiver`;
2. implies that receiver;
3. is implied by that receiver;
4. or remains logically independent on the checked API surface.

Do not infer equivalence merely because both eventually produce seventh-power data.

## 10. Report

Create `report-015.md` answering explicitly:

1. Is `eta` proved to have exact ramified-prime multiplicity one?
2. Is the six-phase product specialized to `7 * residualRoot^7`?
3. Are six stripped factors/ideals constructed?
4. Is their product a seventh-power principal ideal?
5. Is pairwise coprimality of the stripped ideals proved?
6. Does the direct ideal identity `span {eta} = ramifiedPrime * I^7` follow?
7. If yes, what exact PID element equation follows and what unit remains?
8. Is any implication/equivalence with the TraceOne cubic receiver proved?
9. Are all decisive new theorems free of `sorryAx`?

Update this campaign ROADMAP with the exact result.

## 11. Audits

Add focused API and axiom audits. Axiom output for decisive new theorems should be limited to
ordinary foundations already accepted in this campaign (`propext`, `Classical.choice`,
`Quot.sound`, as applicable).

Run at least:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicIdealOwnership
lake build DkMath.FLT.Seven
lake build <new API audit>
lake build <new axiom audit>
git diff --check
```

Scan new source for `sorry`, `admit`, `unsafe`, and project `axiom` declarations.

## 12. Outcome labels

Use exactly one:

```text
Outcome A — DIRECT IDEAL OWNERSHIP GREEN; PID ELEMENT PACKET GREEN; ONLY MU_7 UNIT PHASE REMAINS
```

```text
Outcome B — DIRECT IDEAL OWNERSHIP GREEN; ELEMENT/PID UNIT PACKAGING REMAINS THE NEXT FRONTIER
```

```text
Outcome C — EXACT RAMIFIED MULTIPLICITY / SIX-PHASE STRIPPING GREEN; PAIRWISE NONRAMIFIED COPRIMALITY IS THE PRECISE FRONTIER
```

```text
Outcome D — DIRECT NORM REMAINS GREEN, BUT ONE EARLIER IDEAL/GALOIS BRIDGE IS STILL MISSING
```

## 13. Hard stop rules

Stop rather than force a stronger claim if any of the following would be required:

- integer norm equality -> ideal seventh-power ownership without prime-ideal analysis;
- `eta ∈ ramifiedPrime` -> exact multiplicity one without excluding `ramifiedPrime^2`;
- product of stripped ideals being a seventh power -> each factor seventh power without
  pairwise coprimality;
- PID principality -> associated unit is a seventh power;
- arbitrary degree-six unit -> `zeta^j * seventh power` without a checked unit-class theorem;
- historical routed packet imported downstream of the current receiver to manufacture the
  direct ideal packet;
- any `sorryAx`-bearing Kummer/default theorem;
- any claim of FLT7 closure before a contradiction from the original primitive counterexample
  is kernel-checked.
