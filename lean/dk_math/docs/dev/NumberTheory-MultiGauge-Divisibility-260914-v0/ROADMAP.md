# Multi-Gauge Divisibility Roadmap 260914 v0

cid: `6aa763a7-1a14-83e8-9041-1029d978663c`

## Campaign objective

Establish a generic arithmetic theory describing how prime visibility changes when the DkMath unit gauge changes.

The central question is:

```text
q escapes in gauge u₁
-> does q escape in gauge u₂?
-> if not, which scale/transition factor introduced q?
-> along a finite chain, where is first capture possible?
```

The v0 branch intentionally stops before Norm / Eisenstein / TraceOne lattice landing.

---

## Phase MG-000 — two-stage arithmetic kernel

Status: COMPLETE / APPROVED

Production:

```text
DkMath/NumberTheory/MultiGauge/Basic.lean
DkMath/NumberTheory/MultiGauge/PrimeTransport.lean
DkMath/NumberTheory/MultiGauge.lean
```

Core objects:

```text
GNGaugeStage
GNGaugeStage.gnValue
GNGaugeStage.value
PrimeCaught
PrimeEscapes
GNGaugeTransition
```

Transition law:

$$
A_2\delta=A_1\nu.
$$

Production theorem family includes both-direction prime transport, visibility equivalence outside transition support, boundary/GN channel decomposition, and common-channel localization into the exponent.

See:

```text
report-000.md
review-000.md
```

---

## Phase MG-001 — finite prime-escape paths

Status: COMPLETE / APPROVED

Production:

```text
DkMath/NumberTheory/MultiGauge/Path.lean
```

Implemented:

```text
GNGaugePath
Linked
endStage
stages
numeratorProduct
denominatorProduct
```

Exact path balance:

```text
endStage.value * denominatorProduct
=
start.value * numeratorProduct.
```

Prime-escape path theorems include endpoint support localization, all-stage escape under numerator avoidance, visibility equivalence outside total path support, and an actual escape-to-capture transition witness whose numerator contains the newly captured prime.

See:

```text
instruction-001.md
report-001.md
review-001.md
```

---

## Phase MG-L2 — Legendre degree-two bridge / audit

Status: COMPLETE / APPROVED — Outcome B: CHANNEL BRIDGE ONLY

Production:

```text
DkMath/NumberTheory/Legendre/MultiGaugeBridge.lean
```

The exact production orientation is:

```text
GTail 2 1 1 n = 2*n + 1.
```

The canonical reversed degree-two stage has:

```text
x = 1
u = n
value = gnValue = 2*n+1.
```

Production now packages:

```text
fresh tied successor-pair delay
-> PrimeCaught q (successorIncrementGaugeStage n);

PrimeEscapes q (successorIncrementGaugeStage n)
-> tied successor pair persists.
```

The audit found no non-tautological `GNGaugeTransition 2` from current Legendre/primorial semantics. The untied case gained no localization beyond existing single-seat divisibility, and the Legendre global square-shell frontier did not advance.

This is an informative boundary, not a failed implementation.

See:

```text
instruction-002.md
report-002.md
review-002.md
```

---

## Phase MG-002 — exact channel path states

Status: DEFERRED / CONDITIONAL

Candidate states remain:

```text
escape
boundary-only
gn-only
```

for primes away from the exponent support.

There is still no concrete primitive-shape transition provider. Building an automaton now would remain mostly descriptive.

Resume MG-002 only after concrete primitive-shape transition semantics make channel-switch pruning mathematically useful.

---

## Phase MG-003A — raw/primitive gauge normalization and synchronized refinement

Status: COMPLETE / APPROVED — Outcome A

Production:

```text
DkMath/NumberTheory/MultiGauge/RawNormalization.lean
DkMath/NumberTheory/PrimorialUniverse/MultiGaugeUnitRefinementBridge.lean
```

The missing abstraction boundary is now explicit:

```text
raw pair
=
common gcd/scale
×
primitive coprime stage.
```

Production proves:

```text
(scaleBy k s).value = k^d * s.value;

s.value = s.scale^d * (s.primitiveStage hg).value;

RawPrimeCaught q s
<->
q | s.scale OR PrimeCaught q (s.primitiveStage hg);

RawPrimeEscapes q s
RawPrimeCaught q (scaleBy k s)
->
q | k.
```

The downstream PUU bridge proves that an actual `UnitRefinesBy` coordinate change sends the two natural coordinates to the same generic `scaleBy k` raw stage.

This is the first non-tautological concrete gauge-refinement transport of the campaign.

See:

```text
instruction-003.md
report-003.md
review-003.md
```

---

## Phase MG-003B — finite raw-refinement paths and primitive-shape invariance

Status: COMPLETE / APPROVED — Outcome A

Production:

```text
DkMath/NumberTheory/MultiGauge/RawRefinementPath.lean
```

Positive synchronized scaling now satisfies:

```text
scale (scaleBy k s) = k * scale s;
primitiveStage (scaleBy k s) = primitiveStage s.
```

For a finite positive factor list, production proves:

```text
endStage = scaleBy cumulativeFactor start;

endStage.value
=
cumulativeFactor^d * start.value;

start escape
+ every listed factor avoids q
-> every visited raw stage escapes q;

start escape
+ capture at some visited raw stage
-> some actual listed factor is divisible by q.
```

This completes the common-scale answer to the original MultiGauge question for finite synchronized unit-refinement chains.

API note: the current escape-to-capture witness proves the arithmetic step and factor localization, but its exported type does not separately encode a list-indexed adjacency certificate. Add one only if a downstream theorem needs order/uniqueness.

---

## Phase MG-003C — primitive-shape transition provider audit

Status: COMPLETE / AUDITED — Outcome B: NO UNCONDITIONAL PRIMITIVE PROVIDER FOUND

The mandatory FLT q-adic/GN reduced-gap, FLT3, FLT5/golden,
Petal/StructuralArithmetic, and ABC/complement candidate families were
audited.  The q-adic route has a conditional/open shape suggesting
`old.value = q^p * new.value`, but its integer local-to-global input is an
open target and no pair of coprime `GNGaugeStage`s is packaged.  The other
families provide different-carrier descent, one-stage GN support identities,
or factor/complement relations rather than the required same-observer balance.

No decorative transition wrapper was added.  MG-003A/B remains
`COMMON-SCALE-ONLY`; it does not count as primitive shape change.

See:

```text
instruction-005.md
report-005.md
```

See:

```text
instruction-004.md
report-004.md
review-004.md
```

---

## Phase MG-004 — Norm / lattice landing

Status: OUT OF CURRENT FRONT-HALF SCOPE

Resume the second half of:

```text
docs/not_implements/260912-MultiGauge-Divisibility-Norm-Lattice-Landing.md
```

only after raw scale transport and concrete primitive-shape transition semantics are stable, or after MG-003C explicitly records that no current primitive provider exists.

Intended later chain:

```text
GN gcd sieve
-> raw gauge normalization / scale support
-> raw refinement path transport
-> primitive gauge transition / path admissibility
-> Norm divisibility
-> coordinate divisibility
-> integer-lattice landing
-> power/Core-image landing
```

---

## Architectural invariants

```text
1. Existing one-stage gcd facts are dependencies, not targets for re-proof.
2. Generic MultiGauge code remains independent of ABC, FLT, and Legendre.
3. Raw common scale and primitive coprime shape are distinct layers.
4. Synchronized common scaling preserves primitive shape.
5. Transition support is explicit: numerator injects possible new primitive support; denominator removes possible old primitive support.
6. Common-scale refinement localizes new raw support to the independent scale factor.
7. Application bridges must not manufacture tautological transitions and call them pruning.
8. Conditional/open descent targets are not unconditional providers.
9. MG-002 state machinery is introduced only when it proves genuine pruning.
10. No Norm/lattice abstraction is introduced merely because it belongs to the long-term plan.
11. No sorry/admit/new axiom declarations.
```

---

## Immediate execution order

```text
MG-000
  COMPLETE / APPROVED

MG-001
  COMPLETE / APPROVED

MG-L2
  COMPLETE / APPROVED
  Outcome B — CHANNEL BRIDGE ONLY

MG-003A
  COMPLETE / APPROVED
  Outcome A — RAW NORMALIZATION AND UNIT-REFINEMENT TRANSPORT ESTABLISHED

MG-003B
  COMPLETE / APPROVED
  Outcome A — FINITE RAW-REFINEMENT PATHS AND PRIMITIVE-SHAPE INVARIANCE

instruction-005
  COMPLETE / AUDITED
  Outcome B — NO UNCONDITIONAL PRIMITIVE PROVIDER FOUND

report-005
  conditional/open q-adic and wrong-observer candidates recorded;
  no application bridge or MG-002 automaton is justified by the current source.
```
