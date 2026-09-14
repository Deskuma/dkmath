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

However, after MG-L2 no concrete primitive-shape transition provider is available. Building an automaton now would be mostly descriptive.

Resume MG-002 only after concrete transition semantics make channel-switch pruning mathematically useful.

---

## Phase MG-003A — raw/primitive gauge normalization and synchronized refinement

Status: NEXT

The MG-L2 audit exposed the missing abstraction boundary.

`GNGaugeStage` is already primitive/coprime:

```text
Coprime x u.
```

But concrete unit refinement in PrimorialUniverse transports raw natural coordinates by common scaling:

```text
(x,u) -> (x*k,u*k).
```

For `k > 1`, the refined pair is generally not coprime and therefore does not directly inhabit `GNGaugeStage`.

The new layer is:

```text
raw pair
=
common gcd/scale
×
primitive coprime stage.
```

Targets:

```text
GNRawGaugeStage;
raw observer homogeneity A_d(kx,ku)=k^d*A_d(x,u);
gcd/common-scale extraction;
primitiveStage normalization;
rawValue = scale^d * primitiveValue;
prime capture iff scale support OR primitive-stage support;
raw escape + refined capture -> q | refinement factor k;
bridge to PrimorialUniverse.UnitCoordinateRefinement.
```

Important architecture:

```text
common-scale refinement
!=
primitive-shape GNGaugeTransition.
```

Do not weaken the existing coprimality invariant to force these layers together.

See:

```text
instruction-003.md
```

---

## Phase MG-003B — concrete primitive-shape transition providers

Status: PLANNED AFTER MG-003A

After raw/common-scale support is separated, re-audit candidate genuine primitive-stage transitions:

```text
explicit quotient/normalization packets;
Petal / primitive-boundary transitions;
FLT or ABC descent packets;
other arithmetic coordinate changes not equal to common scaling.
```

A provider must derive the `GNGaugeTransition` balance from independent semantics. Endpoint-copy constructions remain excluded.

`FixedBigGauge` real-valued refinement may provide semantic context, but it does not by itself supply a natural-number primitive-stage balance.

---

## Phase MG-004 — Norm / lattice landing

Status: OUT OF CURRENT FRONT-HALF SCOPE

Resume the second half of:

```text
docs/not_implements/260912-MultiGauge-Divisibility-Norm-Lattice-Landing.md
```

only after raw scale transport and concrete primitive-shape transition semantics are stable.

Intended later chain:

```text
GN gcd sieve
-> raw gauge normalization / scale support
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
4. Transition support is explicit: numerator injects possible new primitive support; denominator removes possible old primitive support.
5. Common-scale refinement localizes new raw support to the independent scale factor.
6. Application bridges must not manufacture tautological transitions and call them pruning.
7. MG-002 state machinery is introduced only when it proves genuine pruning.
8. No Norm/lattice abstraction is introduced merely because it belongs to the long-term plan.
9. No sorry/admit/new axiom declarations.
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

instruction-003
  NEXT
  raw stage
  common-scale homogeneity
  gcd primitive normalization
  exact raw support decomposition
  synchronized unit-refinement capture localization

report-003 + review
  decide whether raw/common-scale transport is established,
  then re-open genuine primitive-shape transition providers.
```
