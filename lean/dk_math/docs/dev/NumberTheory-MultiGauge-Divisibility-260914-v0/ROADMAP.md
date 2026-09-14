# Multi-Gauge Divisibility Roadmap 260914 v0

cid: `6aa763a7-1a14-83e8-9041-1029d978663c`

## Campaign objective

Establish a generic arithmetic theory describing how prime visibility changes when the DkMath unit gauge changes.

The central question is:

```text
q escapes in gauge u₁
-> does q escape in gauge u₂?
-> if not, which transition factor introduced q?
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

Prime-escape path theorems now include:

```text
endpoint support localization;
all-stage escape under numerator avoidance;
start/end visibility iff outside total transition support;
escape -> capture transition witness with q | numerator;
start escape + end capture -> q | numeratorProduct;
start capture + end escape -> q | denominatorProduct.
```

The implementation uses a simple recursive `List` path and requires no automaton layer.

See:

```text
instruction-001.md
report-001.md
review-001.md
```

---

## Phase MG-L2 — Legendre degree-two bridge / audit

Status: NEXT

This is the first major downstream audit before any quadratic-order work.

Keep the bridge outside the generic MultiGauge core.

### Orientation correction

For the production `GTail` orientation:

```text
GTail 2 1 x u = x + 2*u.
```

Therefore the successor increment is represented by the reversed degree-two stage:

```text
x = 1
u = n
GTail 2 1 1 n = 2*n + 1.
```

Since the boundary is `1`, the full stage value is also `2*n+1`.

Do not use the false orientation `GTail 2 1 n 1 = 2*n+1`.

### Existing production fact

PrimorialUnitUniverse already proves:

```text
fresh tied successor-pair delay
-> q | 2*n + 1.
```

The first bridge target is therefore:

```text
fresh tied successor-pair delay
-> PrimeCaught q (successorIncrementGaugeStage n).
```

This is a single-stage GN/channel reinterpretation.

### Genuine-transition audit

A stronger MultiGauge interpretation requires a non-tautological `GNGaugeTransition 2` whose balance law comes from actual Legendre / primorial / gauge semantics and whose numerator support gives independent pruning.

Endpoint-copy constructions such as

```text
numerator   := second.value
denominator := first.value
```

are mathematically valid but provide no new information and do not count as a successful transition bridge.

Audit:

```text
successor increment stage n -> n+1;
fresh-prime insertion S -> insert q S;
existing fixed/refined gauge semantics;
short paths with independently localized numerator support;
untied successor case.
```

Outcome policy:

```text
Outcome A — GENUINE TRANSITION GAIN
  a non-tautological transition/path yields new Legendre pruning.

Outcome B — CHANNEL BRIDGE ONLY
  reversed-stage L036 bridge is useful, but no genuine transition/global survivor theorem.

Outcome C — NO MATERIAL GAIN
  do not add decorative bridge abstractions.
```

No Legendre conjecture endpoint may be claimed unless an actual square-shell escape provider is proved.

See:

```text
instruction-002.md
```

---

## Phase MG-002 — exact channel path states

Status: PLANNED / CONDITIONAL

Only after the Legendre audit, investigate whether stages should expose the three off-exponent prime states:

```text
escape
boundary-only
gn-only
```

For prime `q` with `q ∤ d`, simultaneous boundary + GN capture is forbidden by the existing gcd firewall.

A state API is warranted only if it proves transition pruning that is awkward in raw divisibility language.

---

## Phase MG-003 — concrete normalization/refinement bridges

Status: DEFERRED UNTIL AFTER LEGENDRE CHECKPOINT

Candidate providers:

```text
FixedBigGauge.fixedBigUnit_transport
FixedBigGauge.fixedBigUnit_refinement
freshPrime_fixedBigUnit_refinement
explicit quotient/normalization packets from FLT or ABC
Petal / primitive-boundary transitions
```

Each bridge must prove the generic balance law from its own concrete semantics.

Do not make the generic MultiGauge layer depend on these applications.

---

## Phase MG-004 — Norm / lattice landing

Status: OUT OF CURRENT FRONT-HALF SCOPE

Resume the second half of:

```text
docs/not_implements/260912-MultiGauge-Divisibility-Norm-Lattice-Landing.md
```

only after prime-escape transport and concrete gauge-transition semantics are stable.

Intended later chain:

```text
GN gcd sieve
-> gauge transition / path admissibility
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
3. Transition support is explicit: numerator injects possible new prime support;
   denominator removes possible old prime support.
4. New capture must be localized before any counting or asymptotic argument.
5. Finite paths remain simple unless a stronger representation is mathematically required.
6. Application bridges must not manufacture tautological transitions and call them pruning.
7. No Norm/lattice abstraction is introduced merely because it belongs to the long-term plan.
8. No sorry/admit/new axiom declarations.
```

---

## Immediate execution order

```text
MG-000
  COMPLETE / APPROVED

MG-001
  COMPLETE / APPROVED

instruction-002
  NEXT
  reversed d=2 successor-increment stage
  L036 capture/persistence bridge
  genuine-transition audit
  untied-case audit
  Legendre-frontier impact assessment

report-002 + review
  decide whether to continue Legendre,
  return to generic channel/path states,
  or move to concrete gauge transitions.
```
