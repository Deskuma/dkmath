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

Implemented the smallest production packet supporting prime escape transport.

Production output:

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

Production theorem family now includes:

```text
second capture -> first capture OR q | numerator
first escape + q ∤ numerator -> second escape

first capture -> second capture OR q | denominator
second escape + q ∤ denominator -> first escape

q ∤ numerator and q ∤ denominator
-> prime visibility iff across the transition
```

The one-stage observer is decomposed into boundary / GN channels, and the existing GN gcd firewall yields the stronger reusable localization:

```text
q | stage.x
q | stage.gnValue
1 <= d
-> q | d
```

without requiring `q` prime.

See:

```text
report-000.md
review-000.md
```

---

## Phase MG-001 — finite prime-escape paths

Status: NEXT

Introduce the minimal finite-chain representation justified by MG-000.

Research target:

$$
q\nmid A_0
\land
\forall i<k,\;q\nmid\nu_i
\Longrightarrow
\forall j\le k,\;q\nmid A_j.
$$

First-capture localization target:

$$
q\nmid A_0
\land
q\mid A_j
\Longrightarrow
q\mid\prod_{i<j}\nu_i.
$$

The preferred path invariant is the telescoped balance:

```text
Ak * product(denominators)
=
A0 * product(numerators).
```

In addition to endpoint localization, MG-001 must prove an all-stage escape theorem and an actual escape-to-capture transition witness whose numerator is divisible by `q`.

Prefer a simple `List` / recursive linked-path representation over a custom automaton framework unless the theorem statements demand more structure.

Expected output:

```text
DkMath/NumberTheory/MultiGauge/Path.lean
report-001.md
```

See:

```text
instruction-001.md
```

---

## Phase MG-002 — exact channel path states

Status: PLANNED / CONDITIONAL

Only after MG-001 is stable, investigate whether each stage should expose the three off-exponent prime states:

```text
escape
boundary-only
gn-only
```

For prime `q` with `q ∤ d`, `boundary + gn` is forbidden by the existing gcd firewall.

The purpose of this phase is not to build a decorative state machine. A state API is warranted only if it proves transition pruning theorems that are awkward in raw divisibility language.

Candidate questions:

```text
Can a boundary-only prime become gn-only without entering transition support?
Can a gn-only prime disappear without entering denominator support?
Which channel switches are forced by x/u normalization?
```

---

## Phase MG-L2 — Legendre degree-two bridge

Status: PLANNED CHECKPOINT

This is the first major downstream audit before any quadratic-order work.

Keep this bridge outside the generic MultiGauge core.

Relevant production fact from the PrimorialUnitUniverse development:

```text
fresh tied successor-pair delay
-> q | 2*n + 1.
```

Degree-two interpretation:

```text
2*n + 1 = GN₂(n,1)
```

Target questions:

```text
1. Can the tied-pair theorem be expressed as a MultiGauge first-capture localization?
2. Does the transition formulation explain the exceptional support as GN₂ support?
3. Can the same framework constrain the untied successor case?
4. Does a two-stage or short finite-path theorem yield a genuine new square-shell escape theorem?
```

Outcome policy:

```text
Outcome A:
  transition-aware pruning gives a new Legendre production theorem;
  continue Legendre bridge.

Outcome B:
  useful localization only, no global survivor theorem;
  record the obstruction and return to generic MultiGauge path theory.

Outcome C:
  no gain beyond L036 restatement;
  do not force further Legendre integration.
```

No Legendre conjecture endpoint may be claimed unless an actual square-shell escape provider is proved.

---

## Phase MG-003 — concrete normalization/refinement bridges

Status: DEFERRED UNTIL AFTER LEGENDRE CHECKPOINT

Connect the generic transition balance law to existing concrete DkMath mechanisms, one bridge at a time.

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

Only after the prime-escape transport theory is stable.

Intended later chain:

```text
GN gcd sieve
-> gauge transition / path admissibility
-> Norm divisibility
-> coordinate divisibility
-> integer-lattice landing
-> power/Core-image landing
```

This branch may contain planning documents for this future work, but MG-000 and MG-001 must not acquire quadratic-order dependencies.

---

## Architectural invariants

Throughout the branch:

```text
1. Existing one-stage gcd facts are dependencies, not targets for re-proof.
2. Generic MultiGauge code remains independent of ABC, FLT, and Legendre.
3. Transition support is explicit: numerator injects possible new prime support;
   denominator removes possible old prime support.
4. New capture must be localized before any counting or asymptotic argument.
5. Finite-path generalization follows a successful two-stage theorem, not vice versa.
6. No Norm/lattice abstraction is introduced merely because it belongs to the long-term plan.
7. No sorry/admit/new axiom declarations.
```

---

## Immediate execution order

```text
MG-000
  COMPLETE / APPROVED

instruction-001
  NEXT
  finite path composition
  telescoped support balance
  all-stage escape
  first-capture localization

report-001 + review
  decide whether MG-L2 Legendre audit is justified

MG-L2 Legendre bridge
  only after MG-001 review, unless a genuinely stronger result emerges earlier
```
