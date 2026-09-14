# instruction-002 — MG-L2 Legendre degree-two MultiGauge audit

cid: `6aa763a7-1a14-83e8-9041-1029d978663c`

## Role

Act as a Lean formalization engineer with a research-audit mindset.

This checkpoint is downstream of the completed generic MultiGauge kernel.
Do not modify the generic mathematics merely to force a Legendre application.

The purpose is to determine exactly how much of the existing Legendre / PrimorialUnitUniverse fresh-prime obstruction is genuinely explained by MultiGauge.

---

## Repository / branch

```text
repository: Deskuma/dkmath
branch:     wip/number-theory-multi-gauge-divisibility-260914-v0
```

Read first:

```text
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/README.md
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/ROADMAP.md
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/review-001.md
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-001.md
```

Inspect production source directly:

```text
DkMath/NumberTheory/MultiGauge/Basic.lean
DkMath/NumberTheory/MultiGauge/PrimeTransport.lean
DkMath/NumberTheory/MultiGauge/Path.lean
DkMath/NumberTheory/PrimorialUniverse/SquareAnchorOffsetSuccessorPairFreshPrimeTransport.lean
DkMath/NumberTheory/Legendre/Frontier.lean
DkMath/Lib/Cosmic/GTail.lean
```

Do not rely on old prose for theorem signatures.

---

## Frozen orientation fact

This checkpoint must use the actual `GTail` argument orientation.

At degree two:

```text
GTail 2 1 x u = x + 2*u.
```

Hence the successor-square increment is represented by the reversed stage:

```text
x = 1
u = n
```

so that:

```text
GTail 2 1 1 n = 2*n + 1
```

and because the boundary factor is `1`:

```text
GNGaugeStage.value = 2*n + 1.
```

Do not write or prove the false orientation `GTail 2 1 n 1 = 2*n+1`.

---

## Existing Legendre-side production fact

The PrimorialUnitUniverse development already proves:

```text
freshPrime_dvd_successor_increment_of_tied_pair_delay
```

with conclusion:

```text
q | 2*n + 1.
```

Its hypotheses are a fresh prime insertion, equal first-hit offsets for the successor square anchors `n` and `n+1`, and strict delay of the tied successor-pair minimum.

The theorem is already production-proved. Do not re-prove its reservation/minimizer machinery.

---

## Task 1 — canonical reversed degree-two stage

Create a minimal downstream bridge, preferably under the Legendre namespace/module ownership rather than inside generic MultiGauge.

Candidate file:

```text
DkMath/NumberTheory/Legendre/MultiGaugeBridge.lean
```

Define a canonical stage such as:

```lean
def successorIncrementGaugeStage (n : ℕ) : GNGaugeStage 2 := ...
```

with:

```text
x = 1
u = n
Coprime 1 n
```

Prove exact identities for:

```text
successorIncrementGaugeStage n |>.gnValue = 2*n + 1
successorIncrementGaugeStage n |>.value   = 2*n + 1
```

Use simplification / existing `GTail` facts where possible. Do not duplicate the general `GTail` development.

---

## Task 2 — re-express L036 as MultiGauge capture

Package the tied-pair obstruction as a semantic capture theorem.

Target shape, adjusted to actual namespaces/signatures:

```text
fresh tied successor-pair delay
-> PrimeCaught q (successorIncrementGaugeStage n)
```

Also package the persistence direction if it is clean:

```text
PrimeEscapes q (successorIncrementGaugeStage n)
-> the tied successor pair persists under insertion of q.
```

This should be a thin bridge using the existing L036 theorem and the exact stage-value identity.

Do not duplicate the tied-pair proof.

---

## Task 3 — channel interpretation

Record the exact channel meaning of the reversed stage.

Because its boundary is `1`, any prime capture is necessarily on the GN channel.

Establish the strongest clean theorem justified by existing APIs, for example:

```text
PrimeCaught q (successorIncrementGaugeStage n)
<-> q | (successorIncrementGaugeStage n).gnValue
```

or a prime-specific equivalent.

The mathematical point is:

```text
tied-pair delay prime
-> captured by the degree-two reversed GN observer
-> not captured through the boundary channel.
```

This is already useful even if no transition bridge exists.

---

## Task 4 — audit for a genuine MultiGauge transition

Now ask whether the Legendre/PrimorialUnitUniverse semantics provide a **non-tautological** `GNGaugeTransition 2`.

Inspect at least these possible interpretations:

```text
A. transition between successor-increment stages n -> n+1;
B. transition induced by fresh-prime basis insertion S -> insert q S;
C. transition induced by an existing fixed/refined arithmetic unit;
D. a short path whose numerator support independently localizes the L036 delay prime.
```

A transition is substantive only if its balance law is derived from existing arithmetic semantics and its numerator/denominator support is independently simpler or more restrictive than merely copying endpoint values.

The following does **not** count as progress:

```text
numerator   := second.value
denominator := first.value
```

or any algebraically equivalent endpoint-copy packet whose transport theorem merely says that a divisor of the endpoint divides the endpoint.

If no substantive transition exists in current production, state this clearly.

---

## Task 5 — untied successor case audit

Inspect the production theorem

```text
squareAnchorSuccessorPairPositiveFirstHit_insert_fresh_lt_iff
```

and determine whether MultiGauge gives any new restriction in the untied case.

The current tied theorem gains `q | 2*n+1` because delay deletes both equal-minimum seats.
In an untied pair, strict delay may require deletion of only the unique minimizing side.

Do not assume the same GN obstruction survives.

Report precisely whether:

```text
1. current MultiGauge APIs produce a genuine new untied localization;
2. only the existing single-seat divisibility remains;
3. a missing concrete gauge transition is exactly the blocker.
```

Do not invent a global survivor theorem.

---

## Task 6 — compare against the actual Legendre frontier

The current endpoint remains equivalent to finite square-offset escape:

```text
LegendreConjecture
<->
forall n > 0, not SquareOffsetsFullyCovered n.
```

Determine whether anything proved in this checkpoint advances that existence statement.

Distinguish strictly between:

```text
local obstruction localization,
transition/path pruning,
global square-shell survivor existence.
```

A localization theorem is not a Legendre proof.

---

## Outcome policy

Use one of these outcomes.

```text
Outcome A — GENUINE TRANSITION GAIN

A non-tautological Legendre MultiGauge transition/path is constructed,
and it yields a new production pruning theorem beyond the existing L036
restatement.

Outcome B — CHANNEL BRIDGE ONLY

The reversed degree-two stage and L036 capture/persistence bridge are useful
and production-worthy, but no non-tautological transition or new global
survivor theorem is obtained.

Outcome C — NO MATERIAL GAIN

Even the proposed channel bridge adds no useful stable API beyond existing
production. Record the audit and do not add decorative abstractions.
```

Outcome B is an acceptable and likely useful result.

---

## Scope limits

Do not implement:

```text
Norm / Eisenstein / TraceOne landing;
ABC or FLT bridges;
new analytic prime-gap estimates;
new conjectural provider;
LegendreConjecture endpoint from an unproved escape hypothesis;
custom automata merely for presentation.
```

Do not modify generic `DkMath.NumberTheory.MultiGauge` unless the audit exposes an actual generic defect. Downstream bridge facts belong downstream.

No `sorry`, `admit`, or new `axiom` declarations.

---

## Validation and report

If production Lean is added, run focused builds for every touched module and its facade/import consumer.

Create:

```text
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-002.md
```

The report must include:

```text
exact orientation used for GTail 2 1;
production theorems added;
whether a genuine transition was found;
why any rejected transition candidate is tautological or non-informative;
untied-case verdict;
impact on SquareOffsetsFullyCovered / Legendre frontier;
focused build commands/results;
forbidden scan;
final Outcome A/B/C.
```
