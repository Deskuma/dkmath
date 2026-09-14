# instruction-005 — MG-003C primitive-shape transition provider audit

cid: `6aa763a7-1a14-83e8-9041-1029d978663c`

## Role

Act as an implementation-oriented arithmetic auditor.

This checkpoint is **audit-first**.

Do not manufacture a `GNGaugeTransition` merely to satisfy the structure. The task is to determine whether the current repository already contains an independently meaningful arithmetic transformation between two coprime GN stages of the same degree.

A production implementation is required only if such a provider is genuinely present.

---

## Repository / branch

```text
repository: Deskuma/dkmath
branch:     wip/number-theory-multi-gauge-divisibility-260914-v0
```

Read first:

```text
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/ROADMAP.md
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/review-004.md
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-004.md

DkMath/NumberTheory/MultiGauge/Basic.lean
DkMath/NumberTheory/MultiGauge/PrimeTransport.lean
DkMath/NumberTheory/MultiGauge/Path.lean
DkMath/NumberTheory/MultiGauge/RawNormalization.lean
DkMath/NumberTheory/MultiGauge/RawRefinementPath.lean
```

Inspect current production sources directly whenever theorem signatures matter.

---

## Frozen distinction

MG-003A/B proved the common-scale mechanism:

```text
(x,u) -> (k*x,k*u)
```

with primitive shape unchanged.

That mechanism is complete and is **not** a primitive `GNGaugeTransition`.

The current target is different:

```text
first  : GNGaugeStage d
second : GNGaugeStage d

first and second have genuinely different primitive coprime coordinates,
```

with an independently derived balance

```text
second.value * denominator
=
first.value * numerator.
```

The coefficients must come from the source arithmetic semantics, not from copying endpoint values.

---

## What counts as a genuine provider

A candidate qualifies only if all of the following are satisfied:

```text
1. same exponent d on both GN stages;
2. first and second are actual coprime `GNGaugeStage d` values;
3. the coordinate pair changes primitive shape, not only common scale;
4. the balance law follows from an already meaningful production theorem/packet;
5. numerator/denominator support has independent arithmetic meaning;
6. endpoint-copy constructions are not used;
7. no new conjectural axiom/provider is introduced.
```

Examples of meaningful coefficients would be a certified removed prime power, descent factor, or normalization factor already present in the source theorem.

---

## Mandatory candidate audit

Audit at least the following families.

### A. FLT q-adic / GN reduced-gap descent

Inspect the production chain around names such as:

```text
QAdicDescentExistenceTarget
PrimeGe5BranchAPrimitiveRestoreGNReducedGapTarget
gnReducedGap_of_qAdicDescentExistence
primitivePacketDescent_of_gnReducedGap
smallerPacket_of_gnReducedGap_and_peel
```

The mathematically interesting shape is roughly:

```text
old gap * GN(p, old gap, y) = x^p

new gap * GN(p, new gap, y) = (x/q)^p
```

which, when all exact divisibility data are available, suggests a removal law of the form

```text
oldStage.value = q^p * newStage.value.
```

If this relation is only available under an open target/hypothesis, classify it as conditional/open. Do not report it as an unconditional provider.

If an already-proved concrete packet supplies the required old/new coprimality and exact equality with no new mathematical hypothesis, then a downstream FLT-specific MultiGauge bridge may be justified.

### B. FLT3 unconditional cubic descent

Inspect the current unconditional FLT3 production modules and determine whether the descent packet contains two natural coprime GN stages of degree `3` with an exact multiplicative observer relation.

Do not infer such a relation merely because a strict descent exists in another algebraic carrier.

### C. FLT5 / golden descent

Inspect the current FLT5 descent route.

A transformation in `GoldenInt`, a norm relation, or an algebraic-unit relation is not automatically a natural-number `GNGaugeTransition`.

Classify precisely whether a same-degree natural GN stage balance exists.

### D. Petal / StructuralArithmetic / primitive-boundary transport

Search for explicit coordinate-change theorems that alter a primitive coprime `(x,u)` pair while preserving an exact multiplicative observer relation.

Avoid importing application modules into generic MultiGauge.

### E. ABC / complement / other packets

Only count a candidate if it really gives the same `GNGaugeStage d` observer on both sides. A relation between different arithmetic quantities, different degrees, Norms, or complements is not enough.

---

## Candidate classification table

In `report-005.md`, classify every serious candidate under one of:

```text
UNCONDITIONAL-PROVIDER
CONDITIONAL-PROVIDER
OPEN-KERNEL
NOT-SAME-OBSERVER
COMMON-SCALE-ONLY
TAUTOLOGICAL
```

For each candidate record:

```text
source module
theorem / packet names
first candidate stage
second candidate stage
candidate numerator / denominator
which hypotheses establish coprimality
which theorem establishes balance
why the classification is correct
```

---

## Implementation policy

### If an unconditional provider exists

Implement the narrowest downstream bridge in the owning application namespace.

Examples of acceptable ownership:

```text
DkMath/FLT/MultiGaugeBridge.lean
DkMath/NumberTheory/StructuralArithmetic/MultiGaugeBridge.lean
```

Do not make generic `DkMath.NumberTheory.MultiGauge` import FLT, ABC, Legendre, or PrimorialUniverse.

The bridge should construct a real `GNGaugeTransition d` and prove at least one nontrivial consequence using the generic API, for example:

```text
prime support removed by a certified denominator factor;
prime escape transported across the concrete transition;
first/new capture localized to an independently meaningful numerator.
```

### If only conditional providers exist

Do not promote them as unconditional arithmetic facts.

A small conditional bridge is allowed only if it packages an already-existing semantic packet cleanly and is useful on its own. Its hypotheses must expose the open/conditional input explicitly.

It does **not** count as Outcome A unless the provider itself is unconditional production mathematics.

### If no genuine provider exists

Add no decorative Lean wrapper.

Produce the audit report and stop with Outcome B.

---

## Explicit non-goals

Do not implement or modify:

```text
MG-002 channel automaton
Norm / Eisenstein / TraceOne landing
Legendre frontier
Goldbach frontier
new FLT theorem
new ABC theorem
analytic estimates
new descent axiom/provider
```

Do not weaken `GNGaugeStage.coprime`.

Do not reinterpret raw common scaling as primitive shape change.

---

## Special caution: source theorem vs target wrapper

A theorem of the form

```text
SomeOpenTarget -> GNReducedGapTarget
```

is a dependency transport theorem, not evidence that the reduced-gap object exists unconditionally.

Likewise, `#print axioms` being clean does not make a theorem unconditional if its statement accepts a mathematical target as an argument.

Classify based on hypotheses, not merely kernel axiom output.

---

## Optional generic observation

If useful for downstream code, it is acceptable to prove a tiny generic constructor from an independently supplied exact multiplicative equality, but only if it reduces repetitive bridge boilerplate.

Do not count such a constructor as a provider. The provider is the application theorem that supplies the equality.

---

## Validation

If Lean production code is added, run focused builds for every new/changed module and its facade.

Always run:

```text
git diff --check
```

and scan changed Lean files for:

```text
sorry
admit
new axiom declarations
```

---

## Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-005.md
```

The report must contain the candidate classification table and one of the following outcomes.

```text
Outcome A — GENUINE PRIMITIVE TRANSITION PROVIDER FOUND

Outcome B — NO UNCONDITIONAL PRIMITIVE PROVIDER FOUND
  conditional/open candidates may exist, but no production provider qualifies.

Outcome P — ENGINEERING PARTIAL
  a qualifying provider appears to exist, but implementation could not be completed for technical reasons.
```

Do not use Outcome A for a conditional target wrapper or tautological endpoint-copy transition.
