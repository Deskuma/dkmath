# instruction-004 — MG-003B finite raw-refinement paths and primitive-shape invariance

cid: `6aa763a7-1a14-83e8-9041-1029d978663c`

## Role

Implement the next bounded production checkpoint of the MultiGauge campaign.

This is a Lean implementation task, not a search for a new Legendre theorem and not a Norm/lattice task.

MG-003A is already complete. Reuse it.

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
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/review-003.md
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-003.md

DkMath/NumberTheory/MultiGauge/RawNormalization.lean
DkMath/NumberTheory/PrimorialUniverse/MultiGaugeUnitRefinementBridge.lean
```

Inspect current Mathlib theorem names before proving gcd/product facts manually.

---

## Mathematical purpose

The original campaign question is:

```text
q escapes in unit system u₀.
After successive synchronized refinements,
does q keep escaping?
If q is first captured, which actual refinement factor introduced it?
```

MG-003A proves the one-step law:

```text
RawPrimeEscapes q s
RawPrimeCaught q (s.scaleBy k)
-> q | k.
```

MG-003B must lift this to a finite positive refinement chain and must close the normalization fact that common scaling preserves primitive shape.

---

## Task 1 — common-scale algebra

In a new generic module, preferably:

```text
DkMath/NumberTheory/MultiGauge/RawRefinementPath.lean
```

prove the basic scale-composition facts needed downstream.

Expected facts include equivalents of:

```text
(scaleBy k₂ (scaleBy k₁ s))
=
scaleBy (k₁*k₂) s
```

and

```text
(scaleBy k s).scale = k * s.scale
```

using the existing gcd multiplication theorem from Mathlib if available.

Do not duplicate a library theorem with a large custom proof when a canonical theorem exists.

---

## Task 2 — primitive-shape invariance

For positive common scale and positive refinement factor, prove that gcd normalization of a synchronized refinement recovers the same primitive coprime stage.

Target shape:

```text
0 < s.scale
0 < k
->
(scaleBy k s).primitiveStage (...) = s.primitiveStage (...)
```

Proof-term equality fields are irrelevant; use extensional equality of stage coordinates and proof irrelevance as appropriate.

Also expose convenient corollaries if useful:

```text
primitive x unchanged;
primitive u unchanged;
primitive PrimeCaught / PrimeEscapes unchanged.
```

Do not weaken `GNGaugeStage.coprime`.

This theorem is conceptually important:

```text
synchronized unit refinement
changes common scale,
not primitive shape.
```

---

## Task 3 — finite raw-refinement path

Introduce the smallest useful path representation for repeated synchronized scaling.

A preferred shape is conceptually:

```lean
structure GNRawRefinementPath (d : ℕ) where
  start : GNRawGaugeStage d
  factors : List ℕ
  factors_pos : ∀ k ∈ factors, 0 < k
```

Exact naming may follow local conventions.

Do not reuse `GNGaugePath` by manufacturing fake `GNGaugeTransition`s. Raw scale refinement is a different layer and should have its own small path representation.

Define only the data needed for theorem statements, for example:

```text
cumulativeFactor
endStage
stages / visitedStages
```

The endpoint should be provably the initial raw stage scaled by the product of all factors.

---

## Task 4 — finite homogeneous transport

Prove the exact endpoint observer law:

```text
endStage.value
=
(cumulativeFactor)^d * start.value.
```

If the recursive stage representation makes a stronger prefix theorem natural, keep it small and reusable.

Do not introduce rational arithmetic, real-valued units, valuations, or Norms into the generic module.

---

## Task 5 — all-stage prime escape

For prime `q`, prove the finite-chain form of the original question:

```text
RawPrimeEscapes q path.start
(∀ k ∈ path.factors, ¬ q | k)
->
∀ s ∈ path.stages, RawPrimeEscapes q s.
```

The proof should reuse the one-step MG-003A theorem or its contraposition rather than re-proving homogeneous divisibility from scratch at every recursive step.

Equivalent clean formulations are acceptable.

---

## Task 6 — first/new capture localization

If the path starts escaped and some visited stage is caught, prove that a real refinement factor carries `q`.

Required theorem shape:

```text
RawPrimeEscapes q path.start
(∃ s ∈ path.stages, RawPrimeCaught q s)
->
∃ k ∈ path.factors, q | k.
```

A stronger actual adjacent-step witness is preferred if it remains simple:

```text
there exists one refinement step
before: escaped
factor: divisible by q
after: caught.
```

Do not force numeric first-index machinery merely to say “first”. Existence of an escape-to-capture adjacent step with factor support is enough.

Also prove the endpoint product localization if natural:

```text
start escaped
end caught
->
q | cumulativeFactor.
```

For prime `q`, a corollary from product divisibility to membership in one factor is useful.

---

## Task 7 — concrete regressions

Add at least one small regression with two or three positive factors showing both behaviors:

```text
1. q avoids every factor -> q escapes every visited stage;
2. q first appears when a factor divisible by q is inserted.
```

Prefer tiny numerals and `norm_num` where appropriate.

---

## Optional PUU composition bridge

Only if it stays small and follows directly from current APIs, add a downstream PUU theorem showing composition of two `UnitRefinesBy` relations and matching it to the raw cumulative factor.

Do not build a dependent list of `PositiveUnit`s unless required by an actual theorem.

The generic finite raw path is the mandatory target; a large PUU path framework is not.

---

## Explicit non-goals

Do not implement in this checkpoint:

```text
MG-002 channel automaton;
Legendre changes;
Goldbach changes;
primitive-shape GNGaugeTransition providers;
Norm divisibility;
Eisenstein / TraceOne;
FLT / ABC application migration;
analytic estimates;
new conjecture endpoints.
```

Do not identify common-scale refinement with primitive `GNGaugeTransition`.

---

## Required validation

Run focused builds for the new module and facades you modify.

At minimum:

```text
lake build DkMath.NumberTheory.MultiGauge.RawRefinementPath
lake build DkMath.NumberTheory.MultiGauge
```

If a PUU bridge is modified/added, also build its focused target and the PUU facade.

Run:

```text
git diff --check
```

Scan changed Lean sources for:

```text
sorry
admit
new axiom declarations
```

Record warnings separately from environmental shell noise.

---

## Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-004.md
```

Record:

```text
outcome;
files changed;
final path representation;
primitive-shape invariance theorem;
finite homogeneous endpoint law;
all-stage escape theorem;
new/first capture factor localization;
regressions;
build commands/results;
any deviation from this instruction.
```

Outcome A requires all of:

```text
primitive shape invariant under positive common scaling;
finite raw refinement path;
all-stage escape under factor avoidance;
new capture localized to an actual refinement factor.
```

If primitive normalization invariance encounters a real arithmetic/API blocker, report Outcome P rather than hiding it behind a weaker wrapper.
