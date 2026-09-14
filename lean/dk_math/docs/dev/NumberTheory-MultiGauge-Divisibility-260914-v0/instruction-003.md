# instruction-003 — MG-003A Raw/Primitive Gauge Normalization & Unit-Refinement Transport

cid: `6aa763a7-1a14-83e8-9041-1029d978663c`

## Role

Implement the missing common-scale layer between physical/unit-coordinate refinement and the existing primitive `GNGaugeStage` API.

This is a Lean implementation task with a small architectural audit.

Do **not** refactor MG-000/MG-001 unless a genuine type-theoretic obstruction is found.
Do **not** build the MG-002 state automaton in this checkpoint.
Do **not** return to Legendre yet.
Do **not** introduce Norm/Eisenstein/TraceOne machinery.

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
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/review-002.md
lean/dk_math/docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-002.md

lean/dk_math/DkMath/NumberTheory/MultiGauge/Basic.lean
lean/dk_math/DkMath/NumberTheory/MultiGauge/PrimeTransport.lean
lean/dk_math/DkMath/NumberTheory/MultiGauge/Path.lean

lean/dk_math/DkMath/NumberTheory/PrimorialUniverse/UnitCoordinateRefinement.lean
lean/dk_math/DkMath/NumberTheory/PrimorialUniverse/CommonLattice.lean
lean/dk_math/DkMath/NumberTheory/PrimorialUniverse/UnitIntersectionClassification.lean

lean/dk_math/DkMath/Lib/Cosmic/GTail.lean
```

Inspect current theorem signatures before implementing. Reuse Mathlib gcd/division facts and existing DkMath results rather than re-proving them under new names.

---

## Mathematical diagnosis

The current production primitive stage is

```lean
GNGaugeStage d
```

with coordinates `x,u` and a field

```text
Coprime x u.
```

Concrete unit refinement already present in PrimorialUniverse acts on raw coordinates by synchronized multiplication:

```text
coarse = k * fine
coordinate n in coarse
-> coordinate n*k in fine.
```

For a pair of raw coordinates this naturally gives

```text
(x,u) -> (x*k,u*k).
```

For `k > 1`, this pair generally has common factor `k`, so it is **not** directly a `GNGaugeStage`.

The missing layer is therefore:

```text
raw pair
=
common gcd/scale
×
primitive coprime pair.
```

This checkpoint must formalize that separation.

---

## Task 0 — ownership audit

Before adding declarations, search for an existing generic raw-GN normalization or common-scale homogeneity API.

If a canonical owner already exists, reuse or minimally extend it.

Do not duplicate a stable theorem merely to satisfy suggested names below.

Record the audit in `report-003.md`.

---

## Task 1 — raw GN gauge stage

Add a generic raw natural-coordinate stage without a coprimality field.

Preferred location:

```text
DkMath/NumberTheory/MultiGauge/RawNormalization.lean
```

Suggested shape:

```lean
structure GNRawGaugeStage (d : ℕ) where
  x : ℕ
  u : ℕ
```

Expose the same arithmetic observer as the primitive stage:

```text
gnValue = GTail d 1 x u
value   = x * gnValue
```

Also expose the common scale

```text
scale = gcd x u.
```

A helper for common scaling is encouraged:

```text
scaleBy k : (x,u) -> (k*x,k*u)
```

or the repository-conventional multiplication orientation.

If useful, add raw predicates such as

```text
RawPrimeCaught
RawPrimeEscapes
```

but avoid a large parallel API. Keep only what is needed for exact support decomposition and refinement transport.

---

## Task 2 — common-scale homogeneity

Prove the exact observer scaling law under synchronized coordinate multiplication.

Target mathematics:

$$
A_d(kx,ku)=k^d A_d(x,u),
$$

where

```text
A_d(x,u) = x * GTail d 1 x u.
```

Preferred theorem meaning:

```text
(scaleBy k s).value = k^d * s.value.
```

A clean proof may use the existing identity

```text
(x+u)^d = x * GTail d 1 x u + u^d
```

or direct `GTail` homogeneity, whichever produces the smaller stable theorem surface.

If a reusable `GTail` homogeneity theorem is genuinely missing and naturally belongs in `DkMath.Lib.Cosmic`, it may be added there, but do not broaden the task into a large Lib refactor.

---

## Task 3 — primitive normalization by gcd

For a raw stage with positive/nonzero gcd, normalize

```text
g = gcd x u
x₀ = x / g
u₀ = u / g.
```

Use the existing Mathlib theorem corresponding to

```text
Coprime (x/g) (u/g).
```

Construct the primitive stage

```text
primitiveStage : GNGaugeStage d.
```

The normalization may take an explicit hypothesis such as

```text
0 < gcd x u
```

instead of forcing positivity into the raw structure itself.

Prove the coordinate reconstruction needed downstream:

```text
x = g * x₀    (up to multiplication orientation)
u = g * u₀.
```

Then prove the central exact factorization:

$$
A_d(x,u)=g^d A_d(x_0,u_0).
$$

This theorem is the semantic bridge between raw gauge scale and the existing primitive observer.

---

## Task 4 — exact prime-support decomposition

For prime `q` and the assumptions needed for primitive normalization, prove an exact support theorem of the form

```text
q | raw.value
<->
q | raw.scale OR PrimeCaught q raw.primitiveStage
```

with any necessary condition such as `1 <= d` stated explicitly.

Also expose the escape form if it remains concise:

```text
RawPrimeEscapes q raw
<->
(¬ q | raw.scale) AND PrimeEscapes q raw.primitiveStage.
```

This is the key structural result of MG-003A:

```text
raw prime visibility
=
common-scale support
OR
primitive GN support.
```

Do not overstate disjointness: a prime may divide both the scale and the primitive observer unless additional hypotheses forbid it.

---

## Task 5 — concrete common-scale refinement transport

Use the homogeneity theorem to prove the first non-tautological concrete transport law.

For prime `q`, common scaling by `k` should yield the logical content:

```text
raw escape before refinement
AND q ∤ k
-> raw escape after refinement.
```

Equivalently / additionally:

```text
raw escape before refinement
AND raw capture after refinement
-> q | k.
```

Also record persistence of old capture under common scaling if it is a short corollary.

This theorem must arise from the independent refinement factor `k`, not by copying endpoint values into a numerator/denominator field.

Do **not** manufacture a `GNGaugeTransition` merely to make this result fit the MG-000 type. It is acceptable, and currently expected, that common-scale refinement is a distinct layer from primitive-shape transition.

---

## Task 6 — PrimorialUniverse semantic bridge

Add a downstream bridge from the existing physical/unit-coordinate refinement API to the new raw-stage scaling theorem.

Preferred ownership:

```text
DkMath/NumberTheory/PrimorialUniverse/MultiGaugeUnitRefinementBridge.lean
```

The generic `DkMath.NumberTheory.MultiGauge` modules must not import PrimorialUniverse.

Use existing:

```text
UnitRefinesBy
HasUnitCoordinate
unitCoordinate_refine
```

For two absolute points with coarse coordinates `x` and `u`, package the fact that the fine coordinates are `x*k` and `u*k`.

Then connect this synchronized coordinate change to the raw `scaleBy k` stage and reuse Task 5.

Desired semantic theorem family:

```text
same two absolute quantities under integer unit refinement
-> raw stage is scaled by k;

prime escapes in coarse raw observer
and is captured in refined raw observer
-> q | k.
```

The exact theorem shape may be a packet/conjunction if that avoids unused semantic hypotheses.

This bridge is downstream evidence that the generic raw scaling law models an actual DkMath unit change.

---

## Task 7 — architecture audit

At the end, state explicitly whether production now supports the following interpretation:

```text
common-scale refinement:
  changes raw support through k^d,
  while primitive normalization isolates the coprime GN core;

primitive-shape transition:
  remains represented separately by GNGaugeTransition.
```

Check whether synchronized refinement preserves the normalized primitive stage exactly. If this is easy and natural, prove it. If it requires avoidable division gymnastics, record it as a derived consequence rather than forcing a brittle theorem.

Do not merge the two transition notions unless a mathematically canonical unification becomes evident.

---

## Required regressions

Include small executable/provable examples sufficient to catch orientation mistakes.

At minimum test one nontrivial common scaling, e.g. a raw coprime pair scaled by `k > 1`, and verify:

```text
gcd scale grows;
raw value scales by k^d;
primitive coordinates recover the original coprime pair;
a prime newly introduced solely by k is localized to scale support.
```

Choose small values that `norm_num`/`decide` can discharge reliably.

---

## Scope barriers

Do not implement in MG-003A:

```text
MG-002 channel automaton
new Legendre theorem
SquareOffsetsFullyCovered argument
Norm divisibility
Eisenstein / TraceOne landing
ABC or FLT application bridge
analytic/counting bounds
```

Do not weaken existing `GNGaugeStage.coprime` merely to make raw refinement fit. The entire point of this checkpoint is to separate raw scale from primitive stage.

No `sorry`, `admit`, or new `axiom` declarations.

---

## Expected files

Likely production output:

```text
DkMath/NumberTheory/MultiGauge/RawNormalization.lean
DkMath/NumberTheory/MultiGauge.lean                  # import update
DkMath/NumberTheory/PrimorialUniverse/MultiGaugeUnitRefinementBridge.lean
```

Facade integration in `DkMath.NumberTheory.PrimorialUniverse` is optional if consistent with current ownership conventions.

Add:

```text
docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-003.md
```

---

## Outcome policy

```text
Outcome A — RAW/PRIMITIVE TRANSPORT ESTABLISHED
  exact normalization factorization and concrete unit-refinement capture localization are production-proved.

Outcome B — ARITHMETIC KERNEL ONLY
  raw/primitive factorization succeeds, but physical UnitCoordinateRefinement bridge has a precise unresolved blocker.

Outcome C — EXISTING ABSTRACTION SUPERSEDES DESIGN
  a better canonical repository abstraction already owns this mathematics; reuse it and report the migration path instead of duplicating it.
```

---

## Validation

Run focused builds for every new/changed production module and relevant facades.

Record in `report-003.md`:

```text
files changed
theorem inventory
exact build commands
warnings/errors
git diff --check
forbidden scan
any design deviation
whether raw refinement is now a genuine non-tautological prime transport provider
```
