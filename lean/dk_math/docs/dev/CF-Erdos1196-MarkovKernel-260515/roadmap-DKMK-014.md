# roadmap: DKMK-014

## 0. Position

DKMK-013 closed the abstract dyadic analytic estimate contract chapter.

The current analytic-to-route flow is:

```text
DyadicBandAnalyticEstimate
  -> DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate
  -> existing DKMK-011 route theorem
  -> weightedHitMass <= 1 + error
```

DKMK-013 also added the first constant-band providers:

```text
DyadicBandAnalyticEstimate.constantBand
DyadicBandAnalyticEstimate.constantBand_of_natCastMulBound
```

DKMK-014 starts the next analytic-provider design layer:

```text
k-dependent decreasing / dyadic tail provider design
```

## 1. Goal

DKMK-014 should decide how to produce:

```lean
DyadicBandAnalyticEstimate x K increment error
```

when `increment` depends on the band index `k`.

The first goal is still a theorem-facing interface, not a Mertens theorem or a
final asymptotic estimate.

## 2. Main Questions

The chapter should answer:

```text
increment k をどう設計するか
非負性をどう出すか
有限 total estimate をどう外部化するか
monotonicity / decay assumptions をどこまで持たせるか
```

The route layer should remain unchanged.

## 3. Candidate Provider Shapes

### Candidate 1: externally supplied k-dependent estimate

This is the direct analogue of the current contract fields.

Data:

```text
x         : Nat
K         : Nat
increment : Nat -> Q
error     : R
```

Proof input:

```text
hinc:
  forall k in Finset.range (K + 1), 0 <= increment k

hbound:
  ((Finset.sum (Finset.range (K + 1)) increment : Q) : R) <=
    1 + error
```

Target:

```lean
DyadicBandAnalyticEstimate x K increment error
```

Status:

```text
essentially constructor-level; useful as API baseline
```

### Candidate 2: decreasing band provider

This candidate adds a decreasing or monotone condition.

Possible data:

```text
x         : Nat
K         : Nat
increment : Nat -> Q
error     : R
```

Possible assumptions:

```text
nonnegativity:
  forall k in Finset.range (K + 1), 0 <= increment k

monotonicity:
  for relevant k, increment (k + 1) <= increment k

total bound:
  finite sum <= 1 + error
```

Status:

```text
design candidate; monotonicity should be included only if consumed
```

The key question is whether monotonicity helps produce `hinc` or `hbound`.
If it is only descriptive, it should not be a field yet.

### Candidate 3: majorant envelope provider

This candidate separates the actual increment from an upper envelope.

Possible data:

```text
increment : Nat -> Q
majorant  : Nat -> Q
error     : R
```

Possible assumptions:

```text
0 <= increment k
increment k <= majorant k
sum majorant <= 1 + error
```

Target:

```text
sum increment <= 1 + error
```

Status:

```text
promising for future dyadic tail estimates, but may need sum comparison lemmas
```

### Candidate 4: dyadic tail upper envelope

This is the main analytic direction.

The provider should eventually express:

```text
each dyadic band contribution is bounded by increment k
sum over k <= 1 + error
```

Status:

```text
main DKMK-014 direction, but not first Lean target
```

### Candidate 5: logarithmic refinement

This remains deferred.

Reason:

```text
logarithmic thresholds require real-to-Nat rounding,
Real.log / Real.exp infrastructure,
and additional comparison lemmas.
```

## 4. Design Principle

Do not add assumptions just because they are mathematically natural.

Only add a field if a later theorem consumes it.

In particular:

```text
monotonicity
decay
majorization
tail comparison
```

should remain outside the core contract until they produce either:

```text
increment_nonneg
total_le_one_add_error
```

or a bridge theorem into `DyadicBandAnalyticEstimate`.

## 5. Non-goals

DKMK-014A should not:

- change `DyadicBandAnalyticEstimate`;
- change `TruncationEnvelopeEstimate`;
- add a route theorem;
- prove a Mertens theorem;
- introduce big-O notation;
- define logarithmic thresholds;
- add real-to-Nat rounding.

## 6. Verification Plan

For docs-only steps:

```text
git diff --check
long-line check on changed docs files
```

For Lean provider steps:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
```

## 7. Next Step

The next concrete step should be DKMK-014B:

```text
decreasing / majorant provider shape review
```

It should decide whether the first non-constant provider is:

- a decreasing-band provider;
- a majorant-envelope provider;
- or another externally supplied k-dependent estimate provider.

The decision should focus on which assumptions are actually consumed to prove
`DyadicBandAnalyticEstimate`.

## 8. DKMK-014B Majorant Provider Shape

DKMK-014B fixes the first non-constant provider direction.

The first provider should be a majorant-envelope provider, not a decreasing
provider.

Reason:

```text
majorant assumptions directly produce the total estimate;
decreasing assumptions are only useful after a theorem consumes them.
```

### Chosen provider

Use:

```lean
DyadicBandAnalyticEstimate.ofMajorant
```

This theorem should build:

```lean
DyadicBandAnalyticEstimate x K increment error
```

from:

```text
increment nonnegativity
pointwise increment <= majorant
majorant total bound
```

### Expected Lean shape

```lean
theorem DyadicBandAnalyticEstimate.ofMajorant
    (x K : Nat)
    (increment majorant : Nat -> Q)
    (hinc_nonneg :
      forall k in Finset.range (K + 1), 0 <= increment k)
    (hle :
      forall k in Finset.range (K + 1), increment k <= majorant k)
    {error : R}
    (hmajorant_bound :
      ((Finset.sum (Finset.range (K + 1)) majorant : Q) : R) <=
        1 + error) :
    DyadicBandAnalyticEstimate x K increment error
```

### Proof plan

The first field is direct:

```text
increment_nonneg := hinc_nonneg
```

The second field should use Rat-side sum comparison:

```text
Finset.sum_le_sum hle
```

to prove:

```text
Finset.sum (Finset.range (K + 1)) increment
  <= Finset.sum (Finset.range (K + 1)) majorant
```

Then cast to Real and compose with:

```text
hmajorant_bound
```

The intended final route is:

```text
sum increment <= sum majorant
sum majorant <= 1 + error
therefore sum increment <= 1 + error
```

### Why not decreasing first

A decreasing condition such as:

```text
increment (k + 1) <= increment k
```

does not by itself prove:

```text
sum increment <= 1 + error
```

It should become a field only when a later theorem consumes it, for example:

```text
decreasing / decay assumption
  -> construct a majorant
  -> ofMajorant
  -> DyadicBandAnalyticEstimate
```

### Non-goals

DKMK-014B should not add:

- Lean code;
- a decreasing provider;
- route theorem changes;
- Mertens or big-O;
- logarithmic thresholds;
- real-to-Nat rounding.

### Next step

DKMK-014C should implement only:

```lean
DyadicBandAnalyticEstimate.ofMajorant
```

If Rat-to-Real cast monotonicity creates friction, keep the statement and proof
small and avoid adding extra provider fields.

## 9. DKMK-014C Lean Majorant Provider

DKMK-014C adds:

```lean
DyadicBandAnalyticEstimate.ofMajorant
```

The theorem consumes:

```text
increment nonnegativity
pointwise increment <= majorant
majorant total bound
```

and produces:

```lean
DyadicBandAnalyticEstimate x K increment error
```

The proof compares sums over `Finset.range (K + 1)` on the Rat side using
`Finset.sum_le_sum`, casts the result to Real, then composes it with
`hmajorant_bound`.

This is the first non-constant provider in the DKMK-014 chapter.

No decreasing condition, route theorem, Mertens / big-O, logarithmic threshold,
or real-to-Nat rounding is added.

## 10. DKMK-014D Majorant Provider Usage Summary

The intended usage flow for the majorant provider is:

```text
increment, majorant
  -> hinc_nonneg : 0 <= increment k on Finset.range (K + 1)
  -> hle : increment k <= majorant k on Finset.range (K + 1)
  -> hmajorant_bound : sum majorant <= 1 + error
  -> DyadicBandAnalyticEstimate.ofMajorant
  -> DyadicBandAnalyticEstimate x K increment error
  -> DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate
  -> existing finite-step route theorem
  -> weightedHitMass <= 1 + error
```

The key point is that `majorant` is the object whose finite sum is estimated.
The actual `increment` may be harder to sum directly, but it can enter the
route once it is bounded above by `majorant` on the same dyadic range.

This separates two jobs:

```text
local band control:
  increment k <= majorant k

finite analytic total estimate:
  sum majorant <= 1 + error
```

The provider consumes exactly these two jobs plus nonnegativity of `increment`.
It does not need to know why the majorant exists.

### Decreasing assumptions

A decreasing or decay assumption remains outside the core provider.

The expected future shape is:

```text
decreasing / decay input
  -> construct or justify majorant
  -> prove pointwise increment <= majorant
  -> prove sum majorant <= 1 + error
  -> ofMajorant
```

This keeps decreasing information useful only when a later theorem consumes it.

### Non-goals

DKMK-014D is docs-only.  It does not add:

- Lean code;
- a decreasing provider;
- route theorem changes;
- Mertens or big-O;
- logarithmic thresholds;
- real-to-Nat rounding.

## 11. DKMK-014E Decreasing / Decay to Majorant Design

The majorant provider chapter is now usable:

```text
increment <= majorant
sum majorant <= 1 + error
  -> DyadicBandAnalyticEstimate.ofMajorant
```

The next design question is how decreasing or decay information should help
produce the `majorant` side of this interface.

### Candidate E1: decreasing only

Data:

```text
increment (k + 1) <= increment k
0 <= increment k
```

This is not enough by itself.

It gives shape information about the sequence, but it does not produce a
finite total estimate:

```text
sum increment <= 1 + error
```

Therefore decreasing alone should not become a new provider field.

### Candidate E2: decay ratio with external total bound

Data:

```text
0 <= increment k
increment (k + 1) <= r * increment k
increment k <= majorant k
sum majorant <= 1 + error
```

Here the decay condition may justify the pointwise majorant, but the finite
sum estimate still remains external.

This is compatible with the current provider stack because the final theorem
can still call:

```lean
DyadicBandAnalyticEstimate.ofMajorant
```

### Candidate E3: explicit majorant construction theorem

This is the preferred next Lean-facing shape.

Instead of changing `DyadicBandAnalyticEstimate`, add a separate theorem that
constructs or validates a usable majorant:

```text
decreasing / decay assumptions
  -> hle : increment k <= majorant k
  -> hmajorant_bound : sum majorant <= 1 + error
  -> ofMajorant
```

The theorem may package the call to `ofMajorant`, but it should not add new
fields to the core analytic estimate.

### Boundary decision

DKMK-014E fixes this boundary:

```text
decreasing / decay:
  evidence used to build or justify a majorant

majorant:
  object whose finite sum is estimated

ofMajorant:
  bridge from pointwise majorization and total majorant bound to
  DyadicBandAnalyticEstimate
```

This keeps the current theorem small and lets future dyadic-tail estimates
specialize only the majorant-construction side.

### Non-goals

DKMK-014E is docs-only.  It does not add:

- Lean code;
- a decreasing provider theorem;
- geometric-series lemmas;
- route theorem changes;
- Mertens or big-O;
- logarithmic thresholds;
- real-to-Nat rounding.

## 12. DKMK-014F Explicit Majorant Construction Exact Shape

DKMK-014F fixes the first explicit majorant-construction theorem shape.

The theorem should not merely rename `ofMajorant`.  A theorem of the form:

```lean
DyadicBandAnalyticEstimate.ofMajorantBoundedBy
```

with the same assumptions as `ofMajorant` would add little.

The next useful provider should expose a concrete majorant family while still
keeping the finite sum estimate external.

### Chosen provider

Use:

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
```

This theorem should use the geometric-shaped majorant:

```text
majorant k = base * ratio^k
```

but it should not prove or simplify the geometric finite sum.

### Expected Lean shape

```lean
theorem DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
    (x K : Nat)
    (increment : Nat -> Q)
    (base ratio : Q)
    (hinc_nonneg :
      forall k in Finset.range (K + 1), 0 <= increment k)
    (hgeom :
      forall k in Finset.range (K + 1),
        increment k <= base * ratio^k)
    {error : R}
    (hgeom_bound :
      ((Finset.sum (Finset.range (K + 1))
          (fun k : Nat => base * ratio^k) : Q) : R) <=
        1 + error) :
    DyadicBandAnalyticEstimate x K increment error
```

### Proof plan

The proof should be a thin call to:

```lean
DyadicBandAnalyticEstimate.ofMajorant
```

with:

```lean
majorant := fun k : Nat => base * ratio^k
```

The fields are then:

```text
hinc_nonneg -> increment_nonneg
hgeom       -> pointwise increment <= majorant
hgeom_bound -> total majorant bound
```

### Why keep the sum bound external

This mirrors the DKMK-013 `constantBand` pattern.

First add the provider that accepts the finite sum bound directly.  Only later,
if useful, add a caller-facing simplification theorem for the finite geometric
sum.

The possible later theorem would be separate:

```text
geometric finite-sum assumptions
  -> sum (base * ratio^k) <= 1 + error
  -> ofPointwiseGeometricMajorant
```

### Boundary decision

DKMK-014F fixes this boundary:

```text
ofPointwiseGeometricMajorant:
  pointwise geometric majorization plus external geometric-sum bound

future geometric-sum theorem:
  proves or simplifies the external geometric-sum bound
```

This keeps DKMK-014F within provider shape design and avoids introducing
geometric-series infrastructure too early.

### Non-goals

DKMK-014F is docs-only.  It does not add:

- Lean code;
- geometric-series lemmas;
- assumptions such as `0 <= ratio` or `ratio < 1`;
- route theorem changes;
- Mertens or big-O;
- logarithmic thresholds;
- real-to-Nat rounding.

## 13. DKMK-014G Lean Pointwise Geometric Majorant Provider

DKMK-014G adds:

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
```

The theorem exposes the concrete pointwise majorant:

```lean
fun k : Nat => base * ratio ^ k
```

and consumes:

```text
increment nonnegativity
pointwise increment k <= base * ratio^k
external finite geometric-sum bound
```

The proof is a thin call to:

```lean
DyadicBandAnalyticEstimate.ofMajorant
```

with the geometric majorant supplied explicitly.

No geometric-series simplification is performed.  In particular, no assumptions
such as `0 <= ratio` or `ratio < 1` are introduced here.  Those belong to a
future theorem that proves the external geometric finite-sum bound.

## 14. DKMK-014H Geometric Majorant Usage Summary

The intended usage flow for the pointwise geometric majorant provider is:

```text
increment
  -> hinc_nonneg :
       0 <= increment k on Finset.range (K + 1)
  -> hgeom :
       increment k <= base * ratio ^ k on Finset.range (K + 1)
  -> hgeom_bound :
       sum (base * ratio ^ k) <= 1 + error
  -> DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
  -> DyadicBandAnalyticEstimate x K increment error
  -> DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate
  -> TruncationEnvelopeEstimate
  -> existing finite-step route theorem
  -> weightedHitMass <= 1 + error
```

The theorem has three jobs:

```text
nonnegativity:
  hinc_nonneg

pointwise geometric control:
  hgeom

finite total estimate:
  hgeom_bound
```

Only the second job is specific to the geometric shape.  The finite total
estimate remains external.

### Why the finite-sum bound is still external

`ofPointwiseGeometricMajorant` does not prove:

```text
sum (base * ratio ^ k) <= 1 + error
```

It only consumes that estimate.

This keeps the provider independent of the analytic side conditions needed to
prove a geometric finite-sum estimate, such as:

```text
0 <= base
0 <= ratio
ratio < 1
closed-form finite geometric sum
tail estimate
```

Those assumptions should appear only in a later theorem that actually proves
`hgeom_bound`.

### Next theorem boundary

The next possible caller-facing theorem should have the shape:

```text
geometric finite-sum assumptions
  -> hgeom_bound :
       sum (base * ratio ^ k) <= 1 + error
  -> ofPointwiseGeometricMajorant
```

That theorem may introduce ratio assumptions or finite geometric-sum lemmas.
It should remain separate from the current provider.

### Non-goals

DKMK-014H is docs-only.  It does not add:

- Lean code;
- geometric-series lemmas;
- assumptions such as `0 <= ratio` or `ratio < 1`;
- route theorem changes;
- Mertens or big-O;
- logarithmic thresholds;
- real-to-Nat rounding.

## 15. DKMK-014I Geometric Sum-Bound Theorem Exact Shape

DKMK-014I fixes the first caller-facing geometric finite-sum theorem shape.

The theorem should not repeat the existing provider with the same
`hgeom_bound`.  Its job is to accept a slightly more caller-friendly finite-sum
bound:

```text
base * sum (ratio ^ k) <= 1 + error
```

and convert it to the bound consumed by:

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
```

### Chosen provider

Use:

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
```

This theorem should still keep the finite geometric sum unevaluated.

### Expected Lean shape

```lean
theorem DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
    (x K : Nat)
    (increment : Nat -> Q)
    (base ratio : Q)
    (hinc_nonneg :
      forall k in Finset.range (K + 1), 0 <= increment k)
    (hgeom :
      forall k in Finset.range (K + 1),
        increment k <= base * ratio ^ k)
    {error : R}
    (hgeom_sum_bound :
      ((base * Finset.sum (Finset.range (K + 1))
          (fun k : Nat => ratio ^ k) : Q) : R) <=
        1 + error) :
    DyadicBandAnalyticEstimate x K increment error
```

### Proof plan

The proof should first rewrite:

```text
sum (fun k => base * ratio ^ k)
```

to:

```text
base * sum (fun k => ratio ^ k)
```

on the Rat side, then call:

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
```

The expected Lean ingredient is a finite-sum distribution lemma such as:

```text
Finset.mul_sum
```

or an equivalent `simpa` over `Finset.sum_mul`.

### Why this is the first finite-sum theorem

This theorem does not prove the closed form:

```text
base * (1 - ratio^(K + 1)) / (1 - ratio)
```

It only moves the constant `base` outside the finite sum.

That is the smallest useful caller-facing step after
`ofPointwiseGeometricMajorant`, and it does not require:

```text
0 <= base
0 <= ratio
ratio < 1
ratio != 1
```

Those assumptions belong to later closed-form or tail-bound theorems.

### Boundary decision

DKMK-014I fixes this boundary:

```text
ofPointwiseGeometricMajorant_of_geomSumBound:
  accepts base * sum ratio^k <= 1 + error
  rewrites it to sum (base * ratio^k) <= 1 + error

future closed-form theorem:
  proves or bounds sum ratio^k itself
```

This keeps DKMK-014I at the algebraic finite-sum factoring layer.

### Non-goals

DKMK-014I is docs-only.  It does not add:

- Lean code;
- closed-form finite geometric-sum lemmas;
- tail-bound lemmas;
- assumptions such as `0 <= ratio`, `ratio < 1`, or `ratio != 1`;
- route theorem changes;
- Mertens or big-O;
- logarithmic thresholds;
- real-to-Nat rounding.
