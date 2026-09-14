# review-004 — MG-003B raw-refinement path review

cid: `6aa763a7-1a14-83e8-9041-1029d978663c`

## Verdict

**APPROVED — Outcome A confirmed.**

MG-003B completes the synchronized common-scale side of the MultiGauge front half.

Production now proves both of the intended structural facts:

```text
positive synchronized scaleBy
-> primitive coprime shape is invariant;

initial raw escape
+ every refinement factor avoids q
-> q escapes at every visited raw stage.
```

It also proves the complementary localization:

```text
initial raw escape
+ capture at some visited stage
-> some actual refinement factor k satisfies q | k.
```

No repair is required before the next checkpoint.

---

## What is now genuinely established

For a raw stage `s` and positive `k`, production proves:

```text
scale (scaleBy k s) = k * scale s
primitiveStage (scaleBy k s) = primitiveStage s
```

under the explicit positive-scale hypotheses.

Thus synchronized refinement changes only common scale support; it does not change the normalized primitive `(x,u)` shape.

For a finite path with factors `k₁,...,k_r`, production also proves:

```text
endStage = scaleBy (product factors) start

endStage.value
  = (product factors)^d * start.value.
```

This is the concrete finite-chain realization of the original research question for common-scale unit refinement.

---

## Prime-escape interpretation

For prime `q`:

```text
RawPrimeEscapes q start
and
forall k in factors, not q | k
```

implies raw escape at every visited stage.

Conversely, if a visited stage is captured after initial escape, an actual listed refinement factor is divisible by `q`.

Therefore the common-scale answer is now exact:

```text
q cannot become newly visible merely because the unit is refined.
A new raw capture can occur only when q enters the common refinement scale.
```

This is stronger and more concrete than the earlier abstract `GNGaugeTransition` path result because the support factor is now supplied by actual synchronized unit-refinement semantics.

---

## API note — adjacency wording

`GNRawRefinementPath.exists_escape_to_capture_step` is mathematically sound for the intended factor-localization use.

Its recursive proof chooses a genuine adjacent refinement step. However, the exported conclusion records only:

```text
s₀ ∈ p.stages
k ∈ p.factors
RawPrimeEscapes q s₀
q | k
RawPrimeCaught q (scaleBy k s₀)
```

and does not encode, as a separate path-order relation, that this occurrence of `k` is the list edge immediately following this occurrence of `s₀`.

Consequences:

```text
- current factor-localization theorems are fully justified;
- do not use this API later as an indexed "first edge" certificate without strengthening it;
- add an indexed/edge packet only if a downstream theorem actually needs order/uniqueness.
```

This is not a blocker for MG-003B.

---

## Architecture after MG-003B

The gauge theory is now cleanly split into two independent mechanisms:

```text
RAW COMMON SCALE
  (x,u) -> (k*x,k*u)
  primitive shape unchanged
  new support localized to k

PRIMITIVE SHAPE
  (x₁,u₁) -> (x₂,u₂)
  both pairs coprime
  requires an independently meaningful GNGaugeTransition balance
```

The first mechanism is now production-complete for finite paths.

The second mechanism still lacks a concrete provider.

---

## Next decision

Proceed to **MG-003C — primitive-shape transition provider audit**.

Do not build MG-002 channel-state machinery yet. A channel automaton becomes useful only after at least one real primitive-shape transition is available.

The MG-003C pass must be audit-first and is allowed to end with no new Lean production theorem if all apparent providers are conditional/open/tautological.
