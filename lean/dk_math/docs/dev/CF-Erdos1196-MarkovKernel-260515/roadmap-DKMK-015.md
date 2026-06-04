# roadmap: DKMK-015

## 0. Position

DKMK-014 closed the `k`-dependent majorant provider chapter.

The current provider chain is:

```text
increment
  -> majorant
  -> pointwise geometric majorant
  -> caller-facing base * sum ratio^k bound
  -> DyadicBandAnalyticEstimate
  -> existing route
```

The latest Lean provider is:

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
```

It consumes:

```text
base * sum (ratio ^ k) <= 1 + error
```

DKMK-015 starts the next layer:

```text
finite geometric-sum / tail-bound theorem design
```

## 1. Goal

DKMK-015 should decide how to prove or package the bound:

```text
base * sum (ratio ^ k) <= 1 + error
```

in a way that can feed:

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
```

The first goal is still theorem-shape design, not a full analytic asymptotic
estimate.

## 2. Main Questions

The chapter should answer:

```text
finite geometric sum identity をどこまで証明するか
ratio != 1 をどの theorem が消費するか
0 <= ratio, ratio < 1 をどの theorem が消費するか
tail-bound を closed form と分けるか
base を掛けた bound をどこで扱うか
```

The route layer should remain unchanged.

## 3. Candidate Theorem Layers

### Candidate 1: finite geometric-sum identity

This candidate proves the algebraic identity:

```text
sum_{k=0}^{K} ratio^k
  = (1 - ratio^(K + 1)) / (1 - ratio)
```

or an equivalent rearranged form.

Possible assumptions:

```text
ratio != 1
```

Status:

```text
algebraic layer; introduces division and ratio != 1
```

### Candidate 2: finite geometric-sum upper bound

This candidate avoids exposing equality and proves an upper bound directly.

Possible target:

```text
sum ratio^k <= 1 / (1 - ratio)
```

Possible assumptions:

```text
0 <= ratio
ratio < 1
```

Status:

```text
order layer; consumes positivity and ratio < 1
```

### Candidate 3: base-scaled bound

This candidate turns a bound on `sum ratio^k` into:

```text
base * sum ratio^k <= 1 + error
```

Possible assumptions:

```text
0 <= base
sum ratio^k <= B
base * B <= 1 + error
```

Status:

```text
scaling layer; consumes base nonnegativity if using order multiplication
```

### Candidate 4: direct caller-facing theorem

This candidate packages the whole path:

```text
ratio side conditions
tail-bound assumptions
base-scaled bound
pointwise geometric majorization
  -> DyadicBandAnalyticEstimate
```

Status:

```text
too broad for first Lean target; useful as later composition theorem
```

## 4. Design Principle

Do not introduce side conditions before a theorem consumes them.

In particular:

```text
ratio != 1:
  belongs to closed-form identity or division theorem

0 <= ratio, ratio < 1:
  belong to upper-bound or tail-bound theorem

0 <= base:
  belongs to base-scaled order theorem
```

The existing provider:

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
```

does not consume any of these side conditions.

## 5. Proposed Order

DKMK-015 should proceed in small layers.

```text
DKMK-015B:
  finite geometric-sum identity exact shape

DKMK-015C:
  optional Lean identity theorem, if the shape is light enough

DKMK-015D:
  finite geometric-sum upper-bound exact shape

DKMK-015E:
  base-scaled bound exact shape

DKMK-015F:
  connection back to geomSumBound provider
```

This sequence keeps algebra, order, scaling, and provider connection separate.

## 6. Non-goals

DKMK-015A should not:

- change `DyadicBandAnalyticEstimate`;
- change the route theorem;
- introduce Mertens or big-O;
- introduce logarithmic thresholds;
- introduce real-to-Nat rounding;
- prove a full dyadic tail estimate;
- add a broad all-in-one theorem.

## 7. Verification Plan

For docs-only steps:

```text
git diff --check
long-line check on changed docs files
```

For Lean steps:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
```

## 8. Next Step

The next concrete step should be DKMK-015B:

```text
finite geometric-sum identity exact shape review
```

It should decide whether the first closed-form theorem is an equality theorem,
a denominator-cleared identity, or an upper-bound theorem that avoids equality.

## 9. DKMK-015B Finite Geometric-Sum Identity Exact Shape

DKMK-015B fixes the first finite geometric-sum identity shape.

The first theorem should be a denominator-cleared identity, not the division
form.

### Chosen identity

Use:

```lean
geomSum_range_mul_one_sub
```

Expected shape:

```lean
lemma geomSum_range_mul_one_sub
    (ratio : R) (K : Nat) :
    (1 - ratio) *
      (Finset.sum (Finset.range (K + 1))
        (fun k : Nat => ratio ^ k))
      =
    1 - ratio ^ (K + 1)
```

Lean implementation may use `R = Real` first, or a generic commutative ring if
the existing library theorem is already generic and convenient.

### Why denominator-cleared first

The division form:

```text
sum ratio^k = (1 - ratio^(K + 1)) / (1 - ratio)
```

requires:

```text
ratio != 1
```

because it divides by `1 - ratio`.

The denominator-cleared form:

```text
(1 - ratio) * sum ratio^k = 1 - ratio^(K + 1)
```

does not require `ratio != 1`.

This matches the DKMK-015 design principle:

```text
side conditions appear only in the theorem that consumes them
```

### Later division form

The division theorem should be a later theorem:

```lean
lemma geomSum_range_eq_div_one_sub
    {ratio : R} (hr : ratio != 1) (K : Nat) :
    Finset.sum (Finset.range (K + 1))
      (fun k : Nat => ratio ^ k)
      =
    (1 - ratio ^ (K + 1)) / (1 - ratio)
```

This later theorem is the first place that should consume `ratio != 1`.

### Later order layer

The upper-bound theorem should also be separate:

```lean
lemma geomSum_range_le_inv_one_sub
    {ratio : R} (hr0 : 0 <= ratio) (hr1 : ratio < 1) (K : Nat) :
    Finset.sum (Finset.range (K + 1))
      (fun k : Nat => ratio ^ k)
      <=
    1 / (1 - ratio)
```

This later theorem is the first place that should consume:

```text
0 <= ratio
ratio < 1
```

### Connection to DKMK-014J

DKMK-014J already accepts:

```text
base * sum ratio^k <= 1 + error
```

DKMK-015B does not yet prove this bound.  It only fixes the algebraic identity
that later division and order theorems may use.

### Non-goals

DKMK-015B is docs-only.  It does not add:

- Lean code;
- a division-form theorem;
- `ratio != 1`;
- order assumptions such as `0 <= ratio` or `ratio < 1`;
- base-scaled bounds;
- route theorem changes;
- Mertens or big-O;
- logarithmic thresholds;
- real-to-Nat rounding.

## 10. DKMK-015C Lean Denominator-Cleared Identity

DKMK-015C adds:

```lean
geomSum_range_mul_one_sub
```

The theorem is the Real specialization of the denominator-cleared finite
geometric-sum identity:

```lean
(1 - ratio) *
  (Finset.sum (Finset.range (K + 1))
    (fun k : Nat => ratio ^ k))
  =
1 - ratio ^ (K + 1)
```

The implementation uses the existing mathlib theorem:

```lean
mul_neg_geom_sum
```

with `n := K + 1`.

This confirms that the first algebraic identity layer is light enough to keep
as a local wrapper in `SourceMassTruncation.lean`.

This step does not add:

- a division-form theorem;
- `ratio != 1`;
- order assumptions such as `0 <= ratio` or `ratio < 1`;
- base-scaled bounds;
- route theorem changes;
- Mertens or big-O;
- logarithmic thresholds;
- real-to-Nat rounding.

## 11. DKMK-015D Finite Geometric-Sum Upper-Bound Exact Shape

DKMK-015D fixes the first order theorem shape.

The next theorem should be an upper-bound theorem, not a division-form equality.

### Chosen theorem

Use:

```lean
geomSum_range_le_one_div_one_sub
```

Expected shape:

```lean
theorem geomSum_range_le_one_div_one_sub
    {ratio : R} (K : Nat)
    (hr0 : 0 <= ratio)
    (hr1 : ratio < 1) :
    Finset.sum (Finset.range (K + 1))
      (fun k : Nat => ratio ^ k)
      <=
    1 / (1 - ratio)
```

Lean implementation should use `R = Real` first, matching the current local
wrapper `geomSum_range_mul_one_sub`.

### Why upper-bound before division form

The downstream provider chain needs:

```text
base * sum ratio^k <= 1 + error
```

not a closed-form equality.

The denominator-cleared identity from DKMK-015C can support the bound directly:

```text
(1 - ratio) * sum ratio^k = 1 - ratio^(K + 1)
```

Under:

```text
0 <= ratio
ratio < 1
```

we have:

```text
0 <= ratio^(K + 1)
0 < 1 - ratio
1 - ratio^(K + 1) <= 1
```

so the finite sum is bounded by:

```text
1 / (1 - ratio)
```

This path may avoid introducing a separate division-form equality theorem.

### Side conditions consumed here

This is the first theorem in DKMK-015 that should consume:

```text
0 <= ratio
ratio < 1
```

It should not require:

```text
ratio != 1
```

as an explicit assumption, because `ratio < 1` already implies `1 - ratio > 0`
for the order argument.

### Later base-scaled layer

The next theorem should scale this bound by `base`:

```lean
theorem base_mul_geomSum_range_le_of_base_mul_one_div_le
    {base ratio error : R} (K : Nat)
    (hbase : 0 <= base)
    (hr0 : 0 <= ratio)
    (hr1 : ratio < 1)
    (hbudget : base * (1 / (1 - ratio)) <= 1 + error) :
    base *
      Finset.sum (Finset.range (K + 1))
        (fun k : Nat => ratio ^ k)
      <=
    1 + error
```

This later theorem is the first place that should consume `0 <= base`.

### Non-goals

DKMK-015D is docs-only.  It does not add:

- Lean code;
- a division-form equality theorem;
- explicit `ratio != 1`;
- base-scaled bounds;
- route theorem changes;
- Mertens or big-O;
- logarithmic thresholds;
- real-to-Nat rounding.

## 12. DKMK-015E Lean Geometric-Sum Upper Bound

DKMK-015E implements the theorem shape fixed in DKMK-015D.

Added theorem:

```lean
theorem geomSum_range_le_one_div_one_sub
    {ratio : Real} (K : Nat)
    (hr0 : 0 <= ratio)
    (hr1 : ratio < 1) :
    Finset.sum (Finset.range (K + 1))
      (fun k : Nat => ratio ^ k)
      <=
    1 / (1 - ratio)
```

The Lean implementation is in:

```text
DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
```

### Proof route

The proof uses the denominator-cleared identity from DKMK-015C:

```text
(1 - ratio) * sum ratio^k = 1 - ratio^(K + 1)
```

Then it uses:

```text
0 <= ratio^(K + 1)
1 - ratio^(K + 1) <= 1
0 < 1 - ratio
```

to derive:

```text
(1 - ratio) * sum ratio^k <= 1
```

Finally, `le_div_iff₀` moves the positive denominator to the right-hand side:

```text
sum ratio^k <= 1 / (1 - ratio)
```

### Side-condition behavior

This theorem consumes:

```text
0 <= ratio
ratio < 1
```

It does not add an explicit:

```text
ratio != 1
```

because the required denominator positivity is supplied by `ratio < 1`.

### Verification

The implementation was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
```

### Non-goals

DKMK-015E does not add:

- a division-form equality theorem;
- base-scaled bounds;
- route theorem changes;
- Mertens or big-O;
- logarithmic thresholds;
- real-to-Nat rounding.

## 13. DKMK-015F Lean Base-Scaled Geometric-Sum Bound

DKMK-015F implements the base-scaled provider-facing bound suggested after
DKMK-015E.

Added theorem:

```lean
theorem base_mul_geomSum_range_le_of_base_mul_one_div_le
    {base ratio error : Real} (K : Nat)
    (hbase : 0 <= base)
    (hr0 : 0 <= ratio)
    (hr1 : ratio < 1)
    (hbudget : base * (1 / (1 - ratio)) <= 1 + error) :
    base *
      Finset.sum (Finset.range (K + 1))
        (fun k : Nat => ratio ^ k)
      <=
    1 + error
```

The Lean implementation is in:

```text
DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
```

### Proof route

The proof first invokes the upper-bound theorem from DKMK-015E:

```text
sum ratio^k <= 1 / (1 - ratio)
```

Then it multiplies the inequality by the nonnegative `base`:

```text
base * sum ratio^k <= base * (1 / (1 - ratio))
```

Finally, it composes this scaled bound with the caller-supplied budget:

```text
base * (1 / (1 - ratio)) <= 1 + error
```

### Side-condition behavior

This theorem consumes:

```text
0 <= base
0 <= ratio
ratio < 1
```

It does not add:

```text
ratio != 1
```

because denominator positivity is still supplied by `ratio < 1` through the
DKMK-015E theorem.

### Verification

The implementation was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
```

### Non-goals

DKMK-015F does not add:

- a division-form equality theorem;
- route theorem changes;
- Mertens or big-O;
- logarithmic thresholds;
- real-to-Nat rounding.

## 14. DKMK-015G Dyadic Provider Connection Shape Review

DKMK-015G fixes the next connection step without adding Lean code.

DKMK-015F provides the Real-side budget theorem:

```lean
base_mul_geomSum_range_le_of_base_mul_one_div_le
```

The existing DKMK-014J provider consumes the finite-sum bound directly:

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
```

The next theorem should connect these two layers.

### Existing provider shape

The existing provider has rational `base` and `ratio`:

```lean
theorem DyadicBandAnalyticEstimate
    .ofPointwiseGeometricMajorant_of_geomSumBound
    (x K : Nat)
    (increment : Nat -> Rat)
    (base ratio : Rat)
    (hinc_nonneg :
      forall k in Finset.range (K + 1), 0 <= increment k)
    (hgeom :
      forall k in Finset.range (K + 1), increment k <= base * ratio ^ k)
    {error : Real}
    (hgeom_sum_bound :
      ((base * Finset.sum (Finset.range (K + 1))
          (fun k : Nat => ratio ^ k) : Rat) : Real) <=
        1 + error) :
    DyadicBandAnalyticEstimate x K increment error
```

This is already the correct low-level provider.

### Chosen next theorem

The next theorem should be a convenience wrapper:

```lean
theorem DyadicBandAnalyticEstimate
    .ofPointwiseGeometricMajorant_of_baseGeomBudget
    (x K : Nat)
    (increment : Nat -> Rat)
    (base ratio : Rat)
    (hinc_nonneg :
      forall k in Finset.range (K + 1), 0 <= increment k)
    (hgeom :
      forall k in Finset.range (K + 1), increment k <= base * ratio ^ k)
    (hbase : 0 <= (base : Real))
    (hr0 : 0 <= (ratio : Real))
    (hr1 : (ratio : Real) < 1)
    {error : Real}
    (hbudget : (base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error) :
    DyadicBandAnalyticEstimate x K increment error
```

The theorem name should be:

```lean
ofPointwiseGeometricMajorant_of_baseGeomBudget
```

This keeps the public caller-facing name shorter than
`ofPointwiseGeometricMajorant_of_baseOneDivOneSubBound`, while the docs explain
that the budget is `base * (1 / (1 - ratio)) <= 1 + error`.

### Proof route for the later Lean implementation

The theorem should:

1. call `base_mul_geomSum_range_le_of_base_mul_one_div_le` with
   `(base : Real)` and `(ratio : Real)`;
2. convert the resulting Real finite-sum bound back to the shape expected by
   `ofPointwiseGeometricMajorant_of_geomSumBound`;
3. call `ofPointwiseGeometricMajorant_of_geomSumBound`.

The main implementation boundary is the coercion identity:

```text
((base * sum (fun k => ratio ^ k) : Rat) : Real)
=
(base : Real) * sum (fun k => (ratio : Real) ^ k)
```

This should be handled locally in the connection theorem.

### Type-boundary decision

Keep the provider theorem in the `Rat`-increment layer, because
`DyadicBandAnalyticEstimate` is currently rational-valued.

Keep the geometric-budget theorem in the `Real` layer, because DKMK-015C-F
already use `Real` and the downstream `error` target is `Real`.

The connection theorem is therefore the correct place to pay the cast cost.

### Non-goals

DKMK-015G does not add:

- Lean code;
- a new provider structure;
- a duplicate of `ofPointwiseGeometricMajorant_of_geomSumBound`;
- a division-form equality theorem;
- route theorem changes;
- Mertens or big-O;
- logarithmic thresholds;
- real-to-Nat rounding.

## 15. DKMK-015H Lean Dyadic Provider Connection

DKMK-015H implements the connection theorem fixed in DKMK-015G.

Added theorem:

```lean
theorem DyadicBandAnalyticEstimate
    .ofPointwiseGeometricMajorant_of_baseGeomBudget
    (x K : Nat)
    (increment : Nat -> Rat)
    (base ratio : Rat)
    (hinc_nonneg :
      forall k in Finset.range (K + 1), 0 <= increment k)
    (hgeom :
      forall k in Finset.range (K + 1), increment k <= base * ratio ^ k)
    (hbase : 0 <= (base : Real))
    (hr0 : 0 <= (ratio : Real))
    (hr1 : (ratio : Real) < 1)
    {error : Real}
    (hbudget : (base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error) :
    DyadicBandAnalyticEstimate x K increment error
```

The Lean implementation is in:

```text
DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
```

### Proof route

The proof first builds the Real-side provider-facing bound:

```text
(base : Real) * sum ((ratio : Real) ^ k) <= 1 + error
```

using:

```lean
base_mul_geomSum_range_le_of_base_mul_one_div_le
```

Then it closes the rational-to-real finite-sum cast boundary locally:

```text
((base * sum (fun k => ratio ^ k) : Rat) : Real)
=
(base : Real) * sum (fun k => (ratio : Real) ^ k)
```

This cast identity closes by `simp`.

Finally, it invokes the existing DKMK-014J provider:

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound
```

### Resulting caller path

Callers can now provide:

```text
base * (1 / (1 - ratio)) <= 1 + error
```

over `Real`, together with the pointwise rational geometric majorant, and get:

```lean
DyadicBandAnalyticEstimate x K increment error
```

This completes the connection from DKMK-015 finite geometric-sum estimates to
the existing DKMK-014J dyadic provider route.

### Verification

The implementation was checked with:

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
```

### Non-goals

DKMK-015H does not add:

- a new provider structure;
- a duplicate low-level provider;
- a division-form equality theorem;
- route theorem changes beyond the connection wrapper;
- Mertens or big-O;
- logarithmic thresholds;
- real-to-Nat rounding.

## 16. DKMK-015I Chapter Summary And Next Budget Source

DKMK-015I closes the finite geometric-sum / provider connection chapter as a
docs-only summary.

The chapter report is:

```text
report-DKMK-015.md
```

### Completed route

DKMK-015 now provides the route:

```text
geometric budget
  -> finite geometric-sum bound
  -> base-scaled finite-sum bound
  -> dyadic source-mass provider
```

The public Lean surfaces added in this chapter are:

```text
geomSum_range_mul_one_sub
geomSum_range_le_one_div_one_sub
base_mul_geomSum_range_le_of_base_mul_one_div_le
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_baseGeomBudget
```

The practical caller path is:

```text
hinc_nonneg
hgeom : increment k <= base * ratio^k
hbase : 0 <= (base : Real)
hr0   : 0 <= (ratio : Real)
hr1   : (ratio : Real) < 1
hbudget : (base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error
  -> DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_baseGeomBudget
  -> DyadicBandAnalyticEstimate
  -> existing finite-step route
```

### Next route question

The next chapter should focus on the source of:

```text
(base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error
```

This is now the main remaining abstract budget obligation.

The next work should decide whether this budget is supplied by:

- an abstract budget provider;
- concrete choices of `base` and `ratio`;
- a log-capacity / dyadic-band analytic estimate;
- or a staged route that first packages the budget and only later refines it.

### Non-goals

DKMK-015I does not add:

- Lean code;
- new theorem statements;
- a division-form equality theorem;
- explicit `ratio != 1`;
- Mertens or big-O;
- logarithmic thresholds;
- real-to-Nat rounding.
