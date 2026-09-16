# Codex Instruction — GNPC-002 Positive GN Finite Representation Bounds / Complete Search Box

Branch: `wip/number-theory-gn-prime-closure-260901-v0`

Project: DkMath NumberTheory GN Prime Closure

Start from current GNPC-001 implementation commit:

```text
4cd741195b58bef30e777360406b5fd96ae8b648
```

Read first:

```text
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/README.md
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-001.md
lean/dk_math/DkMath/NumberTheory/GNPrimeClosure.lean
```

---

# 0. Current verified state

GNPC-001 is complete.

The branch already exposes the elementary prime-product closure

```lean
DkMath.NumberTheory.prime_boundary_mul_GN_iff
DkMath.NumberTheory.prime_boundary_mul_GN_iff_boundary_eq_one_of_GN_prime
```

for the canonical

```lean
DkMath.CosmicFormulaBinom.GN
```

with no new `sorry` or `axiom`.

GNPC-002 does **not** extend the prime-product proof.

Instead, it formalizes the finite representation region for positive,
nondegenerate GN coordinates.

The key change of viewpoint is:

> Fix the target value `n`.  Before asking whether `n` is prime, prove that all
> positive GN representations `GN d x u = n` lie in an explicitly bounded
> finite search region.

This is stronger and more reusable than a theorem specialized to prime targets.

---

# 1. Mathematical target

The canonical GN expansion is

$$
GN_d(x,u)=\sum_{k=0}^{d-1}\binom{d}{k+1}x^k u^{d-1-k}.
$$

In the positive nondegenerate region

```text
2 ≤ d
0 < x
0 < u
```

all summands are nonnegative and the endpoint terms are

$$
d\,u^{d-1}
$$

and

$$
x^{d-1}.
$$

The positive integer point `(1,1)` gives the degree floor

$$
GN_d(1,1)=2^d-1.
$$

Therefore every positive representation

$$
GN_d(x,u)=n
$$

must satisfy at least

$$
2^d-1\le n,
$$

$$
x^{d-1}<n,
$$

and

$$
d\,u^{d-1}<n.
$$

A coarse but very useful consequence is

$$
d<n,\qquad x<n,\qquad u<n.
$$

Thus every positive representation of a fixed target `n` lies in a finite
`n × n × n` coordinate box.

The purpose of GNPC-002 is to make this statement executable and reusable in Lean.

---

# 2. Mandatory reconnaissance

Before editing Lean source, search current DkMath and Mathlib for exact or near
duplicates.  Record the result in `report-002.md`.

Search at least for:

```text
GN_eq_sum
GN_tail_rec
GN_tail_decomposition
GN d 1 1
2 ^ d - 1
one_le_GN_nat_of_two_le
xpow_lt_bodyN_nat_of_two_le
GN monotone
Monotone GN
pow monotone Nat
sum_choose
add_pow
```

Known nearby DkMath anchors include:

```text
DkMath.CosmicFormulaBinom.GN
DkMath.CosmicFormulaBinom.GN_eq_sum
DkMath.CosmicFormulaBinom.one_le_GN_nat_of_two_le
DkMath.CosmicFormulaBinom.xpow_lt_bodyN_nat_of_two_le
DkMath.CosmicFormula.GN_tail_rec
```

Do not assume the names above are sufficient for the final proof.  Re-check
current source and use the lightest existing API.

If any requested theorem already exists under another name, reuse it and add
only the missing facade/corollary.

---

# 3. Preferred ownership

Prefer a new thin NumberTheory module:

```text
DkMath/NumberTheory/GNRepresentationBounds.lean
```

Do not put these representation-space theorems into `GNPrimeClosure.lean`
unless source inspection shows a compelling reason.

The new module should depend only on the canonical GN algebra and the minimum
Mathlib arithmetic needed for the bounds.

Avoid importing ABC, FLT, Legendre, Primitive, Zsigmondy, cyclotomic, valuation,
or other application layers.

---

# 4. Required theorem surface

Declaration names below are preferred, not mandatory.  Preserve mathematical
content even if a nearby existing name suggests a better local convention.
Report all final names.

## GNPC-002-A. Positive representation predicate

Introduce a reusable predicate for the nondegenerate positive region.

Preferred shape:

```lean
def GNPositiveRepresentation (n d x u : ℕ) : Prop :=
  2 ≤ d ∧
  0 < x ∧
  0 < u ∧
  DkMath.CosmicFormulaBinom.GN d x u = n
```

A structure is acceptable only if it materially improves the later finite
enumeration API.  Do not over-engineer the representation type.

The distinction from degenerate coordinates is intentional:

```text
d ≤ 1
x = 0
u = 0
```

are outside this predicate.

Do not try to classify those degenerate cases in this checkpoint.

---

## GNPC-002-B. Exact minimum anchor at `(1,1)`

Prove or expose the exact identity

```lean
theorem GN_one_one_eq_two_pow_sub_one (d : ℕ) :
    DkMath.CosmicFormulaBinom.GN d 1 1 = 2 ^ d - 1
```

Equivalent naming is fine.

This theorem should be valid for all natural `d` if the canonical definition
permits it.  Do not unnecessarily add `2 ≤ d` unless Lean/source behavior
actually requires it.

Prefer an existing binomial-sum identity if available.  Avoid introducing a
heavy dependency merely to rewrite the Cosmic Formula Body.

---

## GNPC-002-C. Positive degree floor

Prove that `(1,1)` is a lower anchor for positive natural coordinates.

Preferred theorem:

```lean
theorem two_pow_sub_one_le_GN
    {d x u : ℕ}
    (hx : 0 < x) (hu : 0 < u) :
    2 ^ d - 1 ≤ DkMath.CosmicFormulaBinom.GN d x u
```

A thin monotonicity theorem for GN is welcome if it is the natural reusable
proof route, for example coordinatewise monotonicity over `ℕ`.

However, do not turn GNPC-002 into a general ordered-semiring monotonicity
refactor.  The required output is the natural-number lower bound.

---

## GNPC-002-D. Endpoint lower bound

Expose the two endpoint contributions of the positive GN polynomial.

Preferred strongest form:

```lean
theorem boundary_pow_add_head_le_GN
    {d x u : ℕ}
    (hd : 2 ≤ d) :
    x ^ (d - 1) + d * u ^ (d - 1) ≤
      DkMath.CosmicFormulaBinom.GN d x u
```

For `d = 2`, this is equality; for higher degree the mixed terms provide the
remaining nonnegative mass.

If the combined inequality is disproportionately awkward because of current
`Finset` indexing, it is acceptable to expose both endpoint inequalities
separately, **provided the strict target bounds in the next section are still
proved**.

Do not weaken the checkpoint to `1 ≤ GN` only.

Useful existing proof routes may include:

```text
GN_eq_sum
GN_tail_rec
GTail endpoint/head decomposition
```

Choose the route with the smallest dependency surface.

---

## GNPC-002-E. Strict coordinate power bounds

Derive strict inequalities in the positive nondegenerate region.

Preferred shapes:

```lean
theorem boundary_pow_lt_GN
    {d x u : ℕ}
    (hd : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) :
    x ^ (d - 1) < DkMath.CosmicFormulaBinom.GN d x u
```

```lean
theorem head_lt_GN
    {d x u : ℕ}
    (hd : 2 ≤ d) (hx : 0 < x) (hu : 0 < u) :
    d * u ^ (d - 1) < DkMath.CosmicFormulaBinom.GN d x u
```

Some hypotheses may be logically unnecessary for one direction.  A weaker,
cleaner assumption surface is acceptable if verified.

The intended meaning is that, once both positive endpoint channels exist, each
individual endpoint is strictly below the total GN value.

---

## GNPC-002-F. Target-dependent bounds for a representation

For

```lean
h : GNPositiveRepresentation n d x u
```

prove the three principal target bounds:

```text
2^d - 1 ≤ n
x^(d-1) < n
d * u^(d-1) < n
```

Then derive the coarse coordinate bounds:

```text
d < n
x < n
u < n
```

Preferred packaged theorem:

```lean
theorem GNPositiveRepresentation.bounds
    {n d x u : ℕ}
    (h : GNPositiveRepresentation n d x u) :
    2 ^ d - 1 ≤ n ∧
    x ^ (d - 1) < n ∧
    d * u ^ (d - 1) < n ∧
    d < n ∧
    x < n ∧
    u < n
```

It is fine to expose the individual lemmas first and package them afterward.
Individual named bounds may be more ergonomic for later search code.

Do **not** introduce logarithms, natural roots, or floating-point approximations
merely to rewrite `2^d - 1 ≤ n` as a logarithmic bound.  The power inequality is
already exact, decidable, and suitable for finite filtering.

---

## GNPC-002-G. Explicit finite search box

Turn the coarse bounds into an executable finite container.

A simple representation is sufficient:

```lean
def GNRepresentationBox (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (Finset.range n).product
    ((Finset.range n).product (Finset.range n))
```

Then define the filtered exact representation set, for example:

```lean
def GNPositiveRepresentations (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (GNRepresentationBox n).filter fun t =>
    GNPositiveRepresentation n t.1 t.2.1 t.2.2
```

Exact tuple shape and names may vary.

The important theorem is completeness:

```lean
theorem mem_GNPositiveRepresentations_iff
    {n d x u : ℕ} :
    (d, (x, u)) ∈ GNPositiveRepresentations n ↔
      GNPositiveRepresentation n d x u
```

The reverse implication must use the proved bounds `d < n`, `x < n`, `u < n`.
This theorem is the formal statement that the finite search box loses no
positive GN representations.

If a direct `Finset` formulation becomes syntactically noisy, an equivalent
finite-set theorem plus a thin executable `Finset` wrapper is acceptable.  But
GNPC-002 should end with an explicit finite/executable representation surface,
not only informal boundedness.

---

## GNPC-002-H. Thin prime specialization

The main bounds are target-general and must not require primality.

At the end, optionally expose the prime-target vocabulary needed by later
GNPC checkpoints:

```lean
def GNPrimeRepresentation (p d x u : ℕ) : Prop :=
  Nat.Prime p ∧ GNPositiveRepresentation p d x u
```

A thin theorem showing that every `GNPrimeRepresentation p d x u` belongs to
the same complete finite representation set is welcome.

Do not add new number-theoretic restrictions on prime representations here.

---

# 5. Required mathematical interpretation in docstrings/report

Document the following distinction clearly.

A prime `p` is multiplicatively indecomposable, but an equality

$$
p=GN_d(x,u)
$$

still gives a nontrivial additive/exponential representation through binomial
coefficients, powers, boundary `x`, and Gap `u`.

GNPC-002 does not classify which prime values occur.  It proves that for every
fixed target `n` — hence in particular for every fixed prime `p` — the positive
GN representation problem is finite.

In particular, the exact lower floor

$$
2^d-1\le n
$$

formalizes the observation that increasing degree removes small target values
from the positive integer GN representation space.

Do not overstate this as a prime-generation theorem.

---

# 6. Regression checks

Add a few small theorem/example checks if useful, but keep them lightweight.
Suggested anchors include:

```text
GN 2 1 1 = 3
GN 3 1 1 = 7
GN 5 1 1 = 31
```

The purpose is only to guard the orientation of the canonical GN definition and
`(1,1)` floor theorem.

Do not add a large numerical search script in this checkpoint.

---

# 7. Explicitly deferred / forbidden in GNPC-002

Do **not** implement any of the following yet:

```text
GN prime → exponent prime
composite-degree GN factorization
nested GN composition identity
cyclotomic factorization
prime-row residue restrictions
p ≡ 1 [MOD d] classification
primitive-prime existence
Zsigmondy expansion
ABC / FLT / Legendre applications
Body primality wrapper
repository-wide GN renaming/refactor
```

`GN > 1` may appear only as a thin corollary of the new positive lower bounds if
it is useful internally.  Do not turn it into a separate campaign.

The next research checkpoint after GNPC-002 may study composite degree and the
implication `GN prime → degree prime`, but **stop before that here**.

---

# 8. Validation

At minimum run from `lean/dk_math`:

```text
lake build DkMath.NumberTheory.GNRepresentationBounds
```

If another final module name is chosen, build that exact module.

Do not spend effort on unrelated repository-wide warnings or existing `sorry`s.

No new `sorry` or `axiom` may be introduced by this checkpoint.

---

# 9. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-002.md
```

Report:

1. Outcome: complete / partial / blocked.
2. Existing DkMath and Mathlib lemmas reused.
3. Final module/import ownership.
4. Final declarations and exact theorem types.
5. Whether the exact `(1,1)` floor theorem required new proof or already existed.
6. Whether combined endpoint lower bound was achieved or split into equivalent lemmas.
7. Exact finite enumeration definition and completeness theorem.
8. Validation command/result.
9. Any deferred issues.

If blocked, identify the narrowest missing algebraic/order lemma.  Do not expand
scope to solve a harder number-theory problem.

---

# 10. Stop condition

GNPC-002 is complete when Lean has a reusable path

```text
GNPositiveRepresentation n d x u
        ↓
2^d - 1 ≤ n
x^(d-1) < n
d*u^(d-1) < n
        ↓
d < n, x < n, u < n
        ↓
(d,x,u) lies in an explicit finite box
        ↓
complete Finset of all positive GN representations of n
```

At that point stop and write `report-002.md`.

Do not continue to prime-degree classification in the same checkpoint.
