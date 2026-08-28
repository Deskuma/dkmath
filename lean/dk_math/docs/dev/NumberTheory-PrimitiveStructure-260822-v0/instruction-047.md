# PRIM-L032 — Two-Adic Fresh-Collision Uniqueness / One-Seat Repair Lean Judgment

Date: 2026-08-25
Branch: `wip/number-theory-primitive-structure-260822-v2`
Toolchain: keep Lean / Mathlib v4.32.2. Do not upgrade.

## 0. Review decision carried into this checkpoint

PRIM-L031 is accepted as **Outcome B — EXACT FRESH-COLLISION MATCHING STRUCTURE**.

Lean has proved that every nontrivial fresh collision has the form

```text
n^2 + r = q * k
n^2 + s = q * (k+1)
```

with

```text
Nat.Prime q
n < q
0 < k
k + 1 <= n
r < n < s
```

and that fresh-collision endpoints are unique. Old support transfers exactly to the consecutive cofactors `k` and `k+1`.

The missing descent is real: `k < n` does not reconstruct `SquareOffsetsFullyCovered k` or a smaller Legendre obstruction. Do not call `k<n` a descent.

The next checkpoint must exploit a new consequence of the consecutive-cofactor theorem rather than merely package the matching as a graph.

## 1. Core observation to submit to Lean

For every fresh collision, `k` and `k+1` are consecutive. Exactly one is even.

Because `k+1 <= n` and `0<k`, the collision itself forces `2 <= n`. Therefore `2` is an old prime direction.

Using

```lean
mem_squareOffsetPrimeSupport_iff_mem_freshCollisionCofactor
```

one endpoint of every fresh-collision pair must contain old prime `2` in its actual support, and the other endpoint must not.

Consequently, inside a

```lean
PairwiseOldSupportDisjointSquareSeatFamily n R
```

there should be **at most one fresh-collision pair**. Two distinct fresh-collision pairs would each consume old prime `2`, contradicting pairwise support disjointness.

This is stronger than the generic matching statement from L031.

The main target of this checkpoint is therefore:

```text
old-support-disjoint family
  -> at most one non-complete-coprime pair
  -> delete at most one seat
  -> complete-point pairwise-coprime family
```

This is a proof-backed implementation checkpoint.

## 2. Required source changes

Add one focused module, suggested path:

```text
DkMath/NumberTheory/Legendre/FreshCollisionRepair.lean
```

It may import:

```text
DkMath.NumberTheory.Legendre.FreshCollisionMatching
DkMath.NumberTheory.Legendre.CoprimeSeatCapacity
```

or the lowest sensible equivalent imports.

Add the module to:

```text
DkMath/NumberTheory/Legendre.lean
```

Do not change public theorem statements in L025--L031.
Do not introduce a general graph or matching library.

## 3. L032-1 — prime `2` ownership of a fresh collision

For

```lean
h : FreshCollisionPair n r s
```

prove first the thin bound

```text
2 <= n.
```

Then use `freshCollision_consecutive_smallCofactor` and the support/cofactor equivalence to prove that exactly one endpoint contains old prime `2`.

A suitable public statement is conceptually:

```lean
(2 ∈ squareOffsetPrimeSupport n r ∧
  2 ∉ squareOffsetPrimeSupport n s) ∨
(2 ∉ squareOffsetPrimeSupport n r ∧
  2 ∈ squareOffsetPrimeSupport n s)
```

The exact Lean shape may differ.

Do not assume full cover for this theorem. The factorization itself should be enough.

Do not merely prove `2` divides one of `k,k+1`; connect the result back to the actual endpoint support Finsets.

## 4. L032-2 — at most one fresh-collision pair inside an old-support family

Let

```lean
hfamily : PairwiseOldSupportDisjointSquareSeatFamily n R
```

and suppose

```lean
hrs : FreshCollisionPair n r s
nhuv : FreshCollisionPair n u v
```

with all four endpoints in `R`.

Prove that the two ordered pairs are equal:

```text
r = u ∧ s = v.
```

Recommended proof strategy:

1. each collision has exactly one endpoint whose actual old support contains `2`;
2. if those `2`-owning endpoints were distinct, `hfamily.2` would make their supports disjoint, contradicting common membership of `2`;
3. if the shared endpoint is lower in both pairs, use `freshCollision_lower_endpoint_unique`;
4. if upper in both, use `freshCollision_upper_endpoint_unique`;
5. lower/upper cross-identification is ruled out by `not_freshCollision_lower_and_upper`.

Do not replace this by a generic graph theorem.

A theorem saying simply that two distinct fresh-collision edges cannot both lie inside `R` is also acceptable if it is easier to consume later, but retain enough information to prove the repair theorem below.

## 5. L032-3 — non-coprime pair equals the unique fresh-collision exception

For ordered distinct members `r<s` of an old-support-disjoint family, prove/reuse the exact implication:

```text
¬ Nat.Coprime (n^2+r) (n^2+s)
  -> FreshCollisionPair n r s.
```

This should be a thin consequence of:

- family support disjointness;
- `Nat.Coprime` / `Nat.gcd = 1`;
- the L030 fresh-gcd classification.

Do not reprove the gcd classification.

The purpose is to make the next statement precise:

> within an old-support-disjoint family there is at most one pair of complete points that fails to be coprime.

Prove that sentence in Lean.

## 6. L032-4 — one-seat complete-coprime repair

Main structural theorem.

For every

```lean
hfamily : PairwiseOldSupportDisjointSquareSeatFamily n R
```

construct a finite subset `R'` such that:

```text
R' ⊆ R
PairwiseCoprimeSquareSeatFamily n R'
R.card <= R'.card + 1
```

Equivalent exact-cardinality formulations are welcome, for example:

```text
R'.card = R.card
```

when no fresh collision occurs, and

```text
R'.card + 1 = R.card
```

when one endpoint of the unique fresh collision is erased.

Suggested proof split:

### No fresh collision in `R`

Take `R' = R`. Any non-coprime ordered pair would create a `FreshCollisionPair`, contradiction.

### A fresh collision `r--s` exists

Erase one endpoint, for example `s`:

```lean
R' := R.erase s
```

If two points in `R'` were not coprime, they would create another fresh collision inside `R`; L032-2 says this must equal `r--s`, impossible because `s ∉ R'`.

Use the existing generic `PairwiseCoprimeSquareSeatFamily`; do not create another complete-coprime family predicate.

## 7. L032-5 — exact quantitative relation between L028 and L029 interfaces

Prove at least one thin public consequence making the one-seat gap explicit.

Preferred shape:

```text
PairwiseOldSupportDisjointSquareSeatFamily n R
  -> exists R' ⊆ R,
       PairwiseCoprimeSquareSeatFamily n R'
       and R.card <= R'.card + 1
```

If useful, also prove the converse direction already known from L029:

```text
PairwiseCoprimeSquareSeatFamily n R
  -> PairwiseOldSupportDisjointSquareSeatFamily n R.
```

Do not claim equivalence of the predicates: the `{1,6}` strictness witness remains valid.

The mathematical conclusion should be stated accurately:

```text
complete-coprime family
        -> old-support-disjoint family
        -> complete-coprime family after deleting at most one seat
```

So the strict weakening from L029 buys at most one extra seat, not an arbitrarily large matching gain.

## 8. L032-6 — capacity/frontier sanity consumer

Add one thin consumer only if it is a direct composition.

For example, if

```text
(primeScalesUpTo n).card + 1 < R.card
```

and `R` is old-support-disjoint, the repaired `R'` must still satisfy

```text
(primeScalesUpTo n).card < R'.card,
```

so the older complete-coprime L028 Frontier theorem already yields a prime square-cell witness.

This theorem is intentionally **weaker** than L029's direct threshold and should be documented as a sanity comparison, not as a stronger frontier result.

More important is the boundary it exposes:

```text
L029 improves on L028 only in the knife-edge possibility
R.card = oldPrimeWorld.card + 1
with one fresh-collision exception.
```

If a clean theorem isolating that knife-edge case can be stated without new framework, add it. Otherwise record it in the report.

## 9. Stronger-beam judgment — mandatory

After Lean proves the one-seat repair, judge whether it creates a genuinely new attack on the universal provider.

Questions:

1. Does prime `2` force at most one fresh collision in every old-support-disjoint family?
2. Can every such family be repaired to a complete-coprime family by deleting at most one seat?
3. Does this sharpen the relationship between L028 and L029 from an unquantified strict weakening to an exact `+1` gap?
4. Does the remaining `+1` knife-edge produce any new contradiction under full cover?
5. Does the theorem create a growing family provider or descent? If not, say no.

Do not promote an exact `+1` structural compression into a Legendre proof unless a genuine new contradiction closes.

## 10. Outcome classification

### Outcome A — EXACT ONE-SEAT REPAIR / PROVIDER COMPRESSION

Use if Lean proves both:

1. at most one fresh-collision pair can occur inside an old-support-disjoint family; and
2. deleting at most one seat produces a complete-point pairwise-coprime family.

This is an A-level structural compression even if it does not prove Legendre.

### Outcome B — TWO-ADIC COLLISION OWNERSHIP ONLY

Use if Lean proves that every fresh collision consumes prime `2`, but the global uniqueness/repair theorem does not close cleanly.

### Outcome C — ONE-SEAT REPAIR CLAIM IS FALSE

Use if a valid counterexample exists: for example an old-support-disjoint family containing two distinct fresh-collision pairs, or a family requiring deletion of at least two seats before complete coprimality.

If C occurs, formalize the smallest clean counterexample if practical and stop this route.

## 11. Documentation

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-two-adic-fresh-collision-repair-lean-judgment-260825.md
```

The report must include:

- exact declarations added;
- how prime `2` appears from consecutive cofactors;
- whether full cover is needed for the `2` ownership theorem;
- the uniqueness theorem for fresh collisions inside an old-support family;
- the one-seat repair theorem and exact cardinality statement;
- relation between L028 and L029 after repair;
- whether any new Frontier strength is gained;
- exact remaining knife-edge / provider problem;
- Outcome A/B/C;
- stop boundary.

## 12. Validation

Run at least:

```text
lake build DkMath.NumberTheory.Legendre.FreshCollisionRepair
lake build DkMath.NumberTheory.Legendre
git diff --check
```

Also run the recent trailing-whitespace / forbidden-placeholder audit.

Do not upgrade Mathlib. Do not run a full repository build unless dependency changes unexpectedly require it.

## 13. Non-goals

Do not:

- claim `k<n` is a descent;
- construct `SquareOffsetsFullyCovered k` from a cofactor;
- introduce a general graph/matching package;
- return to analytic prime counting, global Jacobsthal, parity reconnaissance, or QR;
- weaken actual old-support statements into arbitrary divisor statements;
- erase the L029 `{1,6}` strictness witness;
- claim Legendre's conjecture without a universal provider or direct contradiction.

The intended theorem chain is:

```text
fresh collision
  -> q*k and q*(k+1)
  -> exactly one cofactor is even
  -> exactly one endpoint owns old prime 2

old-support-disjoint family
  -> two distinct fresh collisions would both spend prime 2
  -> impossible
  -> at most one non-coprime pair
  -> erase at most one seat
  -> complete-point pairwise-coprime family
```
