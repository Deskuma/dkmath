# PRIM-L033 — Active Nondivisor-Prime Capacity / Even-Anchor Knife-Edge Elimination Lean Judgment

Date: 2026-08-25
Branch: `wip/number-theory-primitive-structure-260822-v2`
Lean / Mathlib: keep v4.32.2

## 0. Goal

PRIM-L032 proved an exact `+1` comparison between complete-point pairwise-coprime families and the weaker old-support-disjoint families.  Do **not** continue polishing that interface globally.

The next target is to shrink the capacity world itself on anchor-coprime seats.

Existing L011/L012 already provide:

```lean
squareAnchorDivisorPrimes n
squareAnchorNondivisorPrimes n
squareAnchorCoprimeOffsets n
squareOffsetAnchorNondivisorSupport n r
squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime
```

For `Nat.Coprime n r`, no prime dividing the anchor can cover `n^2+r`.  Therefore the exact capacity world for such seats is not all `primeScalesUpTo n`, but only `squareAnchorNondivisorPrimes n`.

This checkpoint must be **proof-backed**.  Implement a focused Lean module and a judgment report.  Do not make a report-only audit.

Suggested module:

```text
DkMath/NumberTheory/Legendre/ActivePrimeCapacity.lean
```

Add the facade import only if the resulting theorem surface is reusable.

## 1. Exact active-family interface

Introduce a minimal finite-family predicate whose members are anchor-coprime square offsets and whose actual active supports are pairwise disjoint.  A suggested shape is:

```lean
def PairwiseActiveOldSupportDisjointSquareSeatFamily
    (n : ℕ) (R : Finset ℕ) : Prop :=
  (∀ r ∈ R, r ∈ squareAnchorCoprimeOffsets n) ∧
    (R : Set ℕ).PairwiseDisjoint
      (fun r => squareOffsetAnchorNondivisorSupport n r)
```

Naming may be adjusted to fit repository style, but keep the semantics exact.

Prove thin bridges between this predicate and the existing
`PairwiseOldSupportDisjointSquareSeatFamily` under the anchor-coprime membership hypothesis.  Reuse
`squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime`; do not re-prove support arithmetic.

## 2. Active-world finite capacity theorem

Under `0 < n` and full cover, prove the localized capacity bound

```text
R.card ≤ (squareAnchorNondivisorPrimes n).card.
```

The proof should count the actual nondivisor support union, analogous to L029, but the containing finite world must be exactly `squareAnchorNondivisorPrimes n`.

Do not weaken the conclusion back to `(primeScalesUpTo n).card`.

Then prove the strict obstruction / Frontier consumer:

```text
(squareAnchorNondivisorPrimes n).card < R.card
  -> ¬ SquareOffsetsFullyCovered n
```

and, for `0 < n`, route through the existing Frontier API to

```text
∃ p, Nat.Prime p ∧ SquareCell n p.
```

This is the primary consumer of the checkpoint.

## 3. Prove the active world is genuinely smaller

Use the existing exact partition

```lean
squareAnchorDivisorPrimes n ∪ squareAnchorNondivisorPrimes n =
  primeScalesUpTo n
```

and disjointness to prove an exact card decomposition if convenient:

```text
card(divisor world) + card(nondivisor world) = card(old prime world).
```

For `1 < n`, prove that the divisor world is nonempty by taking a prime divisor of `n`, and conclude the strict shrink

```text
(squareAnchorNondivisorPrimes n).card <
  (primeScalesUpTo n).card.
```

Do not introduce analytic `π(n)` notation or prime-counting estimates.

This theorem is important: L033 must show that the new threshold is materially smaller, not just an API rename.

## 4. Even-anchor elimination of the L032 fresh exception

This is the second main Lean judgment.

Assume the anchor is even and two seats are anchor-coprime.  Then their complete points are odd.  Equivalently, prime `2` cannot belong to either old support.

Combine this with L032:

```lean
freshCollision_primeTwo_owner
```

which says every nontrivial fresh collision has exactly one endpoint owning old prime `2`.

Prove that, for an even anchor, an active old-support-disjoint coprime-seat family is automatically a complete-point pairwise-coprime family.

A target theorem may have the semantic shape

```lean
PairwiseActiveOldSupportDisjointSquareSeatFamily n R
  -> Even n
  -> PairwiseCoprimeSquareSeatFamily n R
```

or an equivalent theorem with hypotheses ordered to fit local APIs.

Do not prove this merely by asserting parity of the final gcd if L032 can be reused directly.  The desired result is the structural composition:

```text
anchor-coprime localization
+ even anchor excludes old prime 2
+ every fresh collision needs prime-2 ownership
= no fresh collision
= no non-coprime pair.
```

If a thinner parity proof is needed internally, that is fine, but retain a public theorem whose mathematical meaning is the composition above.

## 5. Even-anchor capacity consumer

Combine Sections 2 and 4 to expose a clean even-anchor theorem:

```text
active-family card excess over the nondivisor-prime world
  -> local square-cell prime.
```

The theorem should use the **localized** threshold, not the full old-prime card.

If useful, also expose that on even anchors the L032 one-seat repair loss is zero for active coprime-seat families.

Do not claim a universal provider.

## 6. False beam: odd anchors must remain distinct

Do not silently generalize the even-anchor theorem to all anchors.

Try to certify a concrete odd-anchor counterexample showing that anchor-coprime localization can still contain a fresh non-coprime collision.

Preferred small witness:

```text
n = 13
r = 1
s = 18

13^2 + 1  = 170
13^2 + 18 = 187

gcd(170,187) = 17 > 13
```

Check in Lean that:

- both `r` and `s` are in `squareAnchorCoprimeOffsets 13`;
- their old/nondivisor supports are disjoint;
- the two complete points are not coprime;
- the common gcd/fresh prime is `17`.

If this exact witness does not fit an existing theorem shape, use another explicit odd-anchor witness, but keep the purpose: **prove that even-anchor elimination is genuinely parity-specific**.

This false beam is important.  Do not erase the `+1` exception globally.

## 7. Stronger-beam / provider judgment

After the required proofs, evaluate only what the Lean theorems actually establish.

Questions:

1. Does coprime-seat localization strictly reduce the finite prime capacity threshold for every `n > 1`?
2. Does even-anchor localization eliminate the L032 fresh-collision exception completely?
3. Does the odd-anchor concrete witness prove that the same elimination is false in general?
4. Does any theorem now provide an explicit family with card exceeding the active threshold for arbitrary `n`?
5. Does any valid descent or direct proof of `LegendreConjecture` follow?

Expected outcomes:

```text
Outcome A — STRICT ACTIVE-WORLD CAPACITY SHRINK / EVEN-ANCHOR EXCEPTION ELIMINATION
Outcome B — ACTIVE-WORLD CAPACITY INTERFACE ONLY
Outcome C — NO MATERIAL LOCALIZATION
```

Use Outcome A only if both the strict threshold shrink and the even-anchor no-fresh-exception theorem are actually proved.

Even Outcome A is **not** a proof of Legendre unless a universal active-family provider is also proved.

## 8. Boundaries

Do not:

- upgrade Lean / Mathlib;
- import RH/CFBRC;
- introduce analytic prime-counting/PNT estimates;
- build a general graph library;
- restart quadratic-residue, parity, global Jacobsthal, finite-difference, or shell-transport audits;
- claim the active-family sufficient condition is equivalent to Legendre unless Lean proves a converse;
- implement a universal provider merely as an assumption and call the route complete.

Keep the module focused on exact finite arithmetic and reusable capacity bridges.

## 9. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-active-nondivisor-capacity-even-anchor-lean-judgment-260825.md
```

Record:

- implemented declarations;
- exact card threshold before/after localization;
- the even-anchor fresh-collision elimination theorem;
- the odd-anchor false-beam witness;
- whether any actual provider was constructed;
- Outcome A/B/C;
- the next exact frontier after Lean judgment.

Stop after the report.  Do not begin PRIM-L034 automatically.
