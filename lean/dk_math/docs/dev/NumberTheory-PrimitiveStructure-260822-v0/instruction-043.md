# PRIM-L028 — Finite Coprime-Seat Capacity Bridge Lean Judgment

Date: 2026-08-25
Branch: `wip/number-theory-primitive-structure-260822-v2`
Toolchain: keep Lean / Mathlib v4.32.2. Do not upgrade.

## 0. Review decision carried into this checkpoint

PRIM-L027 source is accepted.

The report's Outcome C is understood narrowly as: the proposed hypothesis
`0 < k -> SquareOffset (4*k) (6*k+3)` was false and Lean correctly exposed the
counterexample `k = 1`.

The salvaged mathematics under the corrected condition `2 <= k` is not a C-level
result: Lean proved a genuine four-seat pairwise-coprime family, pairwise-disjoint
actual old-prime supports, four distinct full-cover witnesses, and an unbounded
periodic parameter family.

Do not rewrite the historical L027 report merely to change its label. Preserve the
counterexample and the repaired theorem surface.

This checkpoint must now stop hand-building isolated cliques and extract the exact
finite-capacity theorem that all L025/L027 witness arguments are instances of.

## 1. Purpose

For a finite set of actual square-shell offsets `R`, assume:

1. every `r in R` is a `SquareOffset n r`;
2. distinct seats in `R` have coprime complete points:

```text
Nat.Coprime (n^2 + r) (n^2 + s)
```

for `r != s`.

Under

```lean
hfull : SquareOffsetsFullyCovered n
```

every seat has a nonempty actual old-prime support. Complete-point coprimality
makes the supports of distinct seats disjoint. Therefore a full cover must spend
at least one distinct old-prime direction per seat.

The central theorem to prove in Lean is:

```text
R.card <= (primeScalesUpTo n).card.
```

Then prove the contrapositive capacity obstruction:

```text
(primeScalesUpTo n).card < R.card
  -> not SquareOffsetsFullyCovered n.
```

Finally connect that local failure of full cover to an actual prime in the square
cell using the existing `Frontier` API.

This is a proof-backed implementation checkpoint, not report-only reconnaissance.

## 2. Required source changes

Add one focused module, suggested path:

```text
DkMath/NumberTheory/Legendre/CoprimeSeatCapacity.lean
```

Import only what is needed. It may import the current clique layer if useful for a
sanity consumer, but the generic theorem itself should depend on the lowest sensible
Legendre support/coprimality/frontier modules.

Add the module to:

```text
DkMath/NumberTheory/Legendre.lean
```

Do not modify L025/L026/L027 theorem statements.
Do not introduce a general graph/coloring library.
Do not use analytic prime-counting estimates.

## 3. L028-1 — minimal finite-family predicate

Introduce at most one small predicate if it materially improves theorem statements.
A suggested shape is:

```lean
def PairwiseCoprimeSquareSeatFamily
    (n : ℕ) (R : Finset ℕ) : Prop :=
  (forall r in R, SquareOffset n r) /\
  forall r in R, forall s in R, r != s ->
    Nat.Coprime (n ^ 2 + r) (n ^ 2 + s)
```

Lean syntax may be adjusted naturally.

If the theorem is cleaner without a new public definition, keep the assumptions
explicit instead. Do not introduce a structure with fields merely to package this.

## 4. L028-2 — support containment

For every seat support, prove/reuse the thin fact that

```text
squareOffsetPrimeSupport n r ⊆ primeScalesUpTo n.
```

This should follow directly from `mem_squareOffsetPrimeSupport` and
`mem_primeScalesUpTo`.

If an equivalent theorem already exists, reuse it instead of duplicating it.

## 5. L028-3 — pairwise support disjointness for a finite family

Use the already-proved generic theorem

```lean
disjoint_squareOffsetPrimeSupport_of_coprime_points
```

from L025.

Show that the family

```text
r ↦ squareOffsetPrimeSupport n r
```

is pairwise disjoint on distinct members of `R` whenever the complete points are
pairwise coprime.

Do not reprove prime-divisor separation point-by-point.

## 6. L028-4 — full cover makes every family support nonempty

Under

```lean
hfull : SquareOffsetsFullyCovered n
```

and shell membership of every `r in R`, use

```lean
squareOffsetCovered_iff_primeSupport_nonempty
```

to obtain nonemptiness of every `squareOffsetPrimeSupport n r`.

This theorem may remain private/local if it is only proof plumbing.

## 7. L028-5 — main finite capacity theorem

Prove a public theorem with the mathematical content:

```text
full cover
+ finite actual seat family
+ pairwise coprime complete points
---------------------------------
R.card <= (primeScalesUpTo n).card
```

A suggested theorem name is:

```lean
card_pairwiseCoprimeSquareSeatFamily_le_primeScalesUpTo_of_fullyCovered
```

Use a finite argument only.

Preferred proof routes:

- pairwise-disjoint nonempty support Finsets -> union cardinality >= `R.card`, then
  union subset `primeScalesUpTo n`; or
- a local/classical choice of one support prime per seat plus injectivity from
  support disjointness.

Do not create a public witness-choice function solely for this proof.

The result must count actual old-prime directions, not arbitrary divisors.

## 8. L028-6 — direct capacity obstruction

Prove the contrapositive theorem:

```lean
(primeScalesUpTo n).card < R.card
-> not SquareOffsetsFullyCovered n
```

under the same shell-membership and pairwise-coprime hypotheses.

Suggested name:

```lean
not_fullyCovered_of_primeWorld_card_lt_pairwiseCoprimeSquareSeats
```

This theorem is the first required frontier consumer of the checkpoint.

## 9. L028-7 — actual prime-square-cell consumer

Assume additionally:

```lean
hn : 0 < n
```

From L028-6 and the existing `Frontier` theorems, prove a local Legendre witness:

```text
exists p, Nat.Prime p and SquareCell n p
```

whenever a pairwise-coprime square-seat family has cardinality strictly larger
than the available old-prime world.

Do not reprove the composite-number/small-prime argument. Reuse one of:

```lean
not_squareOffsetsFullyCovered_iff_escaping_nonempty
prime_of_squareAnchoredSupportEscape
```

or an equivalent existing frontier chain.

A suggested theorem name is:

```lean
exists_prime_squareCell_of_primeWorld_card_lt_pairwiseCoprimeSquareSeats
```

This theorem is local in `n`; do not state the global Legendre conjecture unless a
separate universal provider has actually been proved.

## 10. L028-8 — instantiate the existing four-seat clique

Use L027 as a sanity consumer of the generic capacity bridge.

Under

```text
2 <= k
Nat.Coprime (4*k+3) 15
SquareOffsetsFullyCovered (4*k)
```

recover the necessary lower bound

```text
4 <= (primeScalesUpTo (4*k)).card
```

through the new generic theorem, not by manually choosing four witnesses again.

A small Finset containing the four L027 offsets is acceptable if needed.
Do not duplicate the entire L027 pairwise-coprime proof; reuse
`centeredPacketClique4_points_pairwise_coprime`.

If Finset boilerplate is disproportionate, this instantiation may be kept as a
small theorem in the new module rather than adding more configuration definitions.

## 11. Stronger-beam judgment — mandatory

After the generic theorem builds, classify what has actually changed.

The new theorem should expose the exact remaining combinatorial target:

```text
construct R inside the shell
such that complete points are pairwise coprime
and
(primeScalesUpTo n).card < R.card.
```

Judge whether the current K3/K4 constructions come anywhere near this threshold.
Do not use PNT or asymptotic estimates in Lean for this checkpoint.

If there is a very thin exact theorem expressing the global sufficient provider,
for example:

```text
(forall n > 0, exists R, ... and primeWorldCard < R.card)
  -> LegendreConjecture
```

it may be added only if it is a direct composition of L028-7 and does not require a
new framework. Otherwise record the local criterion and stop.

Do not start a broad search for growing cliques in this checkpoint.

## 12. Outcome classification

### Outcome A — DIRECT CAPACITY FRONTIER BRIDGE

Use if Lean proves both:

1. the generic full-cover capacity bound, and
2. the strict-cardinality criterion producing an actual prime square-cell witness.

This is a direct conditional frontier breaker even if no large family is yet known.

### Outcome B — GENERIC CAPACITY STRUCTURE ONLY

Use if the family-cardinality theorem is proved but the local prime-witness consumer
does not close cleanly through the existing frontier API.

### Outcome C — ABSTRACTION ADDS NO USABLE THEOREM

Use if the generic family layer collapses into awkward restatement without a clean
capacity inequality or is not reusable from L027.

## 13. Documentation

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveStructure-260822-v0/
  primitive-coprime-seat-capacity-lean-judgment-260825.md
```

The report must include:

- exact declarations added;
- proof strategy for finite cardinality;
- whether choice or support-union counting was used;
- the local non-full-cover theorem;
- the local prime-square-cell consumer;
- L027/K4 instantiation result;
- exact remaining threshold problem;
- Outcome A/B/C;
- stop boundary.

Also state explicitly that L027's original `0 < k` proposal was false but its
`2 <= k` salvaged theorem surface is retained and used.

## 14. Validation

Run at least:

```text
lake build DkMath.NumberTheory.Legendre.CoprimeSeatCapacity
lake build DkMath.NumberTheory.Legendre
git diff --check
```

Also run the recent trailing-whitespace / forbidden-placeholder audit.

Do not upgrade Mathlib. Do not run a full repository build unless dependency changes
unexpectedly require it.

## 15. Non-goals

Do not:

- claim Legendre's conjecture without a universal large-family provider;
- introduce graph coloring or clique-search infrastructure;
- invoke PNT, Chebyshev, Rosser-Schoenfeld, Jacobsthal, or analytic sieve bounds;
- hand-build K5/K6 merely to increase a constant witness count;
- erase the L027 `k = 1` counterexample;
- return to report-only reconnaissance in place of Lean theorem attempts.

The essential checkpoint is:

```text
pairwise-coprime actual shell seats
        ↓
pairwise-disjoint actual old-prime supports
        ↓
full cover spends >= one distinct old prime per seat
        ↓
R.card <= old-prime-world.card
        ↓
if R.card is larger, full cover is impossible
        ↓
Frontier API gives an actual prime in the square cell
```
