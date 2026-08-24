# Codex Instruction — PRIM-L010 Near/Far Pair Localization and Far-Carry Exactness

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-L009 is complete.

The Legendre application layer now has a first-order and second-order finite cover ledger.

First order:

```text
squareCoverIncidenceCount n
  = squareCoverBaselineIncidence n
      + squareAnchorCarryCount n
```

and under `SquareOffsetsFullyCovered n`:

```text
squareCoverBaselineIncidence n + squareAnchorCarryCount n
  = 2*n + squareCoverOverlapExcess n.
```

Second order now includes:

```text
squarePrimePairs
squarePrimePairOverlapCount
squareOffsetPrimePairMultiplicity
```

with the exact local/global double count and the bound

```text
squareCoverOverlapExcess n
  ≤ squarePrimePairOverlapCount n.
```

Hence full cover forces the second-order budget inequality

```text
squareCoverBaselineIncidence n + squareAnchorCarryCount n
  ≤ 2*n + squarePrimePairOverlapCount n.
```

The pair ledger is already rewritten through the product-wave occupancy for `p*q`.

Earlier PRIM-L006/L007/L008 checkpoints also established for every positive modulus `m`:

```text
(squareWaveOffsets n m).card
  = (2*n) / m + squareWaveCarry n m
```

with:

```text
squareWaveCarry n m ≤ 1.
```

For distinct old primes `p`, `q`:

```text
squarePrimePairOverlapOffsets n p q
  = squareWaveOffsets n (p*q).
```

In particular:

```text
2*n < p*q
  -> (squarePrimePairOverlapOffsets n p q).card ≤ 1.
```

PRIM-L010 must now exploit exactly this local modulus/window comparison without escalating to third-order inclusion-exclusion.

---

# Goal

Split the canonical old-prime pairs into two exact finite regions:

```text
near pairs: p*q ≤ 2*n
far pairs:  2*n < p*q
```

and separate their contributions to the pair-overlap ledger.

The key structural distinction is:

```text
near product wave:
  at least one full product period fits in the square window;

far product wave:
  no full product period fits in the square window,
  so its entire overlap occupancy is exactly the one-bit square-anchor carry.
```

For a far pair, therefore:

```text
card(pair overlap) = squareWaveCarry n (p*q) ∈ {0,1}.
```

This should lead to an exact representation of the far contribution as the cardinality of the finite set of far pairs whose product wave actually hits the square window.

Then rewrite the complete second-order ledger as:

```text
near product-period baseline
+ near product carries
+ active far-pair count.
```

Do not attempt to prove this budget too small for full cover.

---

# Preferred location

Continue in:

```text
DkMath/NumberTheory/Legendre.lean
```

for this checkpoint.

Do not refactor/move the existing Legendre declarations at the same time.

---

# Required reconnaissance

Before coding, inspect the current API already present in `Legendre.lean` and current Mathlib Finset lemmas around:

```text
Finset.filter_filter
Finset.filter_union_filter_neg_eq
Finset.sum_filter
Finset.sum_congr
Finset.card_filter
Finset.card_congr
Finset.card_pos
Finset.Nonempty
Nat.div_eq_of_lt
Nat.lt_of_not_ge
```

The exact theorem names are search hints only.

Reuse the current definitions/theorems:

```text
squarePrimePairs
squarePrimePairOverlapCount
squarePrimePairOverlapOffsets
squarePrimePairOverlapOffsets_eq_squareWaveOffsets_product
card_squarePrimePairOverlapOffsets_eq_div_sub_div
card_squareWaveOffsets_eq_div_add_carry
card_squarePrimePairOverlapOffsets_le_one_of_two_mul_lt_product
squareWaveCarry_le_one
```

Do not re-prove pair-overlap/product-wave equivalence.

---

# Required implementation surface

Names below are preferred, not mandatory. Report final declaration names.

## 1. Near/far canonical pair partition

Define:

```lean
noncomputable def squarePrimeNearPairs (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (squarePrimePairs n).filter
    (fun pair => pair.1 * pair.2 ≤ 2 * n)

noncomputable def squarePrimeFarPairs (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (squarePrimePairs n).filter
    (fun pair => 2 * n < pair.1 * pair.2)
```

Expose exact membership for both.

Preferred near theorem shape:

```lean
@[simp] theorem mem_squarePrimeNearPairs
    {n p q : ℕ} :
    (p,q) ∈ squarePrimeNearPairs n ↔
      (p,q) ∈ squarePrimePairs n ∧ p*q ≤ 2*n
```

and analogously for far pairs.

If useful, also expose the fully expanded prime/bound form through the existing `mem_squarePrimePairs` theorem.

## 2. Exact pair partition

Prove that every canonical pair is exactly one of near/far.

Acceptable forms include:

```lean
squarePrimeNearPairs n ∪ squarePrimeFarPairs n = squarePrimePairs n
```

plus disjointness, or a direct membership equivalence:

```text
pair ∈ squarePrimePairs n
↔ pair ∈ nearPairs n ∨ pair ∈ farPairs n
```

with the two cases mutually exclusive.

Do not use classical choice beyond ordinary finite-set bookkeeping.

## 3. Near/far overlap-count ledgers

Define:

```lean
noncomputable def squarePrimeNearPairOverlapCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squarePrimeNearPairs n,
    (squarePrimePairOverlapOffsets n pair.1 pair.2).card

noncomputable def squarePrimeFarPairOverlapCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squarePrimeFarPairs n,
    (squarePrimePairOverlapOffsets n pair.1 pair.2).card
```

Then prove the exact split:

```lean
theorem squarePrimePairOverlapCount_eq_near_add_far
    (n : ℕ) :
    squarePrimePairOverlapCount n =
      squarePrimeNearPairOverlapCount n +
      squarePrimeFarPairOverlapCount n
```

No inequalities here; make the partition exact.

## 4. Generic far-wave carry exactness

Before specializing to prime pairs, prove the useful generic local theorem:

```lean
theorem card_squareWaveOffsets_eq_carry_of_two_mul_lt_modulus
    {n m : ℕ}
    (hm : 0 < m)
    (hfar : 2 * n < m) :
    (squareWaveOffsets n m).card = squareWaveCarry n m
```

The proof should simply use:

```text
card_squareWaveOffsets_eq_div_add_carry
```

and `(2*n)/m = 0` from `2*n < m`.

This theorem makes explicit that a product period longer than the local window contributes no baseline occupancy at all.

## 5. Far pair overlap = product carry

For any canonical far pair prove:

```lean
theorem card_squarePrimePairOverlapOffsets_eq_carry_of_mem_far
    {n p q : ℕ}
    (hpq : (p,q) ∈ squarePrimeFarPairs n) :
    (squarePrimePairOverlapOffsets n p q).card =
      squareWaveCarry n (p*q)
```

Use membership in `squarePrimePairs` to recover primality/distinctness and use the generic far-wave theorem.

Also expose if cheap:

```text
card(pair overlap) = 0 ∨ card(pair overlap) = 1.
```

Do not turn this into a probability statement.

## 6. Active far pairs

Define the finite set of far pairs whose unique possible product wave actually hits:

Preferred definition:

```lean
noncomputable def squarePrimeActiveFarPairs (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (squarePrimeFarPairs n).filter
    (fun pair => squareWaveCarry n (pair.1 * pair.2) = 1)
```

An equivalent filter by nonempty pair-overlap set is acceptable.

Expose membership.

Then prove the main far exactness theorem:

```lean
theorem squarePrimeFarPairOverlapCount_eq_card_activeFarPairs
    (n : ℕ) :
    squarePrimeFarPairOverlapCount n =
      (squarePrimeActiveFarPairs n).card
```

This should use the fact that each far-pair summand is exactly a `0/1` carry.

This theorem is stronger than the previous coarse bound

```text
far overlap count ≤ number of far pairs.
```

A thin corollary of that inequality may also be exposed.

## 7. Far active iff local product wave is nonempty

Strongly preferred if short:

```lean
theorem mem_squarePrimeActiveFarPairs_iff_overlap_nonempty
    {n p q : ℕ} :
    (p,q) ∈ squarePrimeActiveFarPairs n ↔
      (p,q) ∈ squarePrimeFarPairs n ∧
      (squarePrimePairOverlapOffsets n p q).Nonempty
```

Equivalent formulation with positive cardinality is acceptable.

This gives the semantic reading:

```text
far pair is active
↔ its one possible product-modulus phase actually lands in 1..2*n.
```

## 8. Near pair exact baseline/carry decomposition

Define:

```lean
noncomputable def squarePrimeNearPairBaseline (n : ℕ) : ℕ :=
  ∑ pair ∈ squarePrimeNearPairs n,
    (2 * n) / (pair.1 * pair.2)

noncomputable def squarePrimeNearPairCarryCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squarePrimeNearPairs n,
    squareWaveCarry n (pair.1 * pair.2)
```

Then prove:

```lean
theorem squarePrimeNearPairOverlapCount_eq_baseline_add_carry
    (n : ℕ) :
    squarePrimeNearPairOverlapCount n =
      squarePrimeNearPairBaseline n +
      squarePrimeNearPairCarryCount n
```

Use the existing product-wave occupancy theorem for each pair.

## 9. Every near pair has at least one overlap seat

Prove:

```lean
theorem one_le_card_squarePrimePairOverlapOffsets_of_mem_near
    {n p q : ℕ}
    (hpq : (p,q) ∈ squarePrimeNearPairs n) :
    1 ≤ (squarePrimePairOverlapOffsets n p q).card
```

The reason is purely local:

```text
p*q ≤ 2*n
-> floor(2*n/(p*q)) ≥ 1.
```

This theorem should not be interpreted as independence; it is just the fact that any residue class modulo a period not longer than the window appears at least once.

A thin corollary:

```text
(squarePrimeNearPairs n).card ≤ squarePrimeNearPairOverlapCount n
```

is useful if easy.

## 10. Exact complete pair-ledger normal form

Combine the near and far results into:

```lean
theorem squarePrimePairOverlapCount_eq_nearBaseline_add_nearCarry_add_activeFar
    (n : ℕ) :
    squarePrimePairOverlapCount n =
      squarePrimeNearPairBaseline n +
      squarePrimeNearPairCarryCount n +
      (squarePrimeActiveFarPairs n).card
```

Associativity/orientation may differ.

This is the main acceptance theorem of PRIM-L010.

It separates the second-order ledger into:

```text
near products:
  repeated baseline overlap + one-bit product carry

far products:
  zero baseline + one-bit hit/no-hit only
```

## 11. Full-cover second-order frontier in near/far form

Using the existing PRIM-L009 full-cover budget inequality, expose:

```lean
theorem baseline_add_carry_le_two_mul_add_near_far_pair_budget_of_fullyCovered
    {n : ℕ}
    (hfull : SquareOffsetsFullyCovered n) :
    squareCoverBaselineIncidence n + squareAnchorCarryCount n ≤
      2 * n +
        (squarePrimeNearPairBaseline n +
          squarePrimeNearPairCarryCount n +
          (squarePrimeActiveFarPairs n).card)
```

Equivalent parenthesization is acceptable.

This remains only a necessary condition.

## 12. Optional far-phase criterion

If very short, connect far-pair activity directly to the product forbidden phase.

For a far product `m = p*q > 2*n`, the local product wave has at most one representative, so activity should be equivalent to the canonical forbidden residue lying inside `squareOffsets n`.

A theorem of the conceptual form:

```text
active far pair
↔ 1 ≤ squareAnchorForbiddenResidue n (p*q)
  ∧ squareAnchorForbiddenResidue n (p*q) ≤ 2*n
```

is useful because it turns far second-order overlap into a direct square-anchor phase test.

Do not force this theorem if natural-number phase normalization becomes the dominant work of the checkpoint.

---

# Interpretation to preserve in docstrings

State clearly:

- the near/far split is by product modulus relative to the actual local square-window length `2*n`;
- near pairs have at least one complete product period inside the window;
- far pairs have no complete product period, so their entire pair-overlap occupancy is the one-bit square-anchor carry;
- `squarePrimeActiveFarPairs` therefore counts exactly the far product phases that actually land in the local window;
- this is a localization refinement of the second-order ledger, not an analytic estimate;
- no prime independence is assumed;
- pair multiplicity remains squarefree support multiplicity, distinct from p-adic valuation depth.

---

# Non-goals

Do **not** add in PRIM-L010:

- a proof of `SquareAnchoredSupportEscape`;
- a proof of Legendre's conjecture;
- an assertion that the near/far budget is impossible;
- third-order or higher inclusion-exclusion;
- Möbius inversion;
- asymptotic estimates for the number of near/far prime pairs;
- Mertens / PNT / prime harmonic estimates;
- Jacobsthal-function machinery;
- quadratic reciprocity / quadratic-residue distribution theory;
- prime-power valuation / Depth theory;
- RH / CFBRC dependencies;
- numerical enumeration as the generic proof method.

Do not replace exact finite pair occupancy by probabilistic heuristics.

---

# Verification

Run:

```sh
lake build DkMath.NumberTheory.Legendre
lake build DkMath.NumberTheory.Primitive
lake build DkMath
git diff --check
```

Audit the touched Lean file for new occurrences of:

```text
sorry
admit
native_decide
axiom
```

Report unrelated pre-existing occurrences separately; do not broaden scope to repair them.

---

# Acceptance criteria

PRIM-L010 is complete when:

1. canonical old-prime pairs are split exactly into near `p*q ≤ 2*n` and far `2*n < p*q` sets;
2. the total pair-overlap ledger splits exactly into near and far contributions;
3. generic far-wave occupancy is proved equal to its `0/1` carry;
4. each far prime-pair overlap cardinality is exactly its product carry;
5. the far overlap sum is exactly the number of active far pairs;
6. near overlap is decomposed exactly into product-period baseline plus product carry;
7. every near pair is proved to have at least one overlap seat;
8. the complete pair ledger is rewritten as `near baseline + near carry + active far count`;
9. the PRIM-L009 full-cover second-order necessary condition is exposed in this near/far normal form;
10. no third-order escalation, analytic estimate, contradiction, or Legendre proof is smuggled in;
11. requested builds and audits are clean.

Stop after PRIM-L010. Do not begin third-order inclusion-exclusion or an escape proof in this implementation pass.

---

# Review questions after PRIM-L010

After this checkpoint, inspect whether the far-pair term is structurally constrained enough to be useful.

In particular compare:

```text
A. far pair activity as a one-bit product carry / phase-in-window event
B. near pair baseline mass versus first-order baseline mass
C. compatibility of carries for p, q, and p*q
D. pairs whose primes divide the anchor n, where product carry may vanish
E. whether second-order counting has now reached its natural limit
```

Only after seeing the PRIM-L010 Lean surface should the next route be chosen between:

```text
product-carry compatibility
anchor-divisor / nondivisor pair partition
quadratic-residue phase rigidity
or abandoning higher-order incidence counting in favor of Primitive Origin localization.
```
