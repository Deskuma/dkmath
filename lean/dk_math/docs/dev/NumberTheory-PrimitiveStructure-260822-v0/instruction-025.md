# Codex Instruction — PRIM-L018 Coprime-Localized Obstruction Ledgers / Waste-Free Second-Order Frontier

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-L017 is complete.

Under full cover, the coprime square window is partitioned exactly into:

```text
simple/fresh seats
singleton-depth seats
multi-support seats
```

with

```text
2 * Nat.totient n
  = simple.card + singletonDepth.card + multi.card.
```

The current obstruction upper ledgers are:

```text
squareAnchorPrimeSquareDepthBudget n
squarePrimePairOverlapCount n
```

and PRIM-L017 proves:

```text
2 * Nat.totient n
  ≤ simple.card + depthBudget + pairOverlapCount
```

under full cover, and the obstruction-only corollary when `simple.card = 0`.

These bounds are correct but intentionally coarse:

- the depth budget counts every `p^2` hit in the full square window, including non-coprime seats and multi-support seats;
- the pair ledger counts every old-prime pair incidence in the full square window, including seats outside the coprime subwindow;
- on coprime seats, anchor-divisor primes cannot occur at all, so the relevant pair support is exactly the anchor-nondivisor support.

The next checkpoint should remove this bookkeeping waste before any contradiction attempt or higher-order escalation.

---

# Goal

Build obstruction ledgers on exactly the same domain as the PRIM-L017 classification:

```text
squareAnchorCoprimeOffsets n
```

and exactly the same old-prime world:

```text
squareAnchorNondivisorPrimes n.
```

Obtain localized depth and pair ledgers, exact local transposes, and the strictly sharper full-cover frontier

```text
2 * φ(n)
  ≤ simpleFresh.card
      + localizedDepthBudget
      + localizedPairOverlapCount.
```

If there are no simple seats:

```text
2 * φ(n)
  ≤ localizedDepthBudget + localizedPairOverlapCount.
```

Also prove that each localized obstruction budget is bounded by its PRIM-L017 global predecessor.  This checkpoint is therefore a refinement/audit of the existing frontier, not a new combinatorial order.

Do not add third-order intersections, analytic estimates, or a Legendre contradiction.

---

# Preferred location

Continue in:

```text
DkMath/NumberTheory/Legendre.lean
```

Do not move existing declarations in this checkpoint.

---

# Required implementation surface

Names are preferred, not mandatory.  Report final names.

## 1. Coprime-local `p^2` wave

Define the coprime seats hit by one nondivisor prime square:

```lean
noncomputable def squareAnchorCoprimePrimeSquareOffsets
    (n p : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeOffsets n).filter
    (fun r => p ^ 2 ∣ n ^ 2 + r)
```

Expose membership:

```lean
@[simp] theorem mem_squareAnchorCoprimePrimeSquareOffsets :
  r ∈ squareAnchorCoprimePrimeSquareOffsets n p ↔
    r ∈ squareAnchorCoprimeOffsets n ∧ p ^ 2 ∣ n ^ 2 + r
```

Prove the obvious subset into the existing generic wave when needed:

```text
squareAnchorCoprimePrimeSquareOffsets n p
  ⊆ squareWaveOffsets n (p^2).
```

Do not claim a quotient-difference cardinality formula for this coprime-filtered set.

## 2. Localized depth budget

Define:

```lean
noncomputable def squareAnchorCoprimePrimeSquareDepthBudget (n : ℕ) : ℕ :=
  ∑ p ∈ squareAnchorNondivisorPrimes n,
    (squareAnchorCoprimePrimeSquareOffsets n p).card
```

Then prove:

```lean
card_singletonDepthOffsets_le_coprimePrimeSquareDepthBudget
```

and the refinement theorem:

```lean
squareAnchorCoprimePrimeSquareDepthBudget_le_primeSquareDepthBudget
    (n : ℕ) :
    squareAnchorCoprimePrimeSquareDepthBudget n ≤
      squareAnchorPrimeSquareDepthBudget n
```

The localized budget still upper-counts a multi-support seat if some support prime occurs to depth at least two; that is acceptable and should be documented.

## 3. Exact local depth multiplicity transpose

Define the number of nondivisor prime-square directions hitting one coprime seat:

```lean
noncomputable def squareAnchorCoprimeDepthMultiplicity
    (n r : ℕ) : ℕ :=
  ((squareAnchorNondivisorPrimes n).filter
    (fun p => p ^ 2 ∣ n ^ 2 + r)).card
```

Prove the exact finite transpose:

```lean
theorem squareAnchorCoprimePrimeSquareDepthBudget_eq_sum_local_depthMultiplicity
    (n : ℕ) :
    squareAnchorCoprimePrimeSquareDepthBudget n =
      ∑ r ∈ squareAnchorCoprimeOffsets n,
        squareAnchorCoprimeDepthMultiplicity n r
```

This is an incidence identity, not a valuation sum.

## 4. Canonical nondivisor prime pairs

Define one copy of each unordered pair from the anchor-nondivisor prime set:

```lean
noncomputable def squareAnchorNondivisorPrimePairs (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((squareAnchorNondivisorPrimes n).product
    (squareAnchorNondivisorPrimes n)).filter
      (fun pair => pair.1 < pair.2)
```

Expose membership in terms of:

```text
p prime, p ≤ n, p ∤ n
q prime, q ≤ n, q ∤ n
p < q.
```

Prove this pair set is a subset of `squarePrimePairs n` if useful for refinement bounds.

## 5. Coprime-local pair overlap

Define:

```lean
noncomputable def squareAnchorCoprimePrimePairOverlapOffsets
    (n p q : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeOffsets n).filter
    (fun r =>
      SquareOffsetForbiddenBy n p r ∧
      SquareOffsetForbiddenBy n q r)
```

Expose exact membership.

Define the localized pair ledger:

```lean
noncomputable def squareAnchorCoprimePrimePairOverlapCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squareAnchorNondivisorPrimePairs n,
    (squareAnchorCoprimePrimePairOverlapOffsets
      n pair.1 pair.2).card
```

This counts `(coprime seat, unordered distinct nondivisor-prime pair)` incidences.

## 6. Exact localized pair double count

The main second-order identity should be:

```lean
theorem squareAnchorCoprimePrimePairOverlapCount_eq_sum_choose_support
    (n : ℕ) :
    squareAnchorCoprimePrimePairOverlapCount n =
      ∑ r ∈ squareAnchorCoprimeOffsets n,
        Nat.choose (squareOffsetAnchorNondivisorSupport n r).card 2
```

Reuse the PRIM-L009 unordered-pair machinery or a local analogue; do not introduce a competing public pair representation unless necessary.

This identity is stronger semantically than simply restricting the old global pair count: it states that the localized pair ledger is exactly the pair multiplicity of the support set used by the coprime classification.

## 7. Localized pair refinement and multi-seat budget

Prove:

```lean
theorem card_multiSupportOffsets_le_coprimePrimePairOverlapCount
    (n : ℕ) :
    (squareAnchorCoprimeMultiSupportOffsets n).card ≤
      squareAnchorCoprimePrimePairOverlapCount n
```

using the local `choose(card,2)` identity.

Also prove:

```lean
theorem squareAnchorCoprimePrimePairOverlapCount_le_squarePrimePairOverlapCount
    (n : ℕ) :
    squareAnchorCoprimePrimePairOverlapCount n ≤
      squarePrimePairOverlapCount n
```

Prefer deriving this from the exact local double count plus the existing PRIM-L009 global double count if that is shortest.

## 8. Seat-local obstruction certificate

Prove a local theorem that explains why the two localized ledgers suffice.

Preferred conceptual form:

```lean
theorem one_le_depthMultiplicity_add_pairMultiplicity_of_coprime_covered_not_simple
    {n r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hcovered : SquareOffsetCovered n r)
    (hnotSimple : ¬ SquareAnchorCoprimeSimpleFreshSeat n r) :
    1 ≤ squareAnchorCoprimeDepthMultiplicity n r +
      Nat.choose (squareOffsetAnchorNondivisorSupport n r).card 2
```

Equivalent theorem shape is acceptable.

The proof should be exactly the PRIM-L017 classification:

```text
singleton-depth
  -> local depth multiplicity ≥ 1
multi-support
  -> choose(card,2) ≥ 1.
```

Do not use full cover in this local theorem.

## 9. Localized full-cover frontier

Combine the exact seat partition with the localized budgets:

```lean
theorem two_mul_totient_le_simpleFresh_add_localDepth_add_localPair_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * Nat.totient n ≤
      (squareAnchorCoprimeSimpleFreshOffsets n).card +
      squareAnchorCoprimePrimeSquareDepthBudget n +
      squareAnchorCoprimePrimePairOverlapCount n
```

Then derive the no-simple version:

```lean
theorem two_mul_totient_le_localDepth_add_localPair_of_fullyCovered_of_no_simpleFresh
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n)
    (hno : (squareAnchorCoprimeSimpleFreshOffsets n).card = 0) :
    2 * Nat.totient n ≤
      squareAnchorCoprimePrimeSquareDepthBudget n +
      squareAnchorCoprimePrimePairOverlapCount n
```

These are the main PRIM-L018 frontiers.

## 10. Explicit refinement of PRIM-L017

Prove the combined domination:

```text
localizedDepthBudget + localizedPairOverlapCount
  ≤ globalDepthBudget + globalPairOverlapCount.
```

A named theorem is preferred if short.

This makes it explicit in Lean that PRIM-L018 removes bookkeeping waste rather than merely renaming the old frontier.

---

# Interpretation to preserve in docstrings

State clearly:

- PRIM-L017 classified coprime covered seats but bounded obstructions by full-window ledgers;
- PRIM-L018 restricts both obstruction ledgers to coprime seats and anchor-nondivisor directions;
- the localized depth multiplicity counts distinct prime-square divisibility witnesses, not p-adic valuation mass;
- the localized pair ledger counts unordered distinct nondivisor-prime pairs on coprime seats;
- the exact pair double count uses the same support set as the seat trichotomy;
- localized budgets are provably no larger than the prior global budgets;
- no contradiction or existence of a simple seat is asserted.

---

# Non-goals

Do not add in PRIM-L018:

- a proof that the localized obstruction-only inequality is impossible;
- a proof that a simple/fresh seat exists;
- a proof of `SquareAnchoredSupportEscape` or Legendre's conjecture;
- third-order inclusion-exclusion;
- Möbius inversion;
- matching/Hall machinery;
- analytic estimates for `Nat.totient`, prime sums, or pair counts;
- a closed quotient-difference formula for coprime-filtered `p^2` waves unless it falls out essentially for free;
- p-adic valuation sums;
- PrimitiveBeam/Zsigmondy first-occurrence claims;
- numerical enumeration as the generic proof method.

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

---

# Acceptance criteria

PRIM-L018 is complete when:

1. the `p^2` depth ledger is restricted to coprime seats;
2. its exact local incidence transpose is available;
3. unordered pairs are restricted to anchor-nondivisor primes and coprime seats;
4. the localized pair ledger has the exact `Nat.choose support.card 2` double-count identity;
5. singleton-depth and multi-support seat counts are bounded by the corresponding localized ledgers;
6. both localized ledgers are proved no larger than their PRIM-L017 global predecessors;
7. the localized full-cover and no-simple frontiers are proved;
8. no higher-order or analytic machinery is introduced.

Stop after PRIM-L018.

---

# Review questions after PRIM-L018

The next review should decide whether the localized obstruction frontier has genuine leverage.

Inspect:

```text
A. local depth multiplicity versus pair multiplicity on the same coprime seat
B. near/far behavior for p^2 and p*q after coprime restriction
C. whether a packet (r, n+r) can carry obstruction witnesses on both sides without forcing extra distinct directions
D. whether the localized obstruction budget still has too much capacity
E. if D is yes, stop escalating incidence order and pivot to a different structural invariant
```

Do not assume in advance that third-order counting is the next step.