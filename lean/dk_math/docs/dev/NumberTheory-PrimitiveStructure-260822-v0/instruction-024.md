# Codex Instruction — PRIM-L017 Coprime Obstruction Seat Partition / Direction–Depth Budget

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-L016 is complete.

For a coprime square offset `r` and a selected old nondivisor support prime `p`, the quotient

```text
k = squareOffsetSupportQuotient n p r
```

satisfies the exact criterion

```text
Nat.Prime k
↔
squareOffsetAnchorNondivisorSupport n r = {p}
  ∧ ¬ p^2 ∣ n^2 + r.
```

The prime quotient lies above `n`, outside `primeScalesUpTo n`, and therefore gives a finite-world `FreshPrimeDirection`.

The complementary obstruction trichotomy is also available:

```text
prime quotient
or selected-direction depth persists
or another old prime direction persists.
```

Earlier checkpoints provide:

```text
card(squareAnchorCoprimeOffsets n) = 2 * Nat.totient n
```

for `0 < n`, the pair-overlap ledger

```text
squarePrimePairOverlapCount n
```

with local `Nat.choose k 2` semantics, and the exact generic wave occupancy

```text
card(squareWaveOffsets n m)
  = (2*n)/m + squareWaveCarry n m
```

for positive `m`.

The purpose of this checkpoint is to lift the PRIM-L016 one-incidence trichotomy to a finite partition of coprime seats and place the Direction and Depth obstructions in one explicit cover budget.

Do not attempt to prove the resulting budget impossible.

---

# Goal

Every covered coprime seat has nonempty old nondivisor support.  Such a seat falls into exactly one structural class:

```text
A. singleton support + depth one
   -> simple/fresh quotient seat

B. singleton support + selected prime square divides the anchored point
   -> self-depth obstruction seat

C. support cardinality at least two
   -> multi-direction / pair-overlap obstruction seat
```

Formalize this as finite seat classes, connect class A to the PRIM-L016 fresh quotient theorem, dominate class B by a prime-square wave ledger, dominate class C by the existing pair-overlap ledger, and derive a full-cover necessary budget.

This checkpoint should synthesize the Direction/Depth split already present in the local quotient theorem.  It should not add analytic estimates or a Legendre proof.

---

# Preferred location

Continue in:

```text
DkMath/NumberTheory/Legendre.lean
```

Do not move existing declarations in this checkpoint.

The file is large, but the theorem surface is still stabilizing.  Defer refactoring until after this budget frontier has been inspected.

---

# Required implementation surface

Names below are preferred, not mandatory.  Report final declaration names.

## 1. Seat-level predicates

Introduce lightweight predicates for the three covered coprime-seat classes.

Preferred conceptual forms:

```lean
def SquareAnchorCoprimeSimpleFreshSeat (n r : ℕ) : Prop :=
  ∃ p,
    p ∈ squareOffsetAnchorNondivisorSupport n r ∧
    squareOffsetAnchorNondivisorSupport n r = {p} ∧
    ¬ p ^ 2 ∣ n ^ 2 + r


def SquareAnchorCoprimeSingletonDepthSeat (n r : ℕ) : Prop :=
  ∃ p,
    p ∈ squareOffsetAnchorNondivisorSupport n r ∧
    squareOffsetAnchorNondivisorSupport n r = {p} ∧
    p ^ 2 ∣ n ^ 2 + r


def SquareAnchorCoprimeMultiSupportSeat (n r : ℕ) : Prop :=
  2 ≤ (squareOffsetAnchorNondivisorSupport n r).card
```

Embedding `Nat.Coprime n r` inside these predicates is optional.  It is acceptable to keep coprimality at the enclosing Finset level.

Do not encode valuation depth numerically.  `p^2 ∣ ...` is the only depth-one/depth-persistence distinction needed here.

## 2. Finite seat classes

Define the corresponding Finsets by filtering `squareAnchorCoprimeOffsets n`, preferably:

```lean
squareAnchorCoprimeSimpleFreshOffsets n
squareAnchorCoprimeSingletonDepthOffsets n
squareAnchorCoprimeMultiSupportOffsets n
```

Expose `[simp]` membership theorems.

If useful, also define the uncovered coprime seats

```lean
squareAnchorCoprimeUncoveredOffsets n
```

as support-cardinality zero.  This is optional because under full cover it vanishes.

## 3. Covered coprime seat trichotomy

Prove that a coprime covered seat belongs to exactly one of the three classes.

A useful theorem shape is:

```lean
theorem coprime_covered_seat_trichotomy
    {n r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hcovered : SquareOffsetCovered n r) :
    SquareAnchorCoprimeSimpleFreshSeat n r ∨
      SquareAnchorCoprimeSingletonDepthSeat n r ∨
      SquareAnchorCoprimeMultiSupportSeat n r
```

The proof should be elementary:

```text
support nonempty
  -> card = 1 or card >= 2
card = 1
  -> support = {p} for its unique p
  -> p^2 divides point or not
```

Also prove pairwise incompatibility of the three classes, or enough Finset disjointness to obtain an exact cardinality partition under full cover.

## 4. Exact full-cover seat partition

Under `0 < n` and `SquareOffsetsFullyCovered n`, prove that the coprime window is exactly the disjoint union of the three covered classes.

Preferred semantic theorem:

```text
squareAnchorCoprimeOffsets n
  = simpleFreshOffsets n
      ∪ singletonDepthOffsets n
      ∪ multiSupportOffsets n
```

with pairwise disjointness.

Then derive the exact cardinality identity:

```lean
theorem two_mul_totient_eq_simple_add_depth_add_multi_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * Nat.totient n =
      (squareAnchorCoprimeSimpleFreshOffsets n).card +
      (squareAnchorCoprimeSingletonDepthOffsets n).card +
      (squareAnchorCoprimeMultiSupportOffsets n).card
```

Equivalent association/order is acceptable.

This equality is a classification identity, not a contradiction.

## 5. Simple seats produce fresh quotient directions

For membership in `squareAnchorCoprimeSimpleFreshOffsets n`, expose the PRIM-L016 consequence:

```lean
theorem exists_fresh_quotient_of_mem_simpleFreshOffsets
    {n r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeSimpleFreshOffsets n) :
    ∃ p,
      p ∈ squareOffsetAnchorNondivisorSupport n r ∧
      FreshPrimeDirection
        (primeScalesUpTo n)
        (squareOffsetSupportQuotient n p r)
        (squareOffsetSupportQuotient n p r)
```

If thin, also expose the old-prime × fresh-prime factorization package by reusing `simple_support_depth_one_factorization`.

Do not claim the fresh quotient is a primitive-origin prime in the PrimitiveBeam/Zsigmondy sense.

## 6. Prime-square depth obstruction budget

Define an upper-budget ledger for self-depth obstructions using the generic wave with modulus `p^2`.

Preferred form:

```lean
noncomputable def squareAnchorPrimeSquareDepthBudget (n : ℕ) : ℕ :=
  ∑ p ∈ squareAnchorNondivisorPrimes n,
    (squareWaveOffsets n (p ^ 2)).card
```

This deliberately counts all square-window hits of `p^2`, not only singleton-support coprime seats.  Therefore it is an upper budget.

Prove:

```lean
theorem card_singletonDepthOffsets_le_primeSquareDepthBudget
    (n : ℕ) :
    (squareAnchorCoprimeSingletonDepthOffsets n).card ≤
      squareAnchorPrimeSquareDepthBudget n
```

The intended proof is a finite incidence count:

each singleton-depth seat provides its unique old nondivisor prime `p`, and that seat belongs to `squareWaveOffsets n (p^2)`.

Avoid choosing a noncomputable witness function if a finite sum/indicator transpose is cleaner.

## 7. Exact arithmetic form of the depth budget

Use the existing generic occupancy theorem to expose:

```lean
theorem squareAnchorPrimeSquareDepthBudget_eq_sum_div_add_carry
    (n : ℕ) :
    squareAnchorPrimeSquareDepthBudget n =
      ∑ p ∈ squareAnchorNondivisorPrimes n,
        ((2 * n) / (p ^ 2) + squareWaveCarry n (p ^ 2))
```

No p-adic valuation API is needed.

If cheap, note that when `2*n < p^2` the contribution is exactly its carry and hence at most one, by existing generic wave theorems.  A near/far `p^2` partition is optional and should not dominate the checkpoint.

## 8. Multi-support seats are paid for by pair overlap

Prove:

```lean
theorem card_multiSupportOffsets_le_squarePrimePairOverlapCount
    (n : ℕ) :
    (squareAnchorCoprimeMultiSupportOffsets n).card ≤
      squarePrimePairOverlapCount n
```

Reuse the existing local pair multiplicity and PRIM-L009 double count rather than building a second pair framework.

A straightforward route is:

```text
multi-support seat
  -> support.card >= 2
  -> 1 <= Nat.choose support.card 2

on coprime seats:
  full old support = anchor-nondivisor support

sum over the coprime subset
  <= sum over all square offsets
  = squarePrimePairOverlapCount n.
```

This theorem need not assume full cover.

## 9. Combined full-cover Direction/Depth budget

Combine the exact seat partition with the two obstruction upper bounds.

Main target:

```lean
theorem two_mul_totient_le_simpleFresh_add_depthBudget_add_pairOverlap_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * Nat.totient n ≤
      (squareAnchorCoprimeSimpleFreshOffsets n).card +
      squareAnchorPrimeSquareDepthBudget n +
      squarePrimePairOverlapCount n
```

This is the main PRIM-L017 frontier.

It separates a hypothetical complete coprime cover into:

```text
simple fresh-quotient seats
+ selected-prime square-depth obstruction budget
+ multi-direction pair-overlap obstruction budget.
```

## 10. Obstruction-only corollary

If no simple/fresh seat exists, derive:

```lean
theorem two_mul_totient_le_depthBudget_add_pairOverlap_of_fullyCovered_of_no_simpleFresh
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n)
    (hno : (squareAnchorCoprimeSimpleFreshOffsets n).card = 0) :
    2 * Nat.totient n ≤
      squareAnchorPrimeSquareDepthBudget n +
      squarePrimePairOverlapCount n
```

Equivalent `Finset = ∅` or `¬ Nonempty` assumptions are acceptable.

This is only a necessary condition under the absence of simple seats.  Do not assert that the right-hand side is too small.

---

# Interpretation to preserve in docstrings

State clearly:

- PRIM-L016 classified one selected incidence by prime quotient vs Direction/Depth obstruction;
- PRIM-L017 classifies whole coprime seats, not selected incidences;
- singleton support + depth one is the simple seat and produces a finite-world fresh quotient direction;
- singleton support + `p^2` divisibility is a depth obstruction;
- support cardinality at least two is a Direction overlap obstruction;
- `squareAnchorPrimeSquareDepthBudget` is an upper ledger of `p^2` wave hits, not a valuation-mass sum;
- `squarePrimePairOverlapCount` counts unordered distinct prime-direction pair incidences, not p-adic depth;
- the combined budget is finite exact bookkeeping / an upper-bound frontier, not a proof of Legendre's conjecture.

---

# Non-goals

Do **not** add in PRIM-L017:

- a proof that a simple/fresh seat always exists;
- a proof that the obstruction-only budget is impossible;
- a proof of `SquareAnchoredSupportEscape`;
- a proof of Legendre's conjecture;
- analytic estimates for `Nat.totient`, prime harmonic sums, pair counts, or square-prime counts;
- full inclusion-exclusion or third-order overlap machinery;
- p-adic valuation-depth summation;
- infinite descent;
- matching/Hall machinery;
- PrimitiveBeam/Zsigmondy first-occurrence claims;
- RH / CFBRC dependencies;
- numerical enumeration as a generic proof method.

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

PRIM-L017 is complete when:

1. the three coprime covered-seat classes are represented finitely;
2. covered coprime seats are classified into simple, singleton-depth, or multi-support cases;
3. under full cover the coprime window has an exact disjoint three-class partition;
4. the exact cardinality partition recovers `2 * Nat.totient n`;
5. a simple seat is bridged to the existing fresh quotient direction theorem;
6. singleton-depth seats are bounded by a `p^2`-wave depth budget;
7. the depth budget has an exact baseline-plus-carry arithmetic form;
8. multi-support seats are bounded by the existing pair-overlap ledger;
9. full cover implies the combined `simple + depth + pair` budget;
10. the no-simple obstruction-only corollary is available;
11. no contradiction or Legendre provider is smuggled into the checkpoint;
12. requested builds and audits are clean.

Stop after PRIM-L017.

---

# Review questions after PRIM-L017

After this checkpoint, inspect whether the combined Direction/Depth obstruction budget has genuine leverage.

Compare:

```text
simple side:
  singleton + depth one
  -> old prime × large fresh prime

Depth obstruction:
  p^2-wave hits

Direction obstruction:
  p*q pair-wave hits
```

Then choose the next route from actual Lean evidence:

```text
A. localize the depth budget by p^2 <= 2*n vs p^2 > 2*n;
B. restrict the pair budget to coprime nondivisor seats rather than all square seats;
C. use packet `(r,n+r)` separation to constrain which obstruction types may occur together;
D. use the packet factor equation on simple seats;
E. stop incidence counting and connect the fresh quotient side to a broader Primitive Origin theorem only if a genuine first-occurrence statement is available.
```

Do not escalate automatically to higher-order inclusion-exclusion.