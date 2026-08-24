# Codex Instruction — PRIM-L006 Local Wave Cardinality and Pair-Overlap Sparsity

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-L005 is complete.

The Legendre application layer now exposes the exact local cover / overlap surface:

```text
SquareOffsetForbiddenBy
SquareOffsetCovered
squareAnchorForbiddenResidue
squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue
squareOffsets
SquareOffsetsFullyCovered
squareOffsetPrimeSupport
mem_squareOffsetPrimeSupport
squareOffsetCovered_iff_primeSupport_nonempty
squareOffsetCovered_iff_primeSupport_card_pos
squareOffsetForbiddenBy_pair_iff_product_dvd
squareOffsetForbiddenBy_pair_iff_product_phase
SquareOffsetOverlap
squareOffsetOverlap_iff_exists_distinct_support
squareCoverIncidenceCount
card_squareOffsets_le_squareCoverIncidenceCount_of_fullyCovered
```

For distinct old primes `p` and `q`, simultaneous coverage of one offset is now exactly one square-anchor wave modulo `p*q`:

```text
p | n^2 + r
q | n^2 + r
<->
p*q | n^2 + r
<->
r lies in one forbidden phase mod p*q.
```

The current incidence ledger counts repeated coverage, and full cover implies at least one incidence per square offset.

PRIM-L006 should now add the missing **local-window geometry**:

> a residue wave of modulus larger than the square-offset window can hit that window at most once.

This is the first localization fact that uses the actual window length `2*n`, rather than only global periodicity.

---

# Goal

Formalize two complementary facts:

1. transpose the incidence count from “sum over offsets of support cardinalities” to “sum over prime waves of their local hit counts”;
2. prove that a wave of modulus `m > 2*n` has at most one hit inside `squareOffsets n`, and specialize this to pairwise overlaps with modulus `p*q`.

The key mathematical statement is:

```text
r1, r2 in {1,...,2*n}
r1 ≡ r2 [MOD m]
2*n < m
=> r1 = r2.
```

Therefore, for distinct primes `p,q`:

```text
2*n < p*q
=> the p-wave and q-wave overlap at at most one square offset.
```

This checkpoint is still an **audit / localization layer**. Do not try to prove that full cover is impossible.

---

# Preferred location

Prefer continuing in:

```text
DkMath/NumberTheory/Legendre.lean
```

if the module remains manageable.

If the local-wave section becomes too large, a sibling such as

```text
DkMath/NumberTheory/Legendre/LocalWaveCardinality.lean
```

is acceptable, but do not create an import cycle or move existing declarations merely for aesthetics.

Report the final location and declaration names.

---

# Required reconnaissance

Before coding, inspect current Lean 4.32 / Mathlib APIs for:

```text
Nat.ModEq.eq_of_lt_of_lt
Nat.ModEq
Finset.card_le_one
Finset.card_filter
Finset.sum_comm
Finset.sum_product
Finset.filter_filter
Finset.card_congr
Finset.sum_bij
Finset.Icc
Finset.card_Icc
```

Names above are search hints only.

Prefer the shortest current API route. Do not build a generic interval/residue-count framework if the needed finite statements can be proved directly.

---

# Required implementation surface

Names are preferred, not mandatory. Report final names.

## 1. Exact square-offset cardinality

Expose:

```lean
@[simp] theorem card_squareOffsets (n : ℕ) :
    (squareOffsets n).card = 2 * n
```

This must also be correct at `n = 0`.

Prefer a short proof from the existing `Finset.Icc` cardinality API.

Then add the existing full-cover incidence lower bound in explicit numeric form, if thin:

```lean
theorem two_mul_le_squareCoverIncidenceCount_of_fullyCovered
    {n : ℕ}
    (hfull : SquareOffsetsFullyCovered n) :
    2 * n ≤ squareCoverIncidenceCount n
```

This should be only a wrapper around the already-proved cardinality inequality.

## 2. Per-prime local wave seat set

Define the offsets in the square window hit by a fixed old prime wave:

```lean
noncomputable def squarePrimeWaveOffsets (n q : ℕ) : Finset ℕ := by
  classical
  exact (squareOffsets n).filter (fun r => SquareOffsetForbiddenBy n q r)
```

Expose exact membership:

```lean
@[simp] theorem mem_squarePrimeWaveOffsets
    {n q r : ℕ} :
    r ∈ squarePrimeWaveOffsets n q ↔
      SquareOffset n r ∧ SquareOffsetForbiddenBy n q r
```

Do not require `Nat.Prime q` merely for this filtering identity.

## 3. Incidence transpose / double-counting identity

Prove the exact finite double-counting theorem:

```lean
theorem squareCoverIncidenceCount_eq_sum_primeWave_cards
    (n : ℕ) :
    squareCoverIncidenceCount n =
      ∑ q ∈ primeScalesUpTo n, (squarePrimeWaveOffsets n q).card
```

This is a combinatorial identity counting the same finite incidence pairs `(r,q)` in the two possible orders:

```text
sum over offsets r of number of covering q
=
sum over old primes q of number of hit offsets r.
```

Preferred proof style:

- expand the support/filter definitions;
- use a finite sum interchange / indicator count;
- avoid introducing a separate bipartite graph abstraction unless genuinely necessary.

Do not estimate either side in this theorem.

## 4. Generic local wave set for an arbitrary positive modulus

To avoid duplicating the pair-product proof, introduce a minimal generic anchored wave set if useful:

```lean
noncomputable def squareWaveOffsets (n m : ℕ) : Finset ℕ := by
  classical
  exact (squareOffsets n).filter (fun r => m ∣ n ^ 2 + r)
```

Equivalent reuse of `SquareOffsetForbiddenBy n m r` is preferred.

Expose membership:

```lean
@[simp] theorem mem_squareWaveOffsets
    {n m r : ℕ} :
    r ∈ squareWaveOffsets n m ↔
      SquareOffset n r ∧ m ∣ n ^ 2 + r
```

If `squarePrimeWaveOffsets` and `squareWaveOffsets` would be literal duplicates, it is acceptable to define only the generic `squareWaveOffsets` and make the prime-wave API a thin abbreviation / theorem. Keep the public surface small.

## 5. Main local sparsity theorem: modulus larger than the window gives at most one hit

Prove a generic theorem of the form:

```lean
theorem card_squareWaveOffsets_le_one_of_two_mul_lt_modulus
    {n m : ℕ}
    (hm : 0 < m)
    (hlarge : 2 * n < m) :
    (squareWaveOffsets n m).card ≤ 1
```

or an equivalent theorem first proving element uniqueness:

```lean
theorem eq_of_mem_squareWaveOffsets_of_two_mul_lt_modulus
    {n m r₁ r₂ : ℕ}
    (hm : 0 < m)
    (hlarge : 2 * n < m)
    (hr₁ : r₁ ∈ squareWaveOffsets n m)
    (hr₂ : r₂ ∈ squareWaveOffsets n m) :
    r₁ = r₂
```

and deriving the cardinality bound.

Preferred mathematical route:

1. both hits satisfy the same square-anchor forbidden phase modulo `m` by
   `squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue`;
2. hence `r₁ ≡ r₂ [MOD m]`;
3. both `r₁,r₂ ≤ 2*n < m`;
4. bounded congruent naturals are equal.

Do not prove this by enumerating offsets.

The theorem is local-window arithmetic and should not require `m` to be prime.

## 6. Pair-overlap seat set

Expose the finite offsets simultaneously hit by two old prime waves, preferably:

```lean
noncomputable def squarePrimePairOverlapOffsets
    (n p q : ℕ) : Finset ℕ := by
  classical
  exact (squareOffsets n).filter
    (fun r => SquareOffsetForbiddenBy n p r ∧ SquareOffsetForbiddenBy n q r)
```

Membership theorem required.

For distinct primes, identify it exactly with the product wave:

```lean
theorem squarePrimePairOverlapOffsets_eq_squareWaveOffsets_product
    {n p q : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpq : p ≠ q) :
    squarePrimePairOverlapOffsets n p q =
      squareWaveOffsets n (p * q)
```

This should be a thin Finset extensionality wrapper around the already-proved
`squareOffsetForbiddenBy_pair_iff_product_dvd`.

## 7. Main pairwise sparsity corollary

For distinct primes, prove:

```lean
theorem card_squarePrimePairOverlapOffsets_le_one_of_two_mul_lt_product
    {n p q : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpq : p ≠ q)
    (hlarge : 2 * n < p * q) :
    (squarePrimePairOverlapOffsets n p q).card ≤ 1
```

This must be obtained by rewriting the pair overlap set to the product wave and applying the generic local sparsity theorem.

Interpretation:

```text
large product p*q
=> pairwise overlap is locally sparse
=> at most one repeated-covered seat in the entire square window.
```

Do not infer that the total overlap excess is small yet; many different prime pairs may share or distribute overlaps.

## 8. Overlap-excess ledger — now encouraged

If it remains compact, add:

```lean
noncomputable def squareCoverOverlapExcess (n : ℕ) : ℕ :=
  ∑ r ∈ squareOffsets n,
    ((squareOffsetPrimeSupport n r).card - 1)
```

and prove under full cover:

```lean
theorem squareCoverIncidenceCount_eq_two_mul_add_overlapExcess_of_fullyCovered
    {n : ℕ}
    (hfull : SquareOffsetsFullyCovered n) :
    squareCoverIncidenceCount n =
      2 * n + squareCoverOverlapExcess n
```

This is the exact bookkeeping identity:

```text
one mandatory incidence per offset
+
all repeated coverage
=
total incidence count.
```

Use pointwise positivity from full cover so that natural subtraction is exact. Do not introduce integer-valued bookkeeping unless Lean makes the Nat proof disproportionately awkward.

If this identity becomes the dominant implementation burden, leave it for the next checkpoint and report that choice explicitly.

---

# Mathematical interpretation to preserve

Docstrings should distinguish three levels:

```text
single-prime wave q
pair intersection p ∩ q = product wave p*q
local square window 1..2*n
```

The new localization fact is:

```text
period > window length
=> at most one hit of that phase in the window.
```

This is not a global density statement.

Also state clearly:

- `squareCoverIncidenceCount` counts incidences, not distinct seats;
- the transposed sum is exact double counting;
- pairwise product-wave sparsity is a necessary structural constraint only;
- support multiplicity remains squarefree prime-direction multiplicity, not p-adic depth.

---

# Non-goals

Do **not** add in PRIM-L006:

- a proof of `SquareAnchoredSupportEscape`;
- a proof of Legendre's conjecture;
- a claim that pairwise sparsity alone prevents full cover;
- analytic estimates for `sum 1/p`;
- Mertens / PNT;
- an asymptotic density argument;
- full inclusion-exclusion;
- Möbius inversion;
- Jacobsthal machinery;
- arbitrary higher-order subset products unless needed internally for a tiny proof;
- prime-power valuation / Depth theory;
- Origin / first-occurrence contradiction work;
- RH / CFBRC imports;
- category theory.

Do not enumerate primes, offsets, or overlap seats for fixed numerical `n` as the generic proof method.

---

# Verification

If modifying `Legendre.lean` directly, run:

```sh
lake build DkMath.NumberTheory.Legendre
lake build DkMath.NumberTheory.Primitive
lake build DkMath
git diff --check
```

If creating a sibling module, also build that module explicitly.

Audit touched Lean files for new occurrences of:

```text
sorry
admit
native_decide
axiom
```

Report unrelated pre-existing occurrences separately; do not broaden scope to repair them.

---

# Acceptance criteria

PRIM-L006 is complete when:

1. `squareOffsets n` has exact cardinality `2*n`;
2. a finite local seat set for a fixed wave is exposed;
3. the incidence count is transposed exactly into a sum of per-prime local wave cardinalities;
4. a generic modulus `m > 2*n` wave is proved to hit the square window at most once;
5. pairwise prime overlap is identified with the product-wave seat set;
6. `2*n < p*q` implies at most one `p/q` overlap seat;
7. no density/provider/Legendre proof is introduced;
8. requested builds and audits are clean.

The overlap-excess identity is strongly encouraged but not required if it causes disproportionate proof overhead.

Stop after PRIM-L006. Do not proceed to higher-order overlap or an escape proof in the same implementation pass.

---

# Review questions after PRIM-L006

The next review should inspect whether the new local sparsity facts justify one of these routes:

```text
A. split prime pairs into p*q <= 2*n and p*q > 2*n, then bound overlap capacity;
B. generalize pair overlap to finite squarefree support products only as far as needed;
C. formulate an anchored Jacobsthal/local-gap statement using the now exact local wave sets;
D. switch from overlap counting to Primitive Origin / first-occurrence obstruction.
```

Do not choose that route inside PRIM-L006.