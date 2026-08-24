# Codex Instruction — PRIM-L012 Coprime Doublet / n-Shift Separation

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-L011 is complete.

The Legendre application layer now partitions the old prime world into anchor-divisor and anchor-nondivisor directions:

```text
squareAnchorDivisorPrimes n
squareAnchorNondivisorPrimes n
```

with exact semantics:

```text
q ∣ n
  -> SquareOffsetForbiddenBy n q r ↔ q ∣ r
```

and, for positive `n`:

```text
SquareOffsetCoveredByAnchorDivisorPrime n r
  ↔ ¬ Nat.Coprime n r.
```

Hence a coprime square offset can only be covered by an old prime `q ≤ n` satisfying `q ∤ n`.

The finite coprime subwindow is:

```text
squareAnchorCoprimeOffsets n
```

and PRIM-L011 proved:

```text
(squareAnchorCoprimeOffsets n).card = 2 * Nat.totient n
```

for `0 < n`.

It also introduced:

```text
squareAnchorNondivisorIncidence n
```

and the full-cover necessary condition:

```text
SquareOffsetsFullyCovered n
-> 2 * Nat.totient n ≤ squareAnchorNondivisorIncidence n.
```

The next checkpoint should use the *geometry of those `2 * φ(n)` seats*, not merely their cardinality.

---

# Goal

Expose the coprime square window as `φ(n)` canonical two-seat packets:

```text
r
n + r
```

with `1 ≤ r ≤ n` and `Nat.Coprime n r`.

The key square-anchor fact is:

```text
q ∤ n
q ∣ n^2 + r
q ∣ n^2 + (n + r)
```

is impossible, because the difference between the two anchored points is exactly `n`.

Therefore **one anchor-nondivisor prime wave can never cover both seats of the same `n`-shift packet**.

This checkpoint should formalize that local separation and sharpen the PRIM-L011 incidence frontier by restricting the incidence ledger to the actual coprime seats, rather than allowing nondivisor-prime hits on non-coprime offsets to count toward the budget.

Do not try to derive a contradiction yet.

---

# Preferred location

Continue in:

```text
DkMath/NumberTheory/Legendre.lean
```

for this checkpoint.

The file is large, but do not combine this implementation pass with declaration moves or a refactor. A later cleanup checkpoint may split the stabilized Legendre analysis surface.

---

# Required reconnaissance

Before coding, inspect the current Lean 4.32 / Mathlib APIs around:

```text
Nat.Coprime
Nat.Coprime.add_self_left
Nat.Coprime.add_self_right
Nat.coprime_add_self_left
Nat.coprime_add_self_right
Nat.dvd_add_iff_left
Nat.dvd_add_iff_right
Finset.image
Finset.card_image_of_injective
Finset.sum_image
Finset.filter
Finset.sum_comm
Nat.filter_coprime_Ico_eq_totient
```

The exact names above are search hints only.

In particular, find the shortest current theorem showing:

```text
Nat.Coprime n r ↔ Nat.Coprime n (n + r)
```

or prove it from a standard coprime-add-self lemma.

For the divisibility separation, avoid natural-number subtraction. Rewrite

```text
n^2 + (n + r)
```

as

```text
(n^2 + r) + n
```

and use divisibility under addition.

---

# Required implementation surface

Names below are preferred, not mandatory. Report final declaration names.

## 1. Canonical first-half coprime representatives

Define the `φ(n)` base representatives of the two-seat decomposition, preferably:

```lean
noncomputable def squareAnchorCoprimeBaseOffsets (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 n).filter (fun r => Nat.Coprime n r)
```

Expose membership:

```lean
@[simp] theorem mem_squareAnchorCoprimeBaseOffsets
    {n r : ℕ} :
    r ∈ squareAnchorCoprimeBaseOffsets n ↔
      1 ≤ r ∧ r ≤ n ∧ Nat.Coprime n r
```

Equivalent conjunction association is acceptable.

For positive `n`, prove:

```lean
theorem card_squareAnchorCoprimeBaseOffsets
    {n : ℕ} (hn : 0 < n) :
    (squareAnchorCoprimeBaseOffsets n).card = Nat.totient n
```

Reuse Mathlib's existing finite totient characterization. Do not re-prove Euler's product formula.

## 2. Coprimality is preserved by the `n`-shift

Prove:

```lean
theorem coprime_anchor_add_iff
    {n r : ℕ} :
    Nat.Coprime n (n + r) ↔ Nat.Coprime n r
```

or the reverse orientation.

This theorem should be generic and thin.

Then show that a base representative produces two coprime square offsets:

```text
r ∈ squareAnchorCoprimeBaseOffsets n
-> r ∈ squareAnchorCoprimeOffsets n
-> n + r ∈ squareAnchorCoprimeOffsets n
```

For the shifted seat, use the bounds `1 ≤ r ≤ n` to obtain:

```text
1 ≤ n + r ≤ 2*n.
```

## 3. Exact two-copy decomposition of the coprime window

Define the shifted second-half image if useful:

```lean
noncomputable def squareAnchorCoprimeShiftOffsets (n : ℕ) : Finset ℕ :=
  (squareAnchorCoprimeBaseOffsets n).image (fun r => n + r)
```

Expose membership / image semantics as needed.

Prove the exact finite decomposition:

```lean
theorem squareAnchorCoprimeOffsets_eq_base_union_shift
    (n : ℕ) :
    squareAnchorCoprimeOffsets n =
      squareAnchorCoprimeBaseOffsets n ∪
        squareAnchorCoprimeShiftOffsets n
```

and prove the base/shift parts are disjoint.

If the exact set equality creates disproportionate interval-normalization work, an equivalent pair-bijection theorem is acceptable:

```text
(base r, side Bool) ↔ squareAnchorCoprimeOffsets n
```

but prefer the direct two-Finset decomposition because it will be useful in later incidence sums.

Do not derive only the cardinality `2*φ(n)` again; PRIM-L011 already has that. The acceptance value here is the explicit packet structure.

## 4. Anchor-nondivisor support at one offset

Define the subset of old support supplied only by nondivisor primes:

```lean
noncomputable def squareOffsetAnchorNondivisorSupport
    (n r : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorNondivisorPrimes n).filter
    (fun q => SquareOffsetForbiddenBy n q r)
```

Expose exact membership:

```lean
@[simp] theorem mem_squareOffsetAnchorNondivisorSupport
    {n r q : ℕ} :
    q ∈ squareOffsetAnchorNondivisorSupport n r ↔
      Nat.Prime q ∧ q ≤ n ∧ ¬ q ∣ n ∧ q ∣ n^2 + r
```

Equivalent factoring through existing membership theorems is preferred over duplicate arithmetic proofs.

## 5. On coprime offsets, all support is nondivisor support

For positive `n`, prove that a coprime offset cannot contain an anchor-divisor prime in its old support.

Preferred exact set statement:

```lean
theorem squareOffsetPrimeSupport_eq_anchorNondivisorSupport_of_coprime
    {n r : ℕ}
    (hn : 0 < n)
    (hcop : Nat.Coprime n r) :
    squareOffsetPrimeSupport n r =
      squareOffsetAnchorNondivisorSupport n r
```

An exact membership iff theorem is acceptable if set equality is syntactically awkward.

Use the already-proved divisor-wave / coprime API from PRIM-L011 rather than rebuilding the argument from scratch.

## 6. Core `n`-shift separation theorem

Prove the key generic arithmetic statement:

```lean
theorem not_both_squareOffsetForbiddenBy_of_not_dvd_anchor
    {n q r : ℕ}
    (hqn : ¬ q ∣ n) :
    ¬ (SquareOffsetForbiddenBy n q r ∧
       SquareOffsetForbiddenBy n q (n + r))
```

No primality, bound, or coprimality assumption should be needed here. The only semantic requirement is `q ∤ n`.

Mathematical proof:

```text
q ∣ n^2 + r
q ∣ n^2 + (n+r) = (n^2+r)+n
-> q ∣ n
```

contradicting `q ∤ n`.

This theorem is the main local rigidity result of PRIM-L012.

## 7. Nondivisor supports of a packet are disjoint

Lift the previous theorem to the finite support sets:

```lean
theorem disjoint_anchorNondivisorSupport_shift
    (n r : ℕ) :
    Disjoint
      (squareOffsetAnchorNondivisorSupport n r)
      (squareOffsetAnchorNondivisorSupport n (n + r))
```

This theorem should not require `SquareOffset n r` or coprimality: it is a pure support consequence of the nondivisor definition.

Interpretation: a nondivisor prime direction may hit the left seat or the right seat of an `n`-shift packet, but never both.

## 8. Full cover forces two distinct nondivisor witnesses per coprime packet

For positive `n`, a base coprime representative `r`, and full cover, prove an explicit witness theorem of the form:

```lean
theorem exists_distinct_anchorNondivisor_cover_pair_of_fullyCovered
    {n r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n)
    (hfull : SquareOffsetsFullyCovered n) :
    ∃ p q,
      p ≠ q ∧
      p ∈ squareOffsetAnchorNondivisorSupport n r ∧
      q ∈ squareOffsetAnchorNondivisorSupport n (n + r)
```

Equivalent orientation / witness packaging is acceptable.

Proof shape:

```text
base membership
-> both r and n+r are coprime square offsets
-> full cover gives coverage of both
-> coprime coverage must come from nondivisor primes
-> both nondivisor supports are nonempty
-> disjointness forces distinct witnesses.
```

This is stronger than merely counting `2*φ(n)` incidences: it says the two seats in each reduced-residue packet require two different old prime directions.

## 9. Coprime-restricted nondivisor incidence

PRIM-L011's `squareAnchorNondivisorIncidence` counts nondivisor-prime hits on *all* square offsets, including offsets that are not coprime to `n`.

Introduce the sharper restricted ledger:

```lean
noncomputable def squareAnchorCoprimeNondivisorIncidence (n : ℕ) : ℕ :=
  ∑ r ∈ squareAnchorCoprimeOffsets n,
    (squareOffsetAnchorNondivisorSupport n r).card
```

Prove the obvious comparison:

```lean
theorem squareAnchorCoprimeNondivisorIncidence_le_nondivisorIncidence
    (n : ℕ) :
    squareAnchorCoprimeNondivisorIncidence n ≤
      squareAnchorNondivisorIncidence n
```

Prefer a finite double-count / subset proof. This theorem exposes that PRIM-L011's incidence frontier may contain hits irrelevant to the coprime subwindow.

## 10. Exact paired form of the restricted incidence

Using the base/shift decomposition, prove:

```lean
theorem squareAnchorCoprimeNondivisorIncidence_eq_sum_base_pairs
    (n : ℕ) :
    squareAnchorCoprimeNondivisorIncidence n =
      ∑ r ∈ squareAnchorCoprimeBaseOffsets n,
        ((squareOffsetAnchorNondivisorSupport n r).card +
         (squareOffsetAnchorNondivisorSupport n (n + r)).card)
```

If `n = 0` creates only degenerate interval normalization, it is acceptable to state this theorem under `0 < n`.

This is the main finite-ledger normalization of the checkpoint.

## 11. Full-cover paired totient lower bound

Under full cover, derive the sharper restricted-incidence frontier:

```lean
theorem two_mul_totient_le_coprimeNondivisorIncidence_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * Nat.totient n ≤
      squareAnchorCoprimeNondivisorIncidence n
```

The preferred proof should use either:

```text
one nonempty support per coprime seat
```

or, better, the paired form plus the fact that each packet has two disjoint nonempty support sets.

This theorem is stronger in localization than PRIM-L011's

```text
2*φ(n) ≤ squareAnchorNondivisorIncidence n
```

because the right-hand side now counts only hits occurring on the seats that actually require nondivisor coverage.

Do not claim a contradiction from this inequality.

## 12. Optional transpose by nondivisor prime

If it remains compact, define the coprime-restricted wave seats:

```lean
squareAnchorCoprimeNondivisorWaveOffsets n q :=
  (squareAnchorCoprimeOffsets n).filter
    (fun r => SquareOffsetForbiddenBy n q r)
```

for `q` in `squareAnchorNondivisorPrimes n`, and transpose the restricted incidence:

```text
squareAnchorCoprimeNondivisorIncidence n
= Σ_{q ∤ n, q≤n prime} card(coprime q-wave seats).
```

Then use `n`-shift separation to show a fixed nondivisor `q` hits at most one seat in each base packet.

A useful bound would be:

```text
card(coprime q-wave seats) ≤ Nat.totient n.
```

This is optional. Do not let the transpose dominate the checkpoint if the core packet-separation surface is already substantial.

---

# Mathematical interpretation to preserve in docstrings

State clearly:

- PRIM-L011 identified the coprime square subwindow as the region that anchor-divisor prime waves cannot cover;
- the `2*φ(n)` coprime seats are not an undifferentiated set: they form `φ(n)` pairs `(r, n+r)`;
- nondivisor prime waves are separated across each pair because simultaneous divisibility would force the prime to divide `n`;
- therefore the two seats of one coprime packet require distinct nondivisor prime directions under full cover;
- `squareAnchorCoprimeNondivisorIncidence` counts only the nondivisor incidences that actually occur on coprime seats;
- this removes irrelevant nondivisor hits on non-coprime offsets from the full-cover budget;
- all support cardinalities still count distinct prime directions, not p-adic depth;
- no probabilistic independence or prime-density statement is being used.

---

# Non-goals

Do **not** add in PRIM-L012:

- a proof of `SquareAnchoredSupportEscape`;
- a proof of Legendre's conjecture;
- a claim that the paired lower bound is impossible;
- Hall's marriage theorem / matching machinery;
- third-order inclusion-exclusion;
- Möbius inversion;
- Mertens / PNT / prime harmonic estimates;
- Jacobsthal-function machinery;
- quadratic reciprocity / quadratic-residue distribution estimates;
- p-adic valuation / prime-power Depth theory;
- RH / CFBRC dependencies;
- numerical enumeration as the generic proof method.

Do not replace the exact `n`-shift separation theorem with a heuristic statement about wave independence.

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

PRIM-L012 is complete when:

1. the `φ(n)` canonical first-half coprime representatives are exposed;
2. the coprime square window is explicitly decomposed into base and `n`-shift copies;
3. anchor-nondivisor support at one offset has exact finite semantics;
4. on coprime offsets, old prime support equals nondivisor support;
5. a nondivisor modulus cannot forbid both `r` and `n+r`;
6. the two nondivisor support sets of one `n`-shift packet are disjoint;
7. under full cover, each coprime packet has two distinct nondivisor prime witnesses;
8. the coprime-restricted nondivisor incidence ledger is defined;
9. it is normalized as a sum over base packets;
10. full cover implies `2*Nat.totient n ≤ squareAnchorCoprimeNondivisorIncidence n`;
11. no Legendre proof, analytic estimate, or higher-order inclusion-exclusion is smuggled into the checkpoint;
12. requested builds and audits are clean.

Stop after PRIM-L012. Do not begin a matching/contradiction argument in this implementation pass.

---

# Review questions after PRIM-L012

The next review should decide whether the packet separation has created genuine leverage beyond the previous incidence lower bound.

In particular inspect:

```text
A. each reduced-residue packet requires two distinct nondivisor prime directions
B. a fixed nondivisor q can occupy at most one side of each packet
C. the two sides correspond to two distinct q-phases in the base coordinate r
D. the restricted incidence removes non-coprime "waste" from PRIM-L011
E. whether a finite bipartite/matching obstruction is now visible
F. whether the quotient-variable transform q*k = n^2 + r exposes coprimality with n
```

Do not automatically introduce Hall/matching machinery. First inspect the Lean surface and determine whether the packet constraints are stronger than ordinary incidence bookkeeping.