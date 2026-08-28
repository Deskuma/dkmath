# Codex Instruction — PRIM-L008 Square-Anchor Wave Carry Decomposition

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-L007 is complete.

The Legendre application layer now has an exact local occupancy formula for every positive modulus `m`:

```text
(squareWaveOffsets n m).card
  = (n^2 + 2*n) / m - n^2 / m
```

with prime and pair-overlap specializations, and the total incidence ledger is exactly:

```text
squareCoverIncidenceCount n
  = ∑ q ∈ primeScalesUpTo n,
      ((n^2 + 2*n) / q - n^2 / q)
```

The previous checkpoints also established:

```text
SquareOffsetsFullyCovered n
  -> 2*n ≤ squareCoverIncidenceCount n
```

and, under full cover,

```text
squareCoverIncidenceCount n
  = 2*n + squareCoverOverlapExcess n.
```

PRIM-L007 therefore converted local wave occupancy from a periodic/density intuition into exact endpoint quotient arithmetic.

The next question is what part of that quotient difference is generic periodic occupancy and what part is specific to the square anchor `n^2`.

---

# Goal

Decompose each exact local wave count into:

```text
complete periods in the window
+
at most one boundary carry caused by the anchor phase
```

Mathematically, for `m > 0` and window length `L = 2*n`, expose the identity

```text
floor((n^2 + L)/m) - floor(n^2/m)
  = floor(L/m) + carry(n,m)
```

where the carry is always `0` or `1` and is controlled by the remainder interaction

```text
(n^2 % m) + (L % m).
```

This checkpoint should make the square-anchor correction explicit and then transpose it through the existing incidence ledger.

Do **not** attempt to prove the carry budget is too small or that full cover is impossible.

---

# Preferred location

Continue in:

```text
DkMath/NumberTheory/Legendre.lean
```

unless the file has become operationally unwieldy and a sibling audit module can be introduced without import-cycle or public-API churn.

Do not move existing declarations in this checkpoint.

---

# Required reconnaissance

Before coding, inspect the current Lean 4.32 / Mathlib API around:

```text
Nat.add_div
Nat.add_mod
Nat.div_add_mod
Nat.mod_lt
Nat.div_eq_of_lt
Nat.div_eq_sub_mod_div
Nat.dvd_iff_mod_eq_zero
Finset.sum_add_distrib
Finset.sum_congr
```

The exact names above are search hints only.

Prefer deriving the new decomposition from the already-proved

```text
card_squareWaveOffsets_eq_div_sub_div
```

plus standard quotient/remainder identities. Do not build another finite bijection proof for the same occupancy count.

---

# Required implementation surface

Names below are preferred, not mandatory. Report final declaration names.

## 1. Define the square-anchor wave carry

Introduce a small natural-number correction term, preferably:

```lean
def squareWaveCarry (n m : ℕ) : ℕ :=
  ((n ^ 2 % m) + ((2 * n) % m)) / m
```

This definition is intended for positive `m`; behavior at `m = 0` does not need a special semantic interpretation.

Alternative equivalent definitions are acceptable if they make the current Mathlib API substantially cleaner, but preserve the idea that this is the one-bit correction produced when the anchor remainder and window remainder cross a modulus boundary.

## 2. Carry is at most one

For positive modulus prove:

```lean
theorem squareWaveCarry_le_one
    {n m : ℕ} (hm : 0 < m) :
    squareWaveCarry n m ≤ 1
```

If convenient, also expose the exact range:

```text
squareWaveCarry n m = 0 ∨ squareWaveCarry n m = 1.
```

Do not encode this as a probability or density.

## 3. Exact baseline-plus-carry occupancy

Prove the main decomposition:

```lean
theorem card_squareWaveOffsets_eq_div_add_carry
    {n m : ℕ} (hm : 0 < m) :
    (squareWaveOffsets n m).card =
      (2 * n) / m + squareWaveCarry n m
```

This should be a rewrite of the PRIM-L007 quotient-difference theorem, not a new counting argument.

This theorem is the main acceptance target.

## 4. Carry threshold characterization

Expose the arithmetic condition deciding whether the extra hit exists.

Preferred form:

```lean
theorem squareWaveCarry_eq_one_iff
    {n m : ℕ} (hm : 0 < m) :
    squareWaveCarry n m = 1 ↔
      m ≤ (n ^ 2 % m) + ((2 * n) % m)
```

and, if thin:

```lean
theorem squareWaveCarry_eq_zero_iff
    {n m : ℕ} (hm : 0 < m) :
    squareWaveCarry n m = 0 ↔
      (n ^ 2 % m) + ((2 * n) % m) < m
```

Equivalent `<` / `≤` formulations are acceptable.

The point is to expose the carry as a deterministic boundary event, not merely prove the upper bound.

## 5. Anchor-divisor waves have zero carry

Prove the important square-anchor specialization:

```lean
theorem squareWaveCarry_eq_zero_of_dvd_anchor
    {n m : ℕ} (hm : 0 < m) (hmn : m ∣ n) :
    squareWaveCarry n m = 0
```

The mathematical reason is:

```text
m ∣ n
-> m ∣ n^2
-> n^2 % m = 0
and m ∣ 2*n
-> (2*n) % m = 0.
```

Then expose the exact occupancy corollary:

```lean
theorem card_squareWaveOffsets_eq_div_of_dvd_anchor
    {n m : ℕ} (hm : 0 < m) (hmn : m ∣ n) :
    (squareWaveOffsets n m).card = (2 * n) / m
```

This is the first explicit distinction between old prime directions that divide the anchor `n` and those that do not.

## 6. Prime specialization

Add a thin wrapper for old prime waves:

```lean
theorem card_squarePrimeWaveOffsets_eq_div_add_carry
    {n q : ℕ} (hq : Nat.Prime q) :
    (squarePrimeWaveOffsets n q).card =
      (2 * n) / q + squareWaveCarry n q
```

and, if cheap:

```lean
theorem card_squarePrimeWaveOffsets_eq_div_of_dvd_anchor
    {n q : ℕ}
    (hq : Nat.Prime q)
    (hqn : q ∣ n) :
    (squarePrimeWaveOffsets n q).card = (2 * n) / q
```

Do not add prime-power depth semantics here.

## 7. Incidence baseline and total carry

Define finite bookkeeping quantities, preferably:

```lean
noncomputable def squareCoverBaselineIncidence (n : ℕ) : ℕ :=
  ∑ q ∈ primeScalesUpTo n, (2 * n) / q

noncomputable def squareAnchorCarryCount (n : ℕ) : ℕ :=
  ∑ q ∈ primeScalesUpTo n, squareWaveCarry n q
```

Then prove the exact decomposition:

```lean
theorem squareCoverIncidenceCount_eq_baseline_add_carry
    (n : ℕ) :
    squareCoverIncidenceCount n =
      squareCoverBaselineIncidence n + squareAnchorCarryCount n
```

Use the existing prime-wave transpose and the new per-wave decomposition.

Do not replace the exact finite sum by an analytic approximation.

## 8. Carry budget is finite and one-bit per prime

Prove the elementary finite bound:

```lean
theorem squareAnchorCarryCount_le_card_primeScalesUpTo
    (n : ℕ) :
    squareAnchorCarryCount n ≤ (primeScalesUpTo n).card
```

This uses only `squareWaveCarry_le_one` for prime moduli.

This theorem is bookkeeping only. Do not infer local escape from it.

## 9. Optional: divisor/nondivisor partition

If clean, define or expose the partition:

```lean
squareAnchorDivisorPrimes n
squareAnchorNondivisorPrimes n
```

as filters of `primeScalesUpTo n` by `q ∣ n` / `¬ q ∣ n`.

Then prove that divisor-prime carries vanish, so the total carry may be summed only over nondivisor primes.

A theorem of the conceptual form

```text
squareAnchorCarryCount n
  = ∑ q in squareAnchorNondivisorPrimes n, squareWaveCarry n q
```

is useful but optional.

Do not create this partition if it causes disproportionate Finset bookkeeping.

## 10. Optional: phase interpretation of the carry

If it is short, connect the carry to the already-defined forbidden phase

```text
squareAnchorForbiddenResidue n m
```

For positive `m`, the extra hit beyond `(2*n)/m` should correspond to the nonzero forbidden phase falling into the terminal partial period of length `(2*n) % m`.

A useful conceptual theorem would be equivalent to:

```text
squareWaveCarry n m = 1
↔
0 < squareAnchorForbiddenResidue n m
  ∧ squareAnchorForbiddenResidue n m ≤ (2*n) % m.
```

Do not force this theorem if truncated-subtraction normalization becomes the dominant work of the checkpoint. The remainder-threshold characterization in section 4 is sufficient for acceptance.

## 11. Full-cover budget identity

Using the existing overlap-excess identity and the new incidence decomposition, prove under full cover:

```lean
theorem baseline_add_carry_eq_two_mul_add_overlapExcess_of_fullyCovered
    {n : ℕ} (hfull : SquareOffsetsFullyCovered n) :
    squareCoverBaselineIncidence n + squareAnchorCarryCount n =
      2 * n + squareCoverOverlapExcess n
```

Equivalent orientation is acceptable.

This is an **exact budget identity**, not a contradiction.

It separates the full-cover bookkeeping into:

```text
complete-period baseline
+ square-anchor boundary carries
=
mandatory one hit per offset
+ repeated-cover overlap waste.
```

---

# Interpretation to preserve in docstrings

State clearly:

- PRIM-L007 gave exact local occupancy by quotient difference;
- PRIM-L008 splits that occupancy into complete periods plus a deterministic `0/1` boundary carry;
- the carry is where the actual square anchor `n^2` enters the occupancy count beyond generic period length;
- if a modulus divides the anchor `n`, its carry vanishes exactly;
- `squareAnchorCarryCount` counts boundary corrections across distinct old prime directions, not p-adic valuation depth;
- the full-cover budget identity is necessary bookkeeping only and does not prove full cover impossible.

---

# Non-goals

Do **not** add in PRIM-L008:

- a proof of `SquareAnchoredSupportEscape`;
- a proof of Legendre's conjecture;
- an assertion that the carry budget is insufficient for full cover;
- Mertens / PNT / prime harmonic estimates;
- asymptotic density arguments;
- Jacobsthal-function machinery;
- full inclusion-exclusion;
- Möbius inversion;
- quadratic-residue distribution estimates;
- prime-power valuation / Depth theory;
- RH / CFBRC imports;
- category theory.

Do not use numerical enumeration for generic theorems.

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

PRIM-L008 is complete when:

1. a finite `0/1` square-wave carry term is exposed;
2. carry is proved at most one for positive modulus;
3. local occupancy is exactly `floor(2*n/m) + carry`;
4. the remainder threshold deciding carry is formalized;
5. moduli dividing the anchor have zero carry and exact baseline occupancy;
6. the prime-wave specialization is available;
7. total incidence is exactly baseline incidence plus total square-anchor carry;
8. total carry is bounded by the number of old prime directions;
9. under full cover, the new baseline/carry ledger is connected exactly to `2*n + overlapExcess`;
10. no analytic estimate or Legendre provider is smuggled into the checkpoint;
11. requested builds and audits are clean.

Stop after PRIM-L008. Do not begin a contradiction or escape proof in this implementation pass.

---

# Review questions after PRIM-L008

The next review should inspect whether the carry decomposition exposes genuinely square-specific rigidity beyond generic periodic occupancy.

In particular compare:

```text
A. primes q dividing n: zero carry, phase 0
B. primes q not dividing n: nonzero square-anchor phase, possible one-bit carry
C. pair moduli p*q: the same carry mechanism controls overlap occupancy
D. full-cover overlap excess versus the exact baseline+carry budget
```

Only after seeing this Lean surface should the next route be chosen between:

```text
higher squarefree intersection carries
quadratic-residue phase constraints
anchor-divisor / nondivisor partition
or a different Primitive Origin localization route.
```
