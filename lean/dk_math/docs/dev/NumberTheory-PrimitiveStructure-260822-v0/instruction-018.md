# Codex Instruction — PRIM-L011 Anchor-Divisor / Coprime-Offset Partition

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-L010 is complete.

The Legendre application layer now has an exact first- and second-order finite cover calculus:

```text
prime-wave occupancy
  = complete-period baseline + 0/1 square-anchor carry

pair overlap
  = product-wave occupancy

pairOverlapCount
  = nearBaseline + nearCarry + activeFarCount
```

with the exact near/far split:

```text
p*q ≤ 2*n   -> near product wave
2*n < p*q   -> far product wave, occupancy = 0/1 carry
```

and the full-cover second-order frontier already rewrites through this localized pair budget.

PRIM-L011 should not escalate to third-order inclusion-exclusion. Instead it should exploit a different square-specific fact that has so far only appeared indirectly through carry-zero lemmas:

```text
q ∣ n
```

forces the square-anchor forbidden phase to be zero.

For such a prime `q`:

```text
q ∣ n^2 + r  ↔  q ∣ r.
```

Therefore the old prime directions that divide the anchor `n` cover exactly the offsets sharing a prime factor with `n`. The offsets coprime to `n` cannot be covered by any anchor-divisor prime and, under hypothetical full cover, must be covered entirely by old primes `q ≤ n` with `q ∤ n`.

This is a genuinely square-anchor-specific partition and should be exposed exactly before any further counting escalation.

---

# Goal

Split the old prime world into:

```text
anchor-divisor primes:    q ≤ n, q prime, q ∣ n
anchor-nondivisor primes: q ≤ n, q prime, q ∤ n
```

Then prove the exact local semantics:

```text
anchor-divisor coverage of r
  ↔ n and r are not coprime
```

for positive `n`.

Consequently, on offsets `r` with `Nat.Coprime n r`, ordinary square-offset coverage is equivalent to coverage by the nondivisor-prime world alone.

Finally package the coprime offsets in the square window and derive the corresponding finite full-cover necessary condition. If the current Mathlib API permits a clean exact cardinality proof, identify the number of coprime offsets in `1..2*n` with `2 * Nat.totient n`.

Do **not** prove that the nondivisor-prime world is insufficient to cover these offsets.

---

# Preferred location

Continue in:

```text
DkMath/NumberTheory/Legendre.lean
```

for this checkpoint.

The file is large, but do not mix theorem relocation/refactoring into the same implementation pass.

---

# Required reconnaissance

Before coding, inspect the current Lean 4.32 / Mathlib APIs around:

```text
Nat.Coprime
Nat.coprime_comm
Nat.not_coprime_iff_dvd
Nat.exists_prime_and_dvd
Nat.exists_prime_and_dvd
Nat.dvd_add_iff_left
Nat.dvd_add_iff_right
Nat.dvd_pow
Nat.Prime.dvd_of_dvd_pow
Nat.totient
Nat.totient_eq_card_coprime
Finset.filter
Finset.Icc
Finset.card_filter
Finset.sum_filter
```

The exact theorem names above are search hints only. Use the current API actually present.

Search first for an existing characterization equivalent to:

```text
¬ Nat.Coprime n r
↔ ∃ q, Nat.Prime q ∧ q ∣ n ∧ q ∣ r
```

under the natural nontriviality assumptions. Do not build a new gcd/prime-factor framework if Mathlib already contains the necessary bridge.

Also inspect whether Mathlib already has interval-cardinality results for numbers coprime to `n` over one or two complete periods. If not, a short finite bijection/periodicity proof is acceptable.

---

# Required implementation surface

Names below are preferred, not mandatory. Report final declaration names.

## 1. Partition the old prime world by whether the prime divides the anchor

Define:

```lean
noncomputable def squareAnchorDivisorPrimes (n : ℕ) : Finset ℕ := by
  classical
  exact (primeScalesUpTo n).filter (fun q => q ∣ n)

noncomputable def squareAnchorNondivisorPrimes (n : ℕ) : Finset ℕ := by
  classical
  exact (primeScalesUpTo n).filter (fun q => ¬ q ∣ n)
```

Expose exact membership theorems:

```lean
q ∈ squareAnchorDivisorPrimes n
↔ Nat.Prime q ∧ q ≤ n ∧ q ∣ n

q ∈ squareAnchorNondivisorPrimes n
↔ Nat.Prime q ∧ q ≤ n ∧ ¬ q ∣ n
```

Also prove the two sets form a disjoint partition of `primeScalesUpTo n` if this is thin.

Do not introduce a new generic PrimeWorld partition abstraction in this checkpoint.

## 2. Divisor-prime waves are exactly zero-phase offset divisibility

Prove the generic anchor-divisor simplification:

```lean
theorem squareOffsetForbiddenBy_iff_dvd_offset_of_dvd_anchor
    {n q r : ℕ}
    (hqn : q ∣ n) :
    SquareOffsetForbiddenBy n q r ↔ q ∣ r
```

No primality hypothesis should be mathematically necessary.

Then specialize the already-defined forbidden residue:

```lean
theorem squareAnchorForbiddenResidue_eq_zero_of_dvd_anchor
    {n q : ℕ}
    (hq : 0 < q)
    (hqn : q ∣ n) :
    squareAnchorForbiddenResidue n q = 0
```

Reuse existing carry-zero facts where appropriate; do not duplicate their proofs.

## 3. Nondivisor prime waves have nonzero square-anchor phase

For a prime not dividing `n`, prove:

```lean
theorem squareAnchorForbiddenResidue_ne_zero_of_prime_not_dvd_anchor
    {n q : ℕ}
    (hq : Nat.Prime q)
    (hqn : ¬ q ∣ n) :
    squareAnchorForbiddenResidue n q ≠ 0
```

Equivalent positive form is acceptable:

```text
0 < squareAnchorForbiddenResidue n q.
```

The proof should use that `q ∤ n` for prime `q` implies `q ∤ n^2`, hence `n^2 % q ≠ 0`.

This theorem is phase classification only; do not infer carry `= 1` from it.

## 4. Coverage by the two anchor classes

Define small semantic predicates or finite support subsets, preferably:

```lean
def SquareOffsetCoveredByAnchorDivisorPrime (n r : ℕ) : Prop :=
  ∃ q, q ∈ squareAnchorDivisorPrimes n ∧ SquareOffsetForbiddenBy n q r


def SquareOffsetCoveredByAnchorNondivisorPrime (n r : ℕ) : Prop :=
  ∃ q, q ∈ squareAnchorNondivisorPrimes n ∧ SquareOffsetForbiddenBy n q r
```

Then prove exact splitting:

```lean
theorem squareOffsetCovered_iff_anchorDivisor_or_nondivisor
    {n r : ℕ} :
    SquareOffsetCovered n r ↔
      SquareOffsetCoveredByAnchorDivisorPrime n r ∨
      SquareOffsetCoveredByAnchorNondivisorPrime n r
```

Prefer deriving this only from the Finset partition / membership semantics.

## 5. Main semantic theorem: anchor-divisor coverage iff non-coprime offset

For positive anchor, prove:

```lean
theorem squareOffsetCoveredByAnchorDivisorPrime_iff_not_coprime
    {n r : ℕ}
    (hn : 0 < n) :
    SquareOffsetCoveredByAnchorDivisorPrime n r ↔
      ¬ Nat.Coprime n r
```

This is a major acceptance target.

Forward direction:

```text
q prime, q ∣ n, q ∣ n^2+r
-> q ∣ r
-> common prime divisor
-> not coprime.
```

Reverse direction:

```text
not coprime
-> some prime q divides both n and r
-> q ≤ n because n > 0
-> q is an old anchor-divisor prime
-> q divides n^2+r.
```

Do not hide the `q ≤ n` step in an unjustified simplification.

## 6. Coprime offsets can only be covered by nondivisor primes

Derive, for positive `n` and `Nat.Coprime n r`:

```lean
theorem squareOffsetCovered_iff_anchorNondivisor_of_coprime
    {n r : ℕ}
    (hn : 0 < n)
    (hcop : Nat.Coprime n r) :
    SquareOffsetCovered n r ↔
      SquareOffsetCoveredByAnchorNondivisorPrime n r
```

This should be a thin consequence of sections 4 and 5.

This is the semantic heart of PRIM-L011:

```text
coprime offset
-> anchor-divisor waves are unavailable
-> any cover must come from a nonzero square-anchor phase q ∤ n.
```

## 7. Finite coprime square-offset set

Define:

```lean
noncomputable def squareAnchorCoprimeOffsets (n : ℕ) : Finset ℕ := by
  classical
  exact (squareOffsets n).filter (fun r => Nat.Coprime n r)
```

Expose membership:

```lean
r ∈ squareAnchorCoprimeOffsets n
↔ SquareOffset n r ∧ Nat.Coprime n r
```

If convenient, also define the complementary non-coprime offset set, but it is not required.

## 8. Exact cardinality of coprime offsets — strongly preferred

For positive `n`, prove if reasonably compact:

```lean
theorem card_squareAnchorCoprimeOffsets
    {n : ℕ}
    (hn : 0 < n) :
    (squareAnchorCoprimeOffsets n).card = 2 * Nat.totient n
```

Mathematical reason: the interval `1..2*n` consists of two complete residue blocks modulo `n`, and coprimality with `n` is periodic with period `n`.

Preferred proof sources:

- an existing Mathlib interval/totient cardinality theorem, if present;
- otherwise split `1..2*n` into the two length-`n` blocks and use translation by `n` plus `Nat.totient_eq_card_coprime`.

Do not use analytic estimates for `Nat.totient n`.

If current Mathlib interval APIs make this theorem disproportionately large, stop after proving an exact two-block decomposition and report the obstruction. Do not spend the entire checkpoint on Finset normalization.

## 9. Nondivisor-prime incidence on the coprime subwindow

Define a finite incidence ledger restricted to the prime directions that do not divide `n`:

```lean
noncomputable def squareAnchorNondivisorIncidence (n : ℕ) : ℕ :=
  ∑ q ∈ squareAnchorNondivisorPrimes n,
    (squarePrimeWaveOffsets n q).card
```

An equivalent local-support double count is acceptable.

Then prove that hypothetical full cover must supply at least one nondivisor-prime incidence for every coprime offset:

```lean
theorem card_squareAnchorCoprimeOffsets_le_nondivisorIncidence_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    (squareAnchorCoprimeOffsets n).card ≤
      squareAnchorNondivisorIncidence n
```

The proof should use section 6, not a generic density argument.

If section 8 is available, expose the direct totient frontier:

```lean
theorem two_mul_totient_le_nondivisorIncidence_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * Nat.totient n ≤ squareAnchorNondivisorIncidence n
```

This is a finite necessary condition only.

## 10. Exact arithmetic form of the nondivisor incidence — strongly preferred

Reuse the existing prime-wave occupancy decomposition to prove:

```lean
theorem squareAnchorNondivisorIncidence_eq_sum_div_add_carry
    (n : ℕ) :
    squareAnchorNondivisorIncidence n =
      ∑ q ∈ squareAnchorNondivisorPrimes n,
        ((2 * n) / q + squareWaveCarry n q)
```

Then, if section 8 succeeded, a thin full-cover arithmetic frontier may state:

```text
2 * Nat.totient n
≤ Σ_{q≤n, q prime, q∤n}
    (floor(2*n/q) + carry(n,q)).
```

Do not attempt to prove this inequality false.

---

# Interpretation to preserve in docstrings

State clearly:

- primes dividing the anchor `n` have forbidden phase zero and cover exactly offsets divisible by those primes;
- collectively, anchor-divisor prime waves cover exactly the offsets not coprime to `n`;
- coprime offsets in the square window therefore cannot use any anchor-divisor wave;
- under full cover they must be supplied entirely by old primes `q ≤ n` with `q ∤ n`;
- for those nondivisor primes the forbidden phase is nonzero and square-specific;
- `Nat.totient` is used only as an exact finite cardinality name for coprime residue classes, not as an analytic density estimate;
- the resulting inequality is a necessary full-cover frontier, not a proof of Legendre.

Keep this distinct from p-adic depth: the partition is by whether a prime direction divides the anchor at all, not by valuation exponent.

---

# Non-goals

Do **not** add in PRIM-L011:

- a proof of `SquareAnchoredSupportEscape`;
- a proof of Legendre's conjecture;
- an assertion that nondivisor primes cannot cover all coprime offsets;
- asymptotic estimates for `Nat.totient`;
- Mertens / PNT / prime harmonic bounds;
- third-order inclusion-exclusion;
- Möbius inversion;
- Jacobsthal-function machinery;
- quadratic-residue distribution estimates;
- p-adic valuation / prime-power Depth theory;
- RH / CFBRC imports;
- numerical enumeration as the generic proof method.

Do not replace exact finite coprimality semantics by probabilistic independence language.

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

PRIM-L011 is complete when:

1. old primes are partitioned into anchor divisors and nondivisors;
2. divisor-prime waves are proved equivalent to ordinary divisibility of the offset;
3. divisor-prime forbidden phase is zero;
4. nondivisor-prime forbidden phase is proved nonzero;
5. ordinary square coverage splits exactly into divisor/nondivisor coverage;
6. for positive `n`, anchor-divisor coverage is exactly `¬ Nat.Coprime n r`;
7. coprime offsets can be covered only by anchor-nondivisor primes;
8. the finite coprime square-offset set is exposed;
9. full cover implies a finite nondivisor-incidence lower bound on the coprime subwindow;
10. if feasible without disproportionate API work, the coprime subwindow cardinality is identified with `2 * Nat.totient n` and the corresponding totient frontier is exposed;
11. no Legendre proof, analytic estimate, or third-order inclusion-exclusion is smuggled into the checkpoint;
12. requested builds and audits are clean.

Stop after PRIM-L011. Do not begin a contradiction proof in this implementation pass.

---

# Review questions after PRIM-L011

After this checkpoint, compare two square-specific localization mechanisms:

```text
A. near/far pair localization by product size p*q versus 2*n
B. anchor-divisor/nondivisor localization by q ∣ n versus q ∤ n
```

The key question is whether the coprime subwindow gives substantially more rigidity than the global incidence ledger.

Review these next routes only after seeing the Lean surface:

```text
1. exact cardinality / geometry of the coprime subwindow if not already closed
2. nondivisor-prime carry/phase compatibility on coprime offsets
3. support-product / squarefree-kernel bounds for a covered coprime offset
4. Primitive Origin / first-occurrence localization
5. stop incidence escalation if the new frontier is still only a loose counting inequality
```

Do not automatically escalate to higher-order inclusion-exclusion.