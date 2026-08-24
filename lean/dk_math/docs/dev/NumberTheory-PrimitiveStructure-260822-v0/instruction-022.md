# Codex Instruction — PRIM-L015 Quotient Co-Support / Direction-Depth Dichotomy

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-L014 is complete.

For every coprime old-prime support incidence `(q,r)` the Legendre layer now has the complementary quotient

```text
k = squareOffsetSupportQuotient n q r = (n^2 + r) / q
```

with exact reconstruction

```text
q*k = n^2 + r,
```

and, for an old nondivisor support prime in the square window,

```text
q ≤ n < k,
Nat.Coprime n k.
```

All coprime nondivisor support incidences are represented by

```text
squareAnchorCoprimeSupportIncidences n
```

and their quotient image by

```text
squareAnchorCoprimeGlobalQuotients n.
```

PRIM-L014 proved that a quotient collision between distinct prime waves forces `n < 4`. Hence for `4 ≤ n` the quotient projection is globally injective and preserves the restricted incidence cardinality. Under full cover:

```text
2 * Nat.totient n ≤ (squareAnchorCoprimeGlobalQuotients n).card.
```

This is a strong collision-rigidity theorem, but quotient cardinality alone still leaves a large ambient range. The next checkpoint should inspect the arithmetic content carried *inside* each quotient.

---

# Goal

Expose how the old-prime support of an anchored point

```text
n^2 + r
```

transforms after dividing by one chosen support prime `p`.

The central elementary fact is:

```text
p | n^2+r
q | n^2+r
p ≠ q
p,q prime
```

iff, after writing

```text
p * k = n^2+r,
```

the other prime direction survives in the quotient:

```text
q | k.
```

Thus division by `p` cannot remove any *other* prime direction. The only ambiguity is whether the `p` direction itself survives in `k`, which is exactly a prime-power-depth question (`p^2 | n^2+r`).

PRIM-L015 should formalize this as a Direction/Depth separation layer:

```text
off-diagonal old-prime support is preserved exactly in the quotient;
only the selected prime direction may disappear by losing one valuation level.
```

Then use the existing square-Body composite detector to characterize non-prime quotients as arising from either:

```text
another old prime direction
or
self-prime depth persisting after division.
```

Do not prove Legendre, do not begin an infinite descent, and do not import p-adic valuation machinery unless genuinely necessary. The intended checkpoint should remain elementary divisibility plus existing Primitive APIs.

---

# Preferred location

Continue in:

```text
DkMath/NumberTheory/Legendre.lean
```

for this bounded checkpoint.

Do not move PRIM-L003–L014 declarations while adding this layer. If the file size now makes a split operationally necessary, use a sibling module importing `DkMath.NumberTheory.Legendre`, but do not create an import cycle and report the final public path.

---

# Required reconnaissance

Before coding, inspect current Lean 4.32 / Mathlib APIs around:

```text
Nat.Prime.dvd_mul
Nat.Prime.dvd_of_dvd_pow
Nat.dvd_prime
Nat.mul_dvd_mul_left
Nat.mul_dvd_mul_iff_left
Nat.Coprime
Finset.erase
Finset.mem_erase
Finset.card_erase_of_mem
Finset.card_le_card
```

Also inspect existing DkMath declarations already available in the file:

```text
squareOffsetAnchorNondivisorSupport
mem_squareOffsetAnchorNondivisorSupport
squareOffsetSupportQuotient
mul_squareOffsetSupportQuotient_eq
anchor_lt_squareOffsetSupportQuotient
coprime_anchor_squareOffsetSupportQuotient_iff
exists_prime_dvd_le_of_not_prime_of_le_squareBody
squareBody
```

Do not rebuild generic prime-divisor or square-Body closure machinery.

---

# Required implementation surface

Names below are preferred, not mandatory. Report final names.

## 1. Old-prime support carried by one quotient

Define the old nondivisor prime directions dividing one complementary quotient:

```lean
noncomputable def squareQuotientAnchorNondivisorSupport
    (n p r : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorNondivisorPrimes n).filter
    (fun q => q ∣ squareOffsetSupportQuotient n p r)
```

Expose exact membership:

```lean
@[simp] theorem mem_squareQuotientAnchorNondivisorSupport
    {n p r q : ℕ} :
    q ∈ squareQuotientAnchorNondivisorSupport n p r ↔
      Nat.Prime q ∧ q ≤ n ∧ ¬ q ∣ n ∧
        q ∣ squareOffsetSupportQuotient n p r
```

This set records distinct old prime directions in the quotient, not valuation exponents.

## 2. Quotient support is contained in point support

Assume `p` is a valid support divisor of `n^2+r` so that

```text
p * quotient = n^2+r.
```

Prove a theorem of the form:

```lean
theorem squareQuotientAnchorNondivisorSupport_subset_offsetSupport
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    squareQuotientAnchorNondivisorSupport n p r ⊆
      squareOffsetAnchorNondivisorSupport n r
```

Any old prime dividing the quotient also divides the original anchored point.

## 3. Exact off-diagonal support transfer

For `p` itself chosen from the offset support, prove the key equivalence for every `q ≠ p`:

```lean
theorem mem_quotientSupport_iff_mem_offsetSupport_of_ne
    {n p q r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hqp : q ≠ p) :
    q ∈ squareQuotientAnchorNondivisorSupport n p r ↔
      q ∈ squareOffsetAnchorNondivisorSupport n r
```

The reverse direction should use primality of `q`: from

```text
q | p*k
```

and `q ≠ p`, deduce `q | k`.

Do not use unique factorization machinery for this elementary step.

## 4. Erased-support equality

Package the previous theorem as the exact finite Direction statement:

```lean
theorem erase_squareQuotientSupport_eq_erase_offsetSupport
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    (squareQuotientAnchorNondivisorSupport n p r).erase p =
      (squareOffsetAnchorNondivisorSupport n r).erase p
```

Equivalent orientation is acceptable.

Semantic meaning:

```text
after dividing by p,
every other old prime direction survives exactly.
```

This is a primary acceptance target.

## 5. Cardinality sandwich

Derive finite cardinality bounds showing that quotient support can differ from offset support by at most the selected direction:

```lean
theorem offsetSupport_card_sub_one_le_quotientSupport_card
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    (squareOffsetAnchorNondivisorSupport n r).card - 1 ≤
      (squareQuotientAnchorNondivisorSupport n p r).card
```

and

```lean
theorem quotientSupport_card_le_offsetSupport_card
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    (squareQuotientAnchorNondivisorSupport n p r).card ≤
      (squareOffsetAnchorNondivisorSupport n r).card
```

If thin, expose the two-value conclusion:

```text
quotientSupport.card = offsetSupport.card - 1
or
quotientSupport.card = offsetSupport.card.
```

Do not interpret the second case as a valuation theorem yet; section 6 identifies the exact elementary depth bit.

## 6. Selected-direction persistence = square divisibility

Strongly preferred if the current Nat divisibility API makes it clean.

For a valid chosen support prime `p`, prove:

```lean
theorem selectedPrime_mem_quotientSupport_iff_square_dvd
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    p ∈ squareQuotientAnchorNondivisorSupport n p r ↔
      p ^ 2 ∣ n ^ 2 + r
```

An equivalent `p * p` spelling is acceptable.

This theorem should be documented as an elementary one-step **depth persistence** statement:

```text
dividing by p removes one p-level;
p remains iff at least one additional p-level was present.
```

Do not introduce `padicValNat` solely for this result.

If available cleanly, derive the exact support cases:

```text
¬ p^2 | n^2+r
-> quotientSupport = offsetSupport.erase p

p^2 | n^2+r
-> quotientSupport = offsetSupport
```

These are preferred but may be omitted if they make the checkpoint disproportionately large.

## 7. Quotient stays inside the certified square Body

For a coprime support incidence, expose a convenient upper bound for the quotient.

Preferred theorem shape:

```lean
theorem squareOffsetSupportQuotient_le_squareBody
    {n p r : ℕ}
    (hr : SquareOffset n r)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    squareOffsetSupportQuotient n p r ≤ squareBody n
```

A sharper upper bound is welcome if essentially free, but do not optimize constants for their own sake.

Together with the existing `n < quotient`, this lets the generic `SquareBody` composite detector apply to the quotient itself.

## 8. Composite quotient has an old nondivisor prime support

For positive `n`, coprime seat `r`, and chosen support prime `p`, prove:

```lean
theorem exists_old_prime_dvd_quotient_of_not_prime
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hnotprime : ¬ Nat.Prime (squareOffsetSupportQuotient n p r)) :
    ∃ q,
      q ∈ squareQuotientAnchorNondivisorSupport n p r
```

Use the existing square-Body theorem. The quotient is already larger than `n`, hence larger than `1`, and is coprime to `n`; any bounded prime divisor obtained from the square-Body detector is therefore an anchor-nondivisor prime.

This is not an assertion that the quotient is usually composite.

## 9. Direction-or-depth dichotomy for a non-prime quotient

Combine the previous pieces into the main semantic theorem.

Preferred witness form:

```lean
theorem not_prime_quotient_iff_self_depth_or_distinct_support
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    ¬ Nat.Prime (squareOffsetSupportQuotient n p r) ↔
      p ∣ squareOffsetSupportQuotient n p r ∨
      ∃ q,
        q ≠ p ∧
        q ∈ squareOffsetAnchorNondivisorSupport n r
```

Equivalent orientation / use of `p^2 ∣ n^2+r` in the self-depth branch is acceptable and may be clearer:

```text
quotient non-prime
iff
selected p-direction persists at depth ≥ 2
or
another old prime direction exists.
```

The reverse direction should use `p ≤ n < quotient` (or `q ≤ n < quotient`) to rule out quotient primality when such a proper prime divisor exists.

This theorem is the main acceptance target of PRIM-L015.

## 10. Optional prime-quotient normal form

If section 9 makes this a short corollary, expose:

```text
Nat.Prime quotient
iff
offset support is exactly {p}
and p does not persist in the quotient.
```

A preferred finite-set form is:

```lean
Nat.Prime (squareOffsetSupportQuotient n p r) ↔
  squareOffsetAnchorNondivisorSupport n r = {p} ∧
  ¬ p ∣ squareOffsetSupportQuotient n p r
```

under the same positive/coprime/support assumptions.

If section 6 is present, an equivalent form using `¬ p^2 ∣ n^2+r` is also useful.

This would identify exactly when an old support incidence factors the anchored point as

```text
small old prime p × large prime quotient k.
```

Do not call `k` primitive unless you additionally prove the corresponding existing `FreshPrimeDirection` predicate in a thin corollary.

## 11. Optional bridge to Primitive Direction

Only if the quotient-prime normal form is already available and the bridge is very thin:

```text
Nat.Prime k and n < k
-> FreshPrimeDirection (primeScalesUpTo n) k k
```

or the exact currently-defined argument order for `FreshPrimeDirection`.

Inspect `PrimitiveDirection.lean` before attempting this; do not guess the predicate shape and do not introduce a duplicate freshness notion.

This is optional. The required result of PRIM-L015 is the Direction/Depth dichotomy, not a new origin theory.

---

# Interpretation to preserve in docstrings

State clearly:

- the quotient support records **distinct old prime directions**, not exponents;
- dividing by one selected support prime preserves every other old direction exactly;
- the selected direction is the sole exceptional channel because one division may or may not exhaust its p-adic depth;
- `p^2 | n^2+r` is used only as the elementary one-step depth marker unless existing valuation APIs are explicitly reused;
- a composite large quotient inside the square Body must expose an old prime divisor, so non-primality decomposes into another direction or surviving self-depth;
- this checkpoint does not prove that any quotient is prime, does not prove an infinite descent, and does not prove Legendre.

The intended structural picture is:

```text
offset old-prime support S
       |
       | divide by chosen p ∈ S
       v
quotient old-prime support

all q ≠ p survive exactly
p survives iff an additional p-depth remains
```

---

# Non-goals

Do **not** add in PRIM-L015:

- a proof of `SquareAnchoredSupportEscape`;
- a proof of Legendre's conjecture;
- an infinite factor descent;
- a matching/Hall theorem argument;
- third-order inclusion-exclusion;
- asymptotic prime estimates;
- Mertens / PNT;
- quadratic-residue distribution;
- a new p-adic valuation framework;
- claims that every quotient is prime or primitive;
- RH / CFBRC dependencies;
- numerical enumeration as the generic proof method.

Do not confuse distinct prime-direction support with prime-power multiplicity.

---

# Verification

Run:

```sh
lake build DkMath.NumberTheory.Legendre
lake build DkMath.NumberTheory.Primitive
lake build DkMath
git diff --check
```

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

PRIM-L015 is complete when:

1. quotient old-nondivisor support is represented finitely;
2. quotient support is contained in the original offset support;
3. every prime direction distinct from the selected divisor is preserved iff-wise in the quotient;
4. erased support equality packages the off-diagonal preservation exactly;
5. quotient-support cardinality differs from offset-support cardinality by at most one;
6. selected-direction persistence is connected to `p^2` divisibility if cleanly available;
7. the quotient is shown to remain inside the certified square Body;
8. a composite quotient is shown to expose an old nondivisor prime support;
9. quotient non-primality is characterized by the Direction-or-Depth dichotomy;
10. no descent, contradiction, or Legendre proof is smuggled into the checkpoint;
11. requested builds and audits are clean.

Stop after PRIM-L015.

---

# Review questions after PRIM-L015

After this checkpoint, inspect whether the new quotient support law produces real leverage.

In particular compare:

```text
A. singleton support + depth one -> large prime quotient / fresh direction
B. multiple support -> quotient necessarily retains another old direction
C. singleton support + persistent self-depth -> pure same-direction obstruction
D. iterating the quotient transform would decrease arithmetic size but must not be started until a well-founded invariant is identified
E. whether existing PrimitiveBeam / Origin APIs can consume the fresh quotient case without inventing a new notion
```

Only after reviewing this surface decide whether the next route is:

```text
Primitive Direction bridge,
valuation-depth bridge,
well-founded quotient descent audit,
or abandonment of quotient iteration if it adds no new rigidity.
```
