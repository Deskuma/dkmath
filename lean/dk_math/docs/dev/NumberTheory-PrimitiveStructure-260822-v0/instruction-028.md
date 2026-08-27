# Codex Instruction — PRIM-L020 Packet Coprimality / Cross-Factor Separation

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-R001 has decomposed the Legendre application into dependency-ordered modules while preserving the public namespace and facade import.

The current packet branch is:

```text
Basic
  -> Wave
  -> PairOverlap
  -> CoprimePacket
  -> Quotient
  -> PacketCross
```

`PacketCross` currently proves, for canonical coprime packet representatives `r`, that an ordered old nondivisor prime pair `(p,q)` may cover the left/right seats

```text
n^2 + r
n^2 + (n + r)
```

and yields complementary factors `a,b > n` satisfying

```text
p * a = n^2 + r
q * b = n^2 + (n + r)
p * a + n = q * b.
```

It also proves product-period sparsity and the `p*q > n` one-packet bound.

The next structural fact is stronger than old-prime support disjointness:
for a coprime base representative, the two packet integers themselves are coprime.  Therefore **all** prime factors are separated across the packet, including factors larger than `n` and factors inside the complementary quotients.

This checkpoint should formalize that cross-factor separation.  It must not attempt a contradiction or a proof of Legendre's conjecture.

---

# Goal

Expose the packet-level arithmetic invariant

```text
Nat.Coprime (n^2 + r) (n^2 + (n + r))
```

for `Nat.Coprime n r`, and transport it through the PRIM-L019 factorization

```text
p * a = n^2 + r
q * b = n^2 + (n + r).
```

The intended factor rectangle is:

```text
left seat              right seat

p * a                   q * b

p  ----- coprime -----  q
p  ----- coprime -----  b
a  ----- coprime -----  q
a  ----- coprime -----  b

within the same side:
  p versus a : NOT classified here
  q versus b : NOT classified here
```

The unclassified same-side relations are exactly where selected-prime depth may persist.  Do not accidentally erase that distinction.

---

# Preferred module placement

Create a new module:

```text
DkMath/NumberTheory/Legendre/PacketCoprimality.lean
```

with

```lean
import DkMath.NumberTheory.Legendre.PacketCross
```

Keep the namespace:

```lean
namespace DkMath.NumberTheory.Legendre
```

Update `DkMath.NumberTheory.Legendre.Frontier` to import this new packet module instead of importing `PacketCross` directly, so the existing top-level facade continues to expose the new declarations through

```lean
import DkMath.NumberTheory.Legendre
```

Do not move or rename existing declarations.

As harmless cleanup, remove the duplicated `open DkMath.NumberTheory.Primitive` / `open DkMath.NumberTheory.StructuralArithmetic` / `open scoped BigOperators` block currently repeated in `Legendre/Basic.lean` if it is still present.

---

# Required implementation surface

Names below are preferred, not mandatory.  Report final declaration names.

## 1. Generic square-packet coprimality

First prove the arithmetic statement independently of prime support.

Preferred theorem shape:

```lean
theorem coprime_squarePacketPoints_of_coprime_offset
    {n r : ℕ}
    (hcop : Nat.Coprime n r) :
    Nat.Coprime (n ^ 2 + r) (n ^ 2 + (n + r))
```

A natural proof route is:

```text
B = A + n
A = n*n + r

gcd(A,B) = gcd(A,n) = gcd(r,n) = 1.
```

Use existing `Nat.Coprime` lemmas where practical; do not introduce a custom gcd theory.

Also expose the canonical packet specialization:

```lean
theorem coprime_squarePacketPoints_of_mem_base
    {n r : ℕ}
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n) :
    Nat.Coprime (n ^ 2 + r) (n ^ 2 + (n + r))
```

## 2. No prime can divide both packet points

Derive the all-prime version of packet support separation:

```lean
theorem not_prime_dvd_both_squarePacketPoints
    {n r ℓ : ℕ}
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n)
    (hℓ : Nat.Prime ℓ) :
    ¬ (ℓ ∣ n ^ 2 + r ∧ ℓ ∣ n ^ 2 + (n + r))
```

This is deliberately stronger than the existing theorem that only excludes one old anchor-nondivisor direction from supporting both seats.

Do not remove the older theorem; this checkpoint only adds the stronger packet invariant.

## 3. Exact quotient-to-quotient coprimality

For one actual ordered packet cross hit, prove the two complementary quotients are coprime.

Preferred form:

```lean
theorem coprime_packetCross_supportQuotients
    {n p q r : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    Nat.Coprime
      (squareOffsetSupportQuotient n p r)
      (squareOffsetSupportQuotient n q (n + r))
```

Use the exact factor reconstruction and packet-point coprimality.  The quotients divide the two coprime packet points, so no prime direction can occur in both quotient factors.

If useful, also expose the corresponding prime-divisor exclusion:

```lean
Nat.Prime ℓ ->
¬ (ℓ ∣ squareOffsetSupportQuotient n p r ∧
   ℓ ∣ squareOffsetSupportQuotient n q (n + r))
```

This is preferred if thin.

## 4. Cross-factor coprimality

For the same ordered hit, prove the factor rectangle separation.

At minimum expose:

```lean
Nat.Coprime p q
Nat.Coprime p (squareOffsetSupportQuotient n q (n + r))
Nat.Coprime (squareOffsetSupportQuotient n p r) q
Nat.Coprime
  (squareOffsetSupportQuotient n p r)
  (squareOffsetSupportQuotient n q (n + r))
```

The first relation also follows from distinct primality already stored in the ordered-pair membership, but providing a theorem/package is useful for downstream factor reasoning.

A preferred bundled theorem is:

```lean
theorem packetCross_factor_rectangle_coprime
    {n p q r : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    let a := squareOffsetSupportQuotient n p r
    let b := squareOffsetSupportQuotient n q (n + r)
    Nat.Coprime p q ∧
      Nat.Coprime p b ∧
      Nat.Coprime a q ∧
      Nat.Coprime a b
```

Equivalent association is fine.

Do **not** assert `Nat.Coprime p a` or `Nat.Coprime q b`.  Those same-side relations may fail exactly when selected-prime depth persists.

## 5. Product-factor coprimality

Expose directly that the two complete factor products are coprime:

```lean
theorem coprime_packetCross_factor_products
    {n p q r : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    let a := squareOffsetSupportQuotient n p r
    let b := squareOffsetSupportQuotient n q (n + r)
    Nat.Coprime (p * a) (q * b)
```

This theorem should be a thin rewrite of packet-point coprimality using the existing exact factor equations.

## 6. Strengthened factorization package

Build a downstream-friendly version of the PRIM-L019 factorization package.

Preferred theorem shape:

```lean
theorem squareAnchorPacketCrossOffsets_coprime_factorization
    {n p q r : ℕ}
    (hpq : (p, q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    ∃ a b,
      p * a = n ^ 2 + r ∧
      q * b = n ^ 2 + (n + r) ∧
      p * a + n = q * b ∧
      n < a ∧ n < b ∧
      Nat.Coprime n a ∧ Nat.Coprime n b ∧
      Nat.Coprime (p * a) (q * b) ∧
      Nat.Coprime p b ∧
      Nat.Coprime a q ∧
      Nat.Coprime a b
```

Reuse `squareAnchorPacketCrossOffsets_factorization`; do not duplicate its arithmetic proof.

## 7. Full-cover packet witness package

Under full cover, expose one such cross-separated factor rectangle for every canonical base representative.

Preferred shape:

```lean
theorem exists_coprime_factor_rectangle_of_fullyCovered
    {n r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n)
    (hfull : SquareOffsetsFullyCovered n) :
    ∃ p q a b,
      p ≠ q ∧
      p ∈ squareAnchorNondivisorPrimes n ∧
      q ∈ squareAnchorNondivisorPrimes n ∧
      p * a = n ^ 2 + r ∧
      q * b = n ^ 2 + (n + r) ∧
      p * a + n = q * b ∧
      n < a ∧ n < b ∧
      Nat.Coprime n a ∧ Nat.Coprime n b ∧
      Nat.Coprime (p * a) (q * b) ∧
      Nat.Coprime p b ∧ Nat.Coprime a q ∧ Nat.Coprime a b
```

It is acceptable to obtain `p,q` from the existing full-cover packet witness and then reuse the new cross-coprimality lemmas.

This remains a necessary structural package under full cover, not a contradiction.

---

# Interpretation to preserve in docstrings

State clearly:

- PRIM-L019 separated packet seats by **old nondivisor support directions**;
- PRIM-L020 upgrades this to coprimality of the **entire two packet integers**;
- therefore no prime factor, old or fresh, may occur on both sides;
- the complementary quotients are coprime across the packet;
- selected-prime depth remains a **same-side** phenomenon (`p` may still divide `a`, and `q` may still divide `b`);
- this gives a cross-factor separation rectangle, not a factorization uniqueness theorem;
- no primality of `a` or `b` is assumed;
- no infinite descent, matching, density estimate, contradiction, or Legendre proof is asserted.

This distinction is important:

```text
across packet sides: complete prime-factor separation
within one side: selected-prime depth may remain
```

---

# Non-goals

Do **not** add in PRIM-L020:

- a proof that either quotient is prime;
- a proof that every packet has a simple/fresh seat;
- a proof that same-side factors `p,a` or `q,b` are coprime;
- a contradiction from the factor rectangle;
- Hall/matching machinery;
- third-order overlap counting;
- analytic prime estimates;
- p-adic valuation sums;
- PrimitiveBeam/Zsigmondy first-occurrence claims;
- a proof of `SquareAnchoredSupportEscape` or Legendre's conjecture;
- RH / CFBRC dependencies.

---

# Refactor-preservation requirements

PRIM-R001 is now the module architecture baseline.

Therefore:

- put new packet mathematics in `PacketCoprimality.lean`, not back into the top-level `Legendre.lean`;
- keep `Legendre.lean` as the thin facade;
- keep declaration namespace `DkMath.NumberTheory.Legendre`;
- avoid introducing reverse dependencies from `Quotient`, `CoprimePacket`, or lower layers into the new module;
- `LocalizedObstruction` must remain independent of the packet branch;
- `Frontier` is the intended merge point.

---

# Verification

Run at least:

```sh
lake build DkMath.NumberTheory.Legendre.PacketCoprimality
lake build DkMath.NumberTheory.Legendre.Frontier
lake build DkMath.NumberTheory.Legendre
lake build DkMath.NumberTheory.Primitive
lake build DkMath
git diff --check
```

Confirm through the facade that representative new declarations are visible with:

```lean
import DkMath.NumberTheory.Legendre
#check DkMath.NumberTheory.Legendre.coprime_squarePacketPoints_of_coprime_offset
```

using the actual final name if adjusted.

Audit touched files for new occurrences of:

```text
sorry
admit
native_decide
axiom
```

Do not broaden scope to unrelated files.

---

# Acceptance criteria

PRIM-L020 is complete when:

1. packet-point coprimality is proved from `Nat.Coprime n r`;
2. canonical coprime packet representatives inherit that theorem;
3. no prime can divide both packet integers;
4. quotient factors from one packet cross hit are coprime;
5. the cross-factor rectangle (`p ⟂ q`, `p ⟂ b`, `a ⟂ q`, `a ⟂ b`) is exposed;
6. same-side depth relations are deliberately left unrestricted;
7. the existing PRIM-L019 factorization has a strengthened coprime package;
8. full cover yields the bounded cross-separated factor package for every base representative;
9. the new module is integrated through `Frontier` and the thin `Legendre` facade remains unchanged in role;
10. no Legendre proof, contradiction, matching, or analytic estimate is added.

After implementation, report the exact theorem names and whether the factor-rectangle API suggests a new structural obstruction beyond second-order counting.