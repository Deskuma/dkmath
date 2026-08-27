# Codex Instruction — PRIM-L021 Packet Determinant / Reduced-Residue Rectangle

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-R001 has decomposed the Legendre application into dependency-ordered modules, with `DkMath.NumberTheory.Legendre` remaining a thin facade.

PRIM-L019 provides ordered packet cross incidences. For a canonical base representative `r`, an ordered pair `(p,q)` supporting the two packet seats gives complementary factors `a,b` with

```text
p * a = n^2 + r
q * b = n^2 + (n + r)
p * a + n = q * b
n < a
n < b
```

PRIM-L020 strengthens this to complete cross-side coprimality. For a canonical coprime packet, the two full points are coprime, and a cross factor rectangle satisfies

```text
Coprime (p*a) (q*b)
Coprime p q
Coprime p b
Coprime a q
Coprime a b
```

while the same-side relations

```text
Coprime p a
Coprime q b
```

remain intentionally unclassified because selected-prime depth may persist.

The purpose of PRIM-L021 is to expose the same packet rectangle in the natural modulus-`n` reduced-residue coordinate. The packet relation is not only a factorization relation: it is an exact determinant relation

```text
q*b - p*a = n
```

and therefore a rank-one congruence modulo the anchor

```text
p*a ≡ q*b ≡ r  [MOD n].
```

This checkpoint should make that finite unit-residue geometry explicit without attempting a contradiction, a matching theorem, or a proof of Legendre's conjecture.

---

# Preferred location

Add a new module:

```text
DkMath/NumberTheory/Legendre/PacketUnitResidue.lean
```

Import:

```lean
import DkMath.NumberTheory.Legendre.PacketCoprimality
```

Then update:

```text
DkMath/NumberTheory/Legendre/Frontier.lean
```

so that `Frontier` imports `PacketUnitResidue` instead of importing `PacketCoprimality` directly.

Do not add new mathematics to the thin facade `DkMath.NumberTheory.Legendre`.

---

# Goal

A canonical packet representative `r` is one reduced residue modulo `n`. Under a packet cross factorization,

```text
p*a = n^2 + r
q*b = n^2 + n + r,
```

so both products represent the same residue class `r` modulo `n`, while their exact difference is one anchor length `n`.

Formalize this as a small API for:

1. canonical base remainder geometry;
2. product-to-base congruence;
3. determinant/difference `n`;
4. all four factors being units relative to `n` in the elementary `Nat.Coprime` sense;
5. a strengthened full-cover factor rectangle carrying the reduced-residue coordinate.

Use `Nat.ModEq` / `%` arithmetic. Do not introduce `ZMod`, quotient groups, or abstract unit-group machinery in this checkpoint unless a tiny local theorem becomes substantially simpler and does not enlarge dependencies.

---

# Required implementation surface

Names below are preferred, not mandatory. Report final declaration names.

## 1. Canonical base is a genuine residue for `1 < n`

For canonical base representatives, expose the strict bound needed to identify `r` with its own residue modulo `n`.

Preferred theorem:

```lean
theorem squareAnchorCoprimeBaseOffsets_lt_anchor
    {n r : ℕ}
    (hn : 1 < n)
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n) :
    r < n
```

Reason: membership gives `r ≤ n` and `Coprime n r`; equality `r = n` would force `n = 1`.

Then, if useful:

```lean
@[simp] theorem mod_anchor_eq_self_of_mem_coprimeBase
    {n r : ℕ}
    (hn : 1 < n)
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n) :
    r % n = r
```

Do not special-case `n = 1` globally. Keep the generic congruence API valid for positive `n`; use `1 < n` only when replacing `r % n` by `r`.

## 2. Both packet points have the same anchor residue

Prove generic congruence/remainder statements for the two complete packet points.

Preferred forms:

```lean
theorem squarePacket_left_modEq_base
    (n r : ℕ) :
    n ^ 2 + r ≡ r [MOD n]


theorem squarePacket_right_modEq_base
    (n r : ℕ) :
    n ^ 2 + (n + r) ≡ r [MOD n]
```

Equivalent `%` equalities are acceptable.

For `1 < n` and canonical `r`, preferably also expose exact remainders:

```lean
(n ^ 2 + r) % n = r
(n ^ 2 + (n + r)) % n = r
```

These are deterministic residue identities, not equidistribution statements.

## 3. Single-incidence quotient product residue

For an existing support incidence, expose that the reconstructed product has the offset residue modulo the anchor.

Useful shape:

```lean
theorem squareOffsetSupportQuotient_mul_modEq_offset
    {n p r : ℕ}
    (hdiv : p ∣ n ^ 2 + r) :
    p * squareOffsetSupportQuotient n p r ≡ r [MOD n]
```

This should be a thin combination of

```text
p * quotient = n^2 + r
```

and the generic packet/anchor residue identity.

No coprimality hypothesis is needed for this congruence itself.

## 4. Packet cross products have the same reduced residue

For a packet cross hit, prove both product coordinates represent the same base residue.

Preferred theorem:

```lean
theorem packetCross_factor_products_modEq_base
    {n p q r : ℕ}
    (hpq : (p,q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    p * squareOffsetSupportQuotient n p r ≡ r [MOD n] ∧
    q * squareOffsetSupportQuotient n q (n + r) ≡ r [MOD n]
```

Then derive the direct rank-one relation:

```lean
theorem packetCross_factor_products_modEq
    ... :
    p * squareOffsetSupportQuotient n p r ≡
      q * squareOffsetSupportQuotient n q (n + r) [MOD n]
```

This is the finite residue form of the packet determinant equation.

## 5. Exact determinant / one-anchor separation

Expose the exact arithmetic difference already implicit in PRIM-L019/L020.

Preferred equality without truncated subtraction:

```lean
theorem packetCross_factor_determinant_eq_anchor
    {n p q r : ℕ}
    (hpq : (p,q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    p * squareOffsetSupportQuotient n p r + n =
      q * squareOffsetSupportQuotient n q (n + r)
```

If cheap, also provide:

```lean
q * squareOffsetSupportQuotient n q (n+r) -
  p * squareOffsetSupportQuotient n p r = n
```

but do not make the subtraction form the primary API.

Interpret this as a determinant-like rectangle relation only in documentation; do not import matrix libraries in this checkpoint.

## 6. All four factors are anchor units in the elementary sense

From packet membership and PRIM-L020, expose that each factor is coprime to the anchor:

```lean
theorem packetCross_all_factors_coprime_anchor
    {n p q r : ℕ}
    (hpq : (p,q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    Nat.Coprime n p ∧
    Nat.Coprime n q ∧
    Nat.Coprime n (squareOffsetSupportQuotient n p r) ∧
    Nat.Coprime n (squareOffsetSupportQuotient n q (n+r))
```

Reuse:

- nondivisor-prime membership for `p,q`;
- existing quotient coprimality transfer for `a,b`.

Do not call these values `Units` in theorem names unless an actual `Units`/`ZMod` object is constructed. In prose, "unit residue" means only invertible residue class as certified by `Nat.Coprime`.

## 7. Reduced-residue rectangle package

Provide one theorem packaging the packet cross hit as a reduced-residue factor rectangle.

A preferred shape is:

```lean
theorem squareAnchorPacketCrossOffsets_unitResidue_factorization
    {n p q r : ℕ}
    (hpq : (p,q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hr : r ∈ squareAnchorPacketCrossOffsets n p q) :
    ∃ a b,
      p * a = n ^ 2 + r ∧
      q * b = n ^ 2 + (n + r) ∧
      p * a + n = q * b ∧
      n < a ∧ n < b ∧
      Nat.Coprime n p ∧ Nat.Coprime n q ∧
      Nat.Coprime n a ∧ Nat.Coprime n b ∧
      Nat.Coprime p b ∧ Nat.Coprime a q ∧ Nat.Coprime a b ∧
      p * a ≡ r [MOD n] ∧
      q * b ≡ r [MOD n]
```

It is acceptable to reuse the PRIM-L020 factorization and append the residue facts rather than re-prove the rectangle.

Do not add `Coprime p a` or `Coprime q b`.

## 8. Full-cover reduced-residue rectangle

Under full cover, every canonical base representative should receive such a rectangle.

Preferred target:

```lean
theorem exists_unitResidue_factor_rectangle_of_fullyCovered
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
      Nat.Coprime n p ∧ Nat.Coprime n q ∧
      Nat.Coprime n a ∧ Nat.Coprime n b ∧
      Nat.Coprime p b ∧ Nat.Coprime a q ∧ Nat.Coprime a b ∧
      p * a ≡ r [MOD n] ∧
      q * b ≡ r [MOD n]
```

Equivalent association/order is acceptable.

If `1 < n`, a stronger convenience theorem may replace the final congruences by exact remainder equations

```text
(p*a) % n = r
(q*b) % n = r.
```

This stronger exact-remainder wrapper is optional.

## 9. Optional cancellation reconnaissance — only if cheap

Inspect Mathlib's `Nat.ModEq` API for cancellation by a factor coprime to the modulus.

If a direct existing lemma makes this trivial, expose one or two consequences such as:

```text
p*a ≡ q*b [MOD n]
Coprime n p
```

implying an equivalent relation after cancelling `p` via a modular inverse/cancellation theorem.

However:

- do not hand-build extended Euclid machinery;
- do not introduce a new modular inverse definition;
- do not move into `ZMod` merely to satisfy this optional item;
- report the relevant Mathlib lemma if found, even if no wrapper is added.

The checkpoint is complete without cancellation.

---

# Interpretation to preserve in docstrings

State clearly:

- canonical packet representatives are reduced residues modulo the anchor;
- the two packet points are one anchor apart and therefore share the same residue modulo `n`;
- the factor rectangle gives two factorizations of the same reduced residue;
- `p,q,a,b` are each coprime to the anchor, so each represents an invertible residue class in the elementary sense;
- the exact equation `p*a + n = q*b` is the determinant-like lift of the modular equality;
- cross-side factors are coprime by PRIM-L020;
- same-side depth remains intentionally unresolved;
- no distribution, matching, uniqueness, primitive-origin, descent, contradiction, or Legendre proof is asserted.

---

# Non-goals

Do **not** add in PRIM-L021:

- a proof of `SquareAnchoredSupportEscape`;
- a proof of Legendre's conjecture;
- a proof that a simple/fresh seat exists;
- a Hall/matching theorem;
- third-order incidence counting;
- analytic estimates for `φ(n)` or primes;
- `ZMod` group theory unless needed for a tiny optional wrapper;
- a new modular inverse implementation;
- PrimitiveBeam/Zsigmondy origin claims;
- infinite descent;
- RH / CFBRC dependencies;
- numerical enumeration as a generic proof method.

---

# Verification

Run:

```sh
lake build DkMath.NumberTheory.Legendre.PacketUnitResidue
lake build DkMath.NumberTheory.Legendre.Frontier
lake build DkMath.NumberTheory.Legendre
lake build DkMath.NumberTheory.Primitive
lake build DkMath
git diff --check
```

Check the new public declarations through the facade import:

```lean
import DkMath.NumberTheory.Legendre
```

Audit touched files for new occurrences of:

```text
sorry
admit
native_decide
axiom
```

---

# Acceptance criteria

PRIM-L021 is complete when:

1. packet points are explicitly shown to represent the same base residue modulo `n`;
2. packet cross factor products are congruent to the canonical base residue;
3. the exact one-anchor determinant equation is exposed as public API;
4. all four factors are proved coprime to the anchor;
5. a packet cross hit is packaged as a reduced-residue factor rectangle;
6. full cover gives such a rectangle for every canonical base representative;
7. `Frontier` imports the new module and the thin facade continues to expose all prior declarations;
8. same-side depth remains intentionally unclassified;
9. no new Legendre proof or contradiction is asserted.
