# Codex Instruction — PRIM-041B Centered / Mirror Observer

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-041 is complete.

The current periodic finite-world surface is:

```text
DkMath.NumberTheory.Primitive.PeriodicPrimeWorld
  primeWorldModulus
  dvd_primeWorldModulus_of_mem
  supportDisjointFrom_add_primeWorldModulus_iff
  supportDisjointFrom_add_mul_primeWorldModulus_iff
  supportDisjointFrom_iff_coprime_primeWorldModulus
  supportDisjointFrom_mod_primeWorldModulus_iff
  supportDisjointFrom_primeScalesUpTo_add_period_iff
```

The main certified periodicity theorem is:

```text
SupportDisjointFrom S (m + k * primeWorldModulus S)
  ↔ SupportDisjointFrom S m
```

for arbitrary finite `S`.

For `KnownPrimeScales S`, support disjointness is also equivalent to coprimality with the finite-world modulus.

User-reported verification of PRIM-041:

```text
lake build DkMath.NumberTheory.Primitive
lake build DkMath.NumberTheory.Legendre
lake build DkMath
git diff --check
```

No new `sorry`, `admit`, `native_decide`, or `axiom` were introduced in touched Lean files.

Legendre's unresolved `SquareAnchoredSupportEscape` remains unproved and must remain so in this checkpoint.

---

# Review finding

PRIM-041 gives the right-translation observer:

```text
r  ↦  r + k*M
```

where

```text
M = primeWorldModulus S.
```

The next structural fact is the centered reflection around a multiple of the same modulus.

For `r ≤ k*M`, divisibility by every `q ∈ S` sees

```text
k*M - r
```

and

```text
k*M + r
```

as the same support state, because `q ∣ k*M`.

The target geometric picture is:

```text
             k*M
              |
      k*M-r   |   k*M+r
          \    |    /
           same finite-world support state
```

This is a generic mirror theorem for the finite support observer. It is not yet the concrete half-period symmetry of the `{2,3,5}` residue list and is not a Legendre theorem.

---

# Goal

Extend the periodic finite-world API with subtraction-side normalization and centered mirror symmetry.

Preferred location:

```text
DkMath/NumberTheory/Primitive/PeriodicPrimeWorld.lean
```

If the file becomes materially clearer by moving mirror theorems to a small sibling module such as

```text
DkMath/NumberTheory/Primitive/CenteredPrimeWorld.lean
```

that is acceptable, but avoid unnecessary module fragmentation for only a few theorems.

Do not add application imports.

---

# Required reconnaissance

Before proving the subtraction statements, check Mathlib for the current canonical forms of:

```text
Nat.dvd_sub'
Nat.dvd_sub
Nat.sub_add_cancel
Nat.sub_add_cancel_of_le
Nat.add_sub_cancel_left/right
Nat.dvd_add_iff_left/right
```

Use existing divisibility/subtraction lemmas rather than rebuilding natural-number arithmetic manually where possible.

Pay attention to truncated subtraction. The bound

```text
r ≤ k * primeWorldModulus S
```

is part of the mathematical statement, not proof noise.

---

# Required implementation surface

Names are preferred, not mandatory. Report final declaration names.

## 1. Left-side centered normalization

Let

```text
M := primeWorldModulus S.
```

Prove conceptually:

```lean
theorem supportDisjointFrom_mul_primeWorldModulus_sub_iff
    {S : Finset ℕ} {k r : ℕ}
    (hr : r ≤ k * primeWorldModulus S) :
    SupportDisjointFrom S (k * primeWorldModulus S - r) ↔
      SupportDisjointFrom S r
```

This is the subtraction counterpart of the existing translation theorem.

The proof should be purely divisibility-theoretic:

```text
q ∈ S
  → q ∣ M
  → q ∣ k*M
  → q ∣ (k*M-r) iff q ∣ r, under r ≤ k*M.
```

Do not introduce `KnownPrimeScales S` unless Lean genuinely requires it; the support predicate itself only tests prime elements that belong to `S`.

## 2. Right-side centered normalization

Expose a clean theorem for the symmetric positive side if the existing PRIM-041 theorem does not already rewrite conveniently:

```lean
theorem supportDisjointFrom_mul_primeWorldModulus_add_iff
    {S : Finset ℕ} {k r : ℕ} :
    SupportDisjointFrom S (k * primeWorldModulus S + r) ↔
      SupportDisjointFrom S r
```

Prefer proving this as a thin corollary of

```text
supportDisjointFrom_add_mul_primeWorldModulus_iff
```

using commutativity. Do not duplicate the divisibility proof.

If the theorem would only be an aesthetic alias with no downstream value, it may be omitted and the mirror theorem may use the existing periodicity theorem directly.

## 3. Generic centered mirror theorem

This is the main checkpoint result.

Prove:

```lean
theorem supportDisjointFrom_centered_mirror_iff
    {S : Finset ℕ} {k r : ℕ}
    (hr : r ≤ k * primeWorldModulus S) :
    SupportDisjointFrom S (k * primeWorldModulus S - r) ↔
      SupportDisjointFrom S (k * primeWorldModulus S + r)
```

The proof should compose the two normalizations through `r`.

Do not prove this by unfolding `SupportDisjointFrom` twice if the left/right normalization theorems are available. The public structure should visibly be:

```text
left centered point
   ↔ residue r
   ↔ right centered point
```

## 4. Modulus-one / empty-world behavior

Do not add nonempty assumptions merely to avoid edge cases.

For `S = ∅`,

```text
primeWorldModulus ∅ = 1
```

and `SupportDisjointFrom ∅ m` is vacuous, so the mirror theorem should remain valid whenever the natural subtraction bound is satisfied.

No separate theorem is required unless a small simp lemma materially improves the proof.

## 5. Canonical bounded-world wrapper

Add a thin specialization for the canonical finite world only if useful:

```lean
theorem supportDisjointFrom_primeScalesUpTo_centered_mirror_iff
    {P k r : ℕ}
    (hr : r ≤ k * primeWorldModulus (primeScalesUpTo P)) :
    SupportDisjointFrom
      (primeScalesUpTo P)
      (k * primeWorldModulus (primeScalesUpTo P) - r) ↔
    SupportDisjointFrom
      (primeScalesUpTo P)
      (k * primeWorldModulus (primeScalesUpTo P) + r)
```

Keep this a wrapper only. The generic theorem is the real result.

---

# Optional residue-negation corollary

If it is inexpensive and avoids Nat subtraction complications later, one optional theorem may express the same idea at one modulus period:

```text
M-r and r have the same support state when r ≤ M.
```

Conceptually:

```lean
theorem supportDisjointFrom_primeWorldModulus_sub_iff
    {S : Finset ℕ} {r : ℕ}
    (hr : r ≤ primeWorldModulus S) :
    SupportDisjointFrom S (primeWorldModulus S - r) ↔
      SupportDisjointFrom S r
```

This should be a specialization of the `k = 1` theorem, not a second proof.

Do not add a large family of redundant `k=1`, `k=2`, swapped-addition aliases.

---

# Mathematical interpretation to preserve

The new theorem is not about primality symmetry.

It certifies only:

```text
finite old-prime support state is reflection-invariant
around multiples of the finite-world modulus.
```

For a certified prime world, PRIM-041 already gives the equivalent coprime reading:

```text
Nat.Coprime (k*M-r) M
  ↔ Nat.Coprime r M
  ↔ Nat.Coprime (k*M+r) M.
```

You may use this internally if it shortens the proof, but the public checkpoint theorem should remain phrased in `SupportDisjointFrom`, because that is the Primitive observer vocabulary.

---

# Explicit non-goals

Do not implement:

```text
proof of SquareAnchoredSupportEscape
proof of LegendreConjecture
concrete modulus theorem `{2,3,5} -> 30`
full residue enumeration `{1,7,11,13,17,19,23,29}`
half-period center `15` pairing for modulus 30
CRT
observer update `S -> insert q S`
PRIM-042 child-seat refinement
prime counts or density
PNT / Mertens
von Mangoldt mass
RH / CFBRC
category theory
```

In particular, do not state that mirrored support-disjoint positions are both prime. They are only equivalent candidate seats unless a separate square-Body or other arithmetic closure applies.

---

# Public aggregation

If a new sibling module is created, update:

```text
DkMath/NumberTheory/Primitive.lean
```

in dependency order.

If the implementation stays in `PeriodicPrimeWorld.lean`, no aggregator change is needed beyond docstring cleanup if desired.

Do not modify `Legendre.lean` in this checkpoint.

---

# Verification

Run at least:

```sh
lake build DkMath.NumberTheory.Primitive
lake build DkMath.NumberTheory.Legendre
lake build DkMath
git diff --check
```

Check touched Lean files for newly introduced:

```text
sorry
admit
native_decide
axiom
```

Ignore unrelated pre-existing warnings.

---

# Report back

Report:

1. files changed;
2. final declaration names;
3. exact left-subtraction normalization theorem;
4. exact generic centered mirror theorem;
5. whether a right-addition normalization wrapper was added or existing periodicity was used directly;
6. whether a canonical `primeScalesUpTo` mirror wrapper was added;
7. build results;
8. confirmation that no concrete PHZ residue list, CRT update, or Legendre provider was introduced.

Stop after PRIM-041B.

The next review will choose between:

```text
PRIM-041C  concrete `{2,3,5}` / modulus-30 residue certificate
PRIM-042   finite-world update by adding a new prime direction
```
