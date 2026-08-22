# Codex Instruction — PRIM-041 Periodic Residue Observer

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-040 is complete.

The current canonical finite-world surface is:

```text
DkMath.NumberTheory.Primitive.FinitePrimeWorld
  primeScalesUpTo
  mem_primeScalesUpTo
  knownPrimeScales_primeScalesUpTo
  supportDisjointFrom_primeScalesUpTo_iff

DkMath.NumberTheory.Primitive.SquareBody
  squareBody
  prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody

DkMath.NumberTheory.Legendre
  SquareAnchoredSupportEscape
  squareAnchoredSupportEscape_iff_raw
  legendreConjecture_iff_squareAnchoredSupportEscape
```

`SquareAnchoredSupportEscape` remains unresolved and is not to be proved in this checkpoint.

User-reported verification of PRIM-040:

```text
lake build DkMath.NumberTheory.Primitive
lake build DkMath.NumberTheory.Legendre
lake build DkMath
git diff --check
```

No new `sorry`, `admit`, `native_decide`, or `axiom` were introduced in the touched Lean files.

Treat this as the accepted starting checkpoint.

---

# Review finding

The Primitive semantic layer now has a canonical finite prime world, but it does not yet expose the exact periodic observation that motivates PHZ.

For a finite set `S` of prime directions, let

```text
M(S) = product of all members of S.
```

Every prime `q ∈ S` divides `M(S)`. Therefore divisibility by old prime directions is unchanged under translation by any multiple of `M(S)`.

The desired semantic statement is:

```text
SupportDisjointFrom S (m + k * M(S))
  ↔ SupportDisjointFrom S m
```

This is the exact finite-wave periodicity layer. It says only that the old support pattern repeats. It does **not** say that a support-disjoint position is prime.

This checkpoint should formalize that observer cleanly and stop there.

---

# Goal

Create the reusable modulus/period layer for finite prime worlds.

Recommended new file:

```text
DkMath/NumberTheory/Primitive/PeriodicPrimeWorld.lean
```

Keep it under `DkMath.NumberTheory.Primitive`; do not put it in `Legendre`.

The dependency should be:

```text
PrimitiveDirection
    ↓
FinitePrimeWorld
    ↓
PeriodicPrimeWorld
    ↓
future PHZ concrete observers
```

---

# Required reconnaissance

Before defining anything, search DkMath and Mathlib for existing equivalents of:

```text
finite product modulus
Nat.Coprime with a finite product
coprimality under addition of a multiple
Nat.gcd / modulo periodicity
Finset.dvd_prod_of_mem
```

Reuse existing theorems where practical.

The current repository already uses the product-of-a-finite-set pattern in `DkMath.Hackathon.FinitePrimeEscape`, including `Finset.dvd_prod_of_mem`; do not duplicate an arithmetic lemma already supplied there merely under a new name unless the Primitive layer genuinely needs a dependency-clean version.

Do not import `DkMath.Hackathon` solely to obtain a trivial product-divisibility fact if Mathlib already supplies it directly.

---

# Required implementation surface

Names are preferred, not mandatory. If existing conventions imply better names, use them and report the final names.

## 1. Finite-world modulus

Define:

```lean
def primeWorldModulus (S : Finset ℕ) : ℕ :=
  ∏ p in S, p
```

This is an arithmetic modulus attached to an arbitrary finite support set.

Do **not** call it `primorial`: `S` need not be an initial prime segment.

For the canonical world, add the thin specialization if useful:

```lean
def primeModulusUpTo (P : ℕ) : ℕ :=
  primeWorldModulus (primeScalesUpTo P)
```

Avoid extra aliases if they do not improve theorem statements.

## 2. Member divides the modulus

Prove the elementary bridge:

```lean
theorem dvd_primeWorldModulus_of_mem
    {S : Finset ℕ} {q : ℕ}
    (hq : q ∈ S) :
    q ∣ primeWorldModulus S
```

This should be a thin wrapper over `Finset.dvd_prod_of_mem` or the current Mathlib equivalent.

## 3. Support periodicity under one full period

Prove:

```lean
theorem supportDisjointFrom_add_primeWorldModulus_iff
    {S : Finset ℕ} {m : ℕ} :
    SupportDisjointFrom S (m + primeWorldModulus S) ↔
      SupportDisjointFrom S m
```

Important: this theorem should not require `KnownPrimeScales S` unless Lean genuinely needs it. The definition only cares about prime members of `S`, and every member divides the product.

Use only divisibility arithmetic. Do not introduce density or primality conclusions.

## 4. Arbitrary period multiple

Prefer to expose the actual PHZ form:

```lean
theorem supportDisjointFrom_add_mul_primeWorldModulus_iff
    {S : Finset ℕ} {m k : ℕ} :
    SupportDisjointFrom S (m + k * primeWorldModulus S) ↔
      SupportDisjointFrom S m
```

An equivalent orientation such as

```lean
m + primeWorldModulus S * k
```

is acceptable if it fits existing arithmetic lemmas better.

Do not maintain duplicate public theorems for both multiplication orders unless one is a trivial simp corollary with clear value.

This theorem is the main checkpoint result because it formalizes coordinates of the form

```text
k * M + r
```

without specializing to `{2,3,5}`.

## 5. Coprime interpretation for certified prime worlds

If it can be proved cleanly from existing Mathlib APIs, prove:

```lean
theorem supportDisjointFrom_iff_coprime_primeWorldModulus
    {S : Finset ℕ} (hS : KnownPrimeScales S) {m : ℕ} :
    SupportDisjointFrom S m ↔ Nat.Coprime m (primeWorldModulus S)
```

An argument with the gcd/product in the opposite order is mathematically equivalent; choose one canonical orientation.

This theorem is important because it identifies an "unreserved seat" with a reduced residue modulo the finite-world modulus.

Do not force this theorem if the only available proof would cause a large import expansion or unrelated refactor. If blocked, report the exact missing Mathlib/DkMath lemma and still complete the direct support-periodicity theorems in sections 3–4.

## 6. Residue normal form

If section 5 is available, add a compact theorem showing that the observer depends only on the residue modulo its modulus, for certified prime worlds:

```lean
theorem supportDisjointFrom_mod_primeWorldModulus_iff
    {S : Finset ℕ} (hS : KnownPrimeScales S) {m : ℕ} :
    SupportDisjointFrom S (m % primeWorldModulus S) ↔
      SupportDisjointFrom S m
```

Handle the empty-world / modulus-one case correctly. Do not add artificial nonempty assumptions unless needed.

If direct modulo normalization becomes disproportionately expensive, stop with the arbitrary-multiple translation theorem and report it as the exact periodicity certificate.

---

# Canonical bounded-world wrappers

Add only thin corollaries for `primeScalesUpTo P` where they materially improve the public API.

Preferred central wrapper:

```lean
theorem supportDisjointFrom_primeScalesUpTo_add_period_iff
    {P m k : ℕ} :
    SupportDisjointFrom
      (primeScalesUpTo P)
      (m + k * primeWorldModulus (primeScalesUpTo P)) ↔
    SupportDisjointFrom (primeScalesUpTo P) m
```

If `primeModulusUpTo` is introduced, use it instead.

Do not involve `SquareCell`, `SquareOffset`, or `SquareAnchoredSupportEscape` in this file.

---

# Concrete `{2,3,5}` checkpoint

A small concrete certificate is allowed, but keep it minimal.

Preferred example if `norm_num` / `decide` handles it cleanly without `native_decide`:

```lean
example : primeWorldModulus ({2, 3, 5} : Finset ℕ) = 30 := by
  norm_num [primeWorldModulus]
```

or an equivalent named theorem if useful.

Do **not** yet formalize the full residue list

```text
{1,7,11,13,17,19,23,29}
```

in this checkpoint. That is a concrete PHZ observer certificate and can follow after the generic period theorem is stable.

---

# Public aggregation

Update:

```text
DkMath/NumberTheory/Primitive.lean
```

to import `PeriodicPrimeWorld` after `FinitePrimeWorld` and before application-specific modules.

Do not change `Legendre.lean` unless a tiny import cleanup is genuinely necessary.

---

# Mathematical interpretation to preserve

The theorem being formalized is:

```text
old prime support pattern
    is invariant under
translation by the finite-world product modulus
```

For the concrete base `{2,3,5}`:

```text
M = 2 * 3 * 5 = 30
```

so support-disjointness is constant along each coordinate family

```text
30*k + r.
```

This is a **candidate-seat periodicity theorem**, not a prime-periodicity theorem.

Never state or imply:

```text
SupportDisjointFrom S m → Nat.Prime m
```

without the separate square-Body bound or another valid closure theorem.

---

# Explicit non-goals

Do not implement:

```text
proof of SquareAnchoredSupportEscape
proof of LegendreConjecture
full `{1,7,11,13,17,19,23,29}` residue enumeration
mirror / subtraction symmetry around k*M
CRT child-seat update after adding q
PRIM-042 observer refinement
prime counts or density
PNT / Mertens / analytic estimates
von Mangoldt weights
RH / CFBRC imports
category-theory abstractions
```

The mirror theorem

```text
k*M-r ↔ k*M+r
```

is mathematically relevant but should be a later small checkpoint after the translation-period API is stable; avoid mixing Nat subtraction edge conditions into PRIM-041.

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
3. definition chosen for the finite-world modulus;
4. exact theorem proving arbitrary-multiple periodicity of `SupportDisjointFrom`;
5. whether the `Nat.Coprime` characterization was completed;
6. whether residue normalization modulo the finite-world modulus was completed;
7. any concrete `30` certificate added;
8. build results;
9. confirmation that no Legendre provider, PHZ residue enumeration, or CRT refinement was introduced.

Stop after PRIM-041. The next review will choose between:

```text
PRIM-041B  mirror symmetry / centered observer
PRIM-041C  concrete {2,3,5} residue certificate
PRIM-042   observer update by adding a new prime direction
```
