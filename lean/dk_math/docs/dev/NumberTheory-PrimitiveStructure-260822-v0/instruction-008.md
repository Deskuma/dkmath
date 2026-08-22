# Codex Instruction — PRIM-045 Canonical Prime-World Residue Space / Exact Refinement

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-044 is complete.

The current generic refinement surface includes:

```text
primeWorldChild
primeWorldChild_eq_iff_of_lt_modulus
survivingChildIndices
card_survivingChildIndices
survivingChildPairs
card_survivingChildPairs
refinedSurvivingSeats
card_refinedSurvivingSeats
supportDisjointFrom_of_mem_refinedSurvivingSeats
```

For a certified old world `S`, a fresh prime `q`, and a finite set `R` of canonical old representatives, we have:

```text
(refinedSurvivingSeats S q R).card = R.card * (q - 1)
```

provided every `r ∈ R` satisfies `r < primeWorldModulus S`.

PRIM-044 also established the concrete construction

```text
phzResidues210 := refinedSurvivingSeats primeWorld235 7 phzResidues30
```

with

```text
phzResidues210.card = 48
```

and every member of `phzResidues210` is support-disjoint from
`insert 7 primeWorld235`.

What is still missing is **exactness**: we have constructed 48 valid seats, but have not yet proved that they are exactly all support-disjoint representatives in the full period `0 ≤ n < 210`.

User-reported verification of PRIM-044:

```text
lake build DkMath.NumberTheory.Primitive.PrimeWorldRefinement
lake build DkMath.NumberTheory.Primitive.PHZ30
lake build DkMath.NumberTheory.Primitive
lake build DkMath.NumberTheory.Legendre
lake build DkMath
git diff --check
```

No new `sorry`, `admit`, `native_decide`, or `axiom` were introduced.

---

# Goal

Introduce a canonical finite residue-space object for a finite prime world and prove that one fresh-prime refinement produces **exactly** the canonical residue space of the enlarged world.

The main target is the generic equality

```text
refinedSurvivingSeats S q (primeWorldResidues S)
  = primeWorldResidues (insert q S)
```

under

```text
KnownPrimeScales S
Nat.Prime q
q ∉ S.
```

This checkpoint should convert PRIM-044 from a constructive lower-side result (“these refined seats survive”) into an exact finite-world decomposition (“these are all surviving seats in the enlarged period”).

Do not use Euler's totient function to prove the result. The equality must come from the refinement coordinates already built in PRIM-042–044.

---

# Preferred module structure

Create a generic sibling module:

```text
DkMath/NumberTheory/Primitive/PrimeWorldResidues.lean
```

Preferred dependency:

```text
PeriodicPrimeWorld
        ↓
PrimeWorldRefinement
        ↓
PrimeWorldResidues
        ↓
PHZ30
```

Update:

```text
DkMath/NumberTheory/Primitive.lean
```

to publicly import the new module.

`PHZ30.lean` may import `PrimeWorldResidues` instead of importing `PrimeWorldRefinement` directly if that makes the dependency clearer.

Avoid moving existing declarations unless necessary.

---

# Required reconnaissance

Before proving the reverse inclusion, inspect Mathlib's current APIs around Euclidean decomposition and quotient bounds, especially:

```text
Nat.mod_add_div
Nat.mod_lt
Nat.div_lt_iff_lt_mul
Nat.div_lt_of_lt_mul
Nat.add_mul_div_left
Nat.add_mul_mod_self_left
```

Use the current canonical lemmas available in this repository's Mathlib version. Do not rebuild quotient/remainder arithmetic manually if a standard lemma is available.

---

# Required implementation surface

Names below are preferred, not mandatory. Report final declaration names.

## 1. Canonical finite prime-world residue set

Define a computable finite canonical residue space.

Preferred definition:

```lean
def primeWorldResidues (S : Finset ℕ) : Finset ℕ :=
  (Finset.range (primeWorldModulus S)).filter
    (fun n => Nat.Coprime n (primeWorldModulus S))
```

This is intentionally a reduced-residue definition using the existing world modulus. For a `KnownPrimeScales` world, existing PRIM-041 results identify it exactly with `SupportDisjointFrom`.

Do not define this using a noncomputable infinite quantified predicate if the coprime formulation gives the same certified-world semantics more cleanly.

Add the basic membership theorem:

```lean
@[simp] theorem mem_primeWorldResidues
    {S : Finset ℕ} {n : ℕ} :
    n ∈ primeWorldResidues S ↔
      n < primeWorldModulus S ∧
      Nat.Coprime n (primeWorldModulus S)
```

Then expose the semantic form for certified prime worlds:

```lean
theorem mem_primeWorldResidues_iff_supportDisjointFrom
    {S : Finset ℕ} (hS : KnownPrimeScales S) {n : ℕ} :
    n ∈ primeWorldResidues S ↔
      n < primeWorldModulus S ∧
      SupportDisjointFrom S n
```

Reuse:

```text
supportDisjointFrom_iff_coprime_primeWorldModulus
```

Do not reprove the coprime/support equivalence.

Useful thin corollaries are encouraged if they simplify later proofs:

```text
n ∈ primeWorldResidues S → n < primeWorldModulus S
n ∈ primeWorldResidues S → SupportDisjointFrom S n
```

under the appropriate certified-world hypothesis.

### Empty-world behavior

Do not add a nonempty assumption. For `S = ∅`, the modulus is `1`; the canonical residue space should behave naturally. No special theorem is required unless useful.

---

## 2. Canonical child-coordinate existence below the enlarged period

PRIM-044 proved uniqueness of child coordinates for canonical parents. We now also need existence.

For

```text
M = primeWorldModulus S
```

and `n < q * M`, expose a theorem conceptually equivalent to:

```lean
theorem exists_primeWorldChild_coordinates_of_lt_mul_modulus
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q n : ℕ}
    (hn : n < q * primeWorldModulus S) :
    ∃ r j,
      r < primeWorldModulus S ∧
      j < q ∧
      n = primeWorldChild S r j
```

The intended canonical coordinates are:

```text
r = n % M
j = n / M.
```

Use Euclidean division. This theorem is arithmetic infrastructure, not CRT.

If a more useful statement also includes uniqueness, it may reuse:

```text
primeWorldChild_eq_iff_of_lt_modulus
```

but do not duplicate that proof.

Do not require `Nat.Prime q` for this arithmetic decomposition unless genuinely needed. `KnownPrimeScales S` may be used only to obtain `0 < M`.

---

## 3. Bound every refined seat by the enlarged period

Prove a generic bound for constructed refined seats.

Conceptually:

```lean
theorem lt_insert_modulus_of_mem_refinedSurvivingSeats
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q : ℕ} {R : Finset ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hR : ∀ r ∈ R, r < primeWorldModulus S)
    {n : ℕ}
    (hn : n ∈ refinedSurvivingSeats S q R) :
    n < primeWorldModulus (insert q S)
```

The proof should use:

```text
r < M
j < q
n = r + j*M
primeWorldModulus_insert
```

not a global search over the new period.

This theorem plus the existing

```text
supportDisjointFrom_of_mem_refinedSurvivingSeats
```

provides the forward inclusion needed by exact refinement.

---

## 4. Exact membership theorem for canonical refinement

This is the main semantic theorem before Finset equality.

Prove:

```lean
theorem mem_refined_primeWorldResidues_iff
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q n : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S) :
    n ∈ refinedSurvivingSeats S q (primeWorldResidues S) ↔
      n < primeWorldModulus (insert q S) ∧
      SupportDisjointFrom (insert q S) n
```

### Forward direction

Reuse:

```text
lt_insert_modulus_of_mem_refinedSurvivingSeats
supportDisjointFrom_of_mem_refinedSurvivingSeats
```

and the semantic membership theorem for the old `primeWorldResidues S`.

### Reverse direction

This is the key new proof.

Given

```text
n < primeWorldModulus (insert q S)
SupportDisjointFrom (insert q S) n
```

rewrite the new modulus using freshness:

```text
primeWorldModulus (insert q S) = q * primeWorldModulus S.
```

Use the canonical Euclidean coordinates:

```text
r = n % M
j = n / M
```

with

```text
r < M
j < q
n = r + j*M.
```

From enlarged support disjointness, recover:

```text
SupportDisjointFrom S n
¬ q ∣ n
```

using

```text
supportDisjointFrom_insert_prime_iff.
```

Then use old periodicity / child normalization to obtain:

```text
SupportDisjointFrom S r.
```

Therefore:

```text
r ∈ primeWorldResidues S
```

and the child index `j` is surviving because `q ∤ n`.

Conclude that `n` belongs to the image `refinedSurvivingSeats`.

Do not use a cardinality-equality argument to obtain reverse inclusion. The point of this checkpoint is an explicit canonical coordinate inverse.

---

## 5. Exact refinement equality

Package the previous theorem as the main checkpoint theorem:

```lean
theorem refinedSurvivingSeats_primeWorldResidues_eq
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S) :
    refinedSurvivingSeats S q (primeWorldResidues S) =
      primeWorldResidues (insert q S)
```

The proof should be a thin `Finset.ext` using:

```text
mem_refined_primeWorldResidues_iff
mem_primeWorldResidues_iff_supportDisjointFrom
knownPrimeScales_insert
```

The exact Finset equality is the real PRIM-045 result.

---

## 6. Cardinality recurrence as a corollary

Now derive, without Euler phi:

```lean
theorem card_primeWorldResidues_insert
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S) :
    (primeWorldResidues (insert q S)).card =
      (primeWorldResidues S).card * (q - 1)
```

This should be a short corollary of:

```text
refinedSurvivingSeats_primeWorldResidues_eq
card_refinedSurvivingSeats
```

with the old residue-bound condition discharged from `mem_primeWorldResidues`.

Do not prove a product-over-all-primes formula yet. That belongs to the next checkpoint.

---

# Concrete PHZ30 / PHZ210 closure

Update `PHZ30.lean` only after the generic exact refinement is complete.

## 7. Identify PHZ30 with the canonical residue world

Prove:

```lean
theorem phzResidues30_eq_primeWorldResidues :
    phzResidues30 = primeWorldResidues primeWorld235
```

Use the existing complete PHZ30 classification. Do not enumerate anything new.

## 8. Identify PHZ210 exactly

Using

```text
phzResidues210 := refinedSurvivingSeats primeWorld235 7 phzResidues30
```

prove:

```lean
theorem phzResidues210_eq_primeWorldResidues_insert_seven :
    phzResidues210 = primeWorldResidues (insert 7 primeWorld235)
```

This must be derived from generic exact refinement plus the PHZ30 identification, not by checking `0..209` individually.

## 9. Complete PHZ210 one-period classification

Expose the exact finite-period statement:

```lean
theorem mem_phzResidues210_iff
    {n : ℕ} :
    n ∈ phzResidues210 ↔
      n < 210 ∧
      SupportDisjointFrom (insert 7 primeWorld235) n
```

Use:

```text
primeWorldModulus_insert_seven_primeWorld235
phzResidues210_eq_primeWorldResidues_insert_seven
mem_primeWorldResidues_iff_supportDisjointFrom
```

Optionally, if it stays thin, add the global periodic classification:

```text
SupportDisjointFrom (insert 7 primeWorld235) m
  ↔ m % 210 ∈ phzResidues210
```

This is useful but secondary to the one-period exactness theorem.

The existing theorem

```text
card_phzResidues210 : phzResidues210.card = 48
```

should remain derived structurally; do not replace it by an interval enumeration.

---

# Mathematical interpretation to preserve

After PRIM-045, the finite-world update should read exactly as:

```text
canonical old residue space R(S)
        ↓ insert fresh prime q
q children per old seat
        ↓ exactly one reserved
q - 1 surviving children
        ↓ no coordinate collisions
exactly the canonical new residue space R(insert q S)
```

Thus the refinement is not merely an injection into the new support-disjoint seats. It is an exact finite decomposition of the entire enlarged period.

This is still a statement about finite divisibility support. It is not a prime-distribution theorem.

---

# Explicit non-goals

Do **not** add in PRIM-045:

- Euler `Nat.totient` / `Nat.Totient` bridge
- `∏ p in S, (p - 1)` closed formula
- arbitrary recursive / list-based sieve iteration
- PHZ210 explicit 48-residue enumeration
- PHZ2310 or insertion of `11`
- Legendre provider or proof
- prime density / Mertens / PNT
- von Mangoldt
- RH / CFBRC
- category theory

Do not infer primality from membership in any prime-world residue set.

---

# Verification

Run:

```sh
lake build DkMath.NumberTheory.Primitive.PrimeWorldResidues
lake build DkMath.NumberTheory.Primitive.PrimeWorldRefinement
lake build DkMath.NumberTheory.Primitive.PHZ30
lake build DkMath.NumberTheory.Primitive
lake build DkMath.NumberTheory.Legendre
lake build DkMath
git diff --check
```

Audit touched Lean files for new:

```text
sorry
admit
native_decide
axiom
```

Stop after PRIM-045 and report:

1. files changed,
2. final declaration names,
3. whether the canonical coordinate reverse inclusion was proved directly,
4. whether exact Finset equality was obtained,
5. whether PHZ210 is now proven to be the complete one-period support-disjoint residue set,
6. build / audit results,
7. any blocker encountered.
