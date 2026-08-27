# Codex Instruction — PRIM-041C Concrete `{2,3,5}` / 30-Period PHZ Certificate

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-041B is complete.

The generic periodic finite-world observer now provides:

```text
DkMath.NumberTheory.Primitive.PeriodicPrimeWorld
  primeWorldModulus
  supportDisjointFrom_add_mul_primeWorldModulus_iff
  supportDisjointFrom_mod_primeWorldModulus_iff
  supportDisjointFrom_mul_primeWorldModulus_sub_iff
  supportDisjointFrom_mul_primeWorldModulus_add_iff
  supportDisjointFrom_centered_mirror_iff
  supportDisjointFrom_primeScalesUpTo_centered_mirror_iff
```

The main generic facts are:

```text
SupportDisjointFrom S (m + k*M) ↔ SupportDisjointFrom S m
SupportDisjointFrom S (m % M) ↔ SupportDisjointFrom S m
SupportDisjointFrom S (k*M-r) ↔ SupportDisjointFrom S (k*M+r)
```

where `M = primeWorldModulus S` and the mirror theorem carries the required natural-subtraction bound.

No primality conclusion follows from these observer theorems alone.

Legendre's unresolved `SquareAnchoredSupportEscape` remains unproved and must remain so in this checkpoint.

---

# Goal

Build the first complete concrete PHZ observer certificate by specializing the generic Primitive periodic API to the finite prime world

```text
S = {2,3,5}
```

with modulus

```text
M = 30.
```

The checkpoint should prove exactly which residues in one period are support-disjoint from `{2,3,5}` and then lift that finite classification to all naturals through the already-proved modulo normalization theorem.

This is a concrete classification of **candidate seats**, not a classification of primes.

Preferred new file:

```text
DkMath/NumberTheory/Primitive/PHZ30.lean
```

A similarly clear name is acceptable if repository conventions suggest one.

Keep the dependency direction:

```text
FinitePrimeWorld
    ↓
PeriodicPrimeWorld
    ↓
PHZ30 concrete certificate
```

Do not import `Legendre` into the concrete observer module.

---

# Required implementation surface

Names below are preferred, not mandatory. Report final names.

## 1. Concrete finite world

Define or expose a canonical concrete set for the base world:

```lean
def primeWorld235 : Finset ℕ := {2, 3, 5}
```

Avoid repeating the literal set in every theorem if a small named definition improves readability.

Prove the certified-prime property:

```lean
theorem knownPrimeScales_primeWorld235 :
    KnownPrimeScales primeWorld235
```

If the existing theorem `knownPrimeScales_two_three_five` from `StructuralArithmetic.FinitePrimeEscapeBridge` can be reused without importing the Hackathon path or pulling unnecessary dependencies, consider it. Otherwise prove the tiny certificate locally with `norm_num`.

Do not introduce a dependency on the Hackathon layer solely for this certificate.

## 2. Modulus certificate

Prove:

```lean
@[simp] theorem primeWorldModulus_primeWorld235 :
    primeWorldModulus primeWorld235 = 30
```

Use `norm_num` / `simp` and the existing definition. No `native_decide`.

This theorem is the concrete bridge from the generic modulus observer to 30-period coordinates.

## 3. Concrete unreserved residue set

Define the one-period support-disjoint residue set:

```lean
def phzResidues30 : Finset ℕ :=
  {1, 7, 11, 13, 17, 19, 23, 29}
```

The exact Lean construction may use nested insert notation or another stable `Finset` expression.

The important semantic contract is that this set is the complete list of residues `r < 30` not divisible by 2, 3, or 5.

## 4. Exact one-period classification

Prove the main finite certificate:

```lean
theorem supportDisjointFrom_primeWorld235_iff_mem_phzResidues30
    {r : ℕ} (hr : r < 30) :
    SupportDisjointFrom primeWorld235 r ↔
      r ∈ phzResidues30
```

This theorem must be **complete in both directions**.

Acceptable proof strategies:

```text
A. rewrite SupportDisjointFrom using the coprime-modulus theorem,
   rewrite modulus = 30,
   then finish the bounded finite arithmetic classification;

B. unfold the finite set and support predicate directly,
   reducing to divisibility by 2, 3, and 5;

C. use interval / Finset filtering if that produces a cleaner exact theorem.
```

Prefer a proof whose mathematical content is visibly the finite residue classification rather than a large opaque tactic block.

`decide` is acceptable for small decidable propositions if repository style permits it. `native_decide` is not allowed.

Do not define `phzResidues30` as a filter whose membership theorem is tautological unless there is also a theorem proving the filter equals the explicit eight-element set. The explicit residue certificate is the point of this checkpoint.

## 5. Global modulo classification

Use the existing generic theorem

```text
supportDisjointFrom_mod_primeWorldModulus_iff
```

plus the modulus certificate to prove the all-natural classification:

```lean
theorem supportDisjointFrom_primeWorld235_iff_mod_mem_phzResidues30
    {m : ℕ} :
    SupportDisjointFrom primeWorld235 m ↔
      m % 30 ∈ phzResidues30
```

This is the main PHZ30 theorem.

The proof should visibly factor as:

```text
m
  ↓ mod 30
one-period residue
  ↓ exact finite classification
membership in {1,7,11,13,17,19,23,29}
```

Do not re-prove generic periodicity.

## 6. `30*k+r` coordinate wrapper

Add a thin coordinate theorem if useful:

```lean
theorem supportDisjointFrom_primeWorld235_add_thirty_mul_iff
    {k r : ℕ} :
    SupportDisjointFrom primeWorld235 (r + 30 * k) ↔
      SupportDisjointFrom primeWorld235 r
```

or the equivalent `30*k+r` orientation.

This should be a corollary of the generic period theorem plus `primeWorldModulus_primeWorld235`.

Do not duplicate the divisibility proof.

## 7. Concrete mirror pairing

Use the already-proved generic centered mirror theorem to expose the concrete residue symmetry under `r ↦ 30-r`.

Preferred generic concrete theorem:

```lean
theorem supportDisjointFrom_primeWorld235_mirror_iff
    {r : ℕ} (hr : r ≤ 30) :
    SupportDisjointFrom primeWorld235 (30 - r) ↔
      SupportDisjointFrom primeWorld235 (30 + r)
```

However, for the actual one-period residue list the more useful relation is residue negation modulo 30:

```text
r ↔ 30-r
```

for `0 < r < 30`.

If inexpensive, prove:

```lean
theorem mem_phzResidues30_sub_iff
    {r : ℕ} (hr0 : 0 < r) (hr30 : r < 30) :
    (30 - r ∈ phzResidues30) ↔ (r ∈ phzResidues30)
```

and/or named certificates for the four visible pairs:

```text
1  ↔ 29
7  ↔ 23
11 ↔ 19
13 ↔ 17
```

Do not spend excessive code on eight separate pair theorems if the generic residue-reflection theorem already captures them cleanly.

---

# Mathematical interpretation

After this checkpoint the concrete observer should certify:

```text
SupportDisjointFrom {2,3,5} m
  ↔ m % 30 ∈ {1,7,11,13,17,19,23,29}
```

Equivalently, every natural position belongs to one of 30 residue seats, and exactly eight seats survive the old waves generated by 2, 3, and 5.

This says only:

```text
not divisible by 2, 3, or 5
```

It does **not** say:

```text
prime
```

For example, the theorem classifies candidate seats globally; primality requires an independent closure theorem such as `SquareBody` with the appropriate support world and range bound.

Keep this distinction explicit in module and theorem docstrings.

---

# Explicit non-goals

Do not implement:

```text
proof of SquareAnchoredSupportEscape
proof of LegendreConjecture
claim that every PHZ30 seat is prime
PRIM-042 update from {2,3,5} to {2,3,5,7}
CRT child-seat refinement
general Euler phi/cardinality theorem
asymptotic density of surviving seats
PNT / Mertens / analytic number theory
prime-power depth / von Mangoldt mass
RH / CFBRC imports
```

Do not extend the 30-stage Body horizon or make claims about where the 30-observer alone remains a primality certificate. That connection belongs to separate square-Body/application theorems.

---

# Public aggregation

If `PHZ30.lean` is a reusable public Primitive observer example, add it to:

```text
DkMath/NumberTheory/Primitive.lean
```

after `PeriodicPrimeWorld` and before `SquareBody` if the dependency graph permits.

If it is better treated as a concrete example layer rather than core facade, it may remain separately importable. Explain the choice in the report.

Do not add a `Legendre` dependency to the Primitive aggregator.

---

# Documentation

Add module documentation explaining:

1. `{2,3,5}` is the first concrete finite prime world;
2. its product modulus is 30;
3. the eight listed residues are exactly the support-disjoint candidate seats;
4. periodicity and mirror symmetry come from generic `PeriodicPrimeWorld` theorems;
5. no primality conclusion is made by PHZ30 itself.

Do not describe 30 as a permanent or universal prime sieve modulus.

---

# Verification

Run at least:

```sh
lake build DkMath.NumberTheory.Primitive.PHZ30
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
2. final concrete world and residue-set declaration names;
3. exact theorem proving the modulus is 30;
4. exact theorem classifying support-disjoint residues below 30;
5. exact theorem lifting the classification to arbitrary `m` through `m % 30`;
6. mirror/reflection theorem(s) added, if any;
7. whether `PHZ30` was added to the public Primitive aggregator;
8. build results;
9. confirmation that no prime conclusion, Legendre provider, or CRT update was introduced.

Stop after PRIM-041C. The next review should decide whether PRIM-042 should formalize the update

```text
{2,3,5} → {2,3,5,7}
```

as a generic finite-world refinement theorem before specializing it to 30 → 210.