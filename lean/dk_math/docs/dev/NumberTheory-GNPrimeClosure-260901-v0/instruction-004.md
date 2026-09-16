# Codex Instruction — GNPC-004 Prime Target Degree Divisibility / Residue Filter

Branch: `wip/number-theory-gn-prime-closure-260901-v0`

Project: DkMath NumberTheory GN Prime Closure

Start from current GNPC-003 implementation commit:

```text
7ba6c8fe9010143bffeff992567648cfc251f7e7
```

Read first:

```text
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/README.md
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-002.md
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-003.md
lean/dk_math/DkMath/NumberTheory/GNRepresentationBounds.lean
lean/dk_math/DkMath/NumberTheory/GNDegreeFactorization.lean
lean/dk_math/DkMath/NumberTheory/WeightedGNBridge.lean
```

---

# 0. Current verified state

GNPC-002 gives, for every positive representation

```lean
hrep : GNPositiveRepresentation p d x u
```

the bounds

```text
d < p
x < p
u < p
```

and the exact target equation

```text
GN d x u = p.
```

GNPC-003 gives, for a prime target,

```lean
GNPositiveRepresentation.degree_prime_of_target_prime
```

so the representation degree `d` is prime.

Separately, DkMath already exposes the prime-row GN congruence API in

```text
DkMath/NumberTheory/WeightedGNBridge.lean
```

including:

```lean
prime_GN_modEq_rightBoundary
prime_GN_modEq_one_of_not_dvd_x
prime_not_dvd_GN_of_not_dvd_x
```

The relevant statements are:

```lean
prime_GN_modEq_rightBoundary
    {q x u : ℕ} (hq : q.Prime) :
    GN q x u ≡ x ^ (q - 1) [MOD q]
```

and

```lean
prime_GN_modEq_one_of_not_dvd_x
    {q x u : ℕ} (hq : q.Prime) (hx : ¬ q ∣ x) :
    GN q x u ≡ 1 [MOD q]
```

GNPC-004 must connect these existing layers.  Do not reprove the weighted-binomial congruence theory.

---

# 1. Mathematical target

Fix a positive nondegenerate prime-target representation

$$
GN_d(x,u)=p,
$$

with

```text
GNPositiveRepresentation p d x u
Nat.Prime p.
```

From GNPC-003,

$$
d\text{ is prime}.
$$

From GNPC-002,

$$
d<p.
$$

The first new target is to show that the degree prime cannot divide the GN boundary coordinate:

$$
d\nmid x.
$$

Reason:

1. Suppose `d ∣ x`.
2. Since `d` is prime, `prime_GN_modEq_rightBoundary` gives

$$
GN_d(x,u)\equiv x^{d-1}\equiv0\pmod d.
$$

3. Hence `d ∣ GN d x u = p`.
4. Since `d` and `p` are both prime, this forces `d = p`.
5. This contradicts the already-proved strict bound `d < p`.

Once `¬ d ∣ x` is available, reuse

```lean
prime_GN_modEq_one_of_not_dvd_x
```

to obtain

$$
GN_d(x,u)\equiv1\pmod d.
$$

Using `GN d x u = p`, obtain the prime-target residue constraint

$$
p\equiv1\pmod d.
$$

Finally convert this to

$$
d\mid p-1.
$$

This is the main GNPC-004 filter.

---

# 2. Mandatory reconnaissance before Lean changes

Before writing proofs:

1. Search the repository for any existing theorem already proving one of:
   - `¬ d ∣ x` from a prime GN target;
   - `GN ... ≡ 1 [MOD d]` under a prime-target representation;
   - `d ∣ p - 1` for GN prime representations.

2. Confirm the exact current theorem types of:

```lean
GNPositiveRepresentation.bounds
GNPositiveRepresentation.degree_prime_of_target_prime
prime_GN_modEq_rightBoundary
prime_GN_modEq_one_of_not_dvd_x
```

3. Search Mathlib for the canonical theorem(s) needed to:
   - turn `d ∣ p` with both `d.Prime` and `p.Prime` into `d = p`;
   - turn a `Nat.ModEq d p 1` statement into `d ∣ p - 1`.

Do not guess theorem names.  If direct Mathlib conversion is awkward, prove a tiny local arithmetic bridge instead of importing heavy theory.

4. Check whether the new theorem surface belongs in a new thin module, expected default:

```text
DkMath/NumberTheory/GNPrimeTargetResidue.lean
```

If an existing thin GN prime-target owner is clearly better, document the choice in the report.

---

# 3. Required theorem surface

The exact final names may be adjusted slightly after reconnaissance, but keep the API shape and dependency direction.

## P0 — boundary nondivisibility is automatic

Preferred theorem:

```lean
theorem GNPositiveRepresentation.degree_not_dvd_boundary_of_target_prime
    {p d x u : ℕ}
    (hrep : GNPositiveRepresentation p d x u)
    (hp : Nat.Prime p) :
    ¬ d ∣ x := by
  ...
```

This theorem must use the already-proved degree primality and strict degree bound rather than add them as duplicate hypotheses.

## P1 — prime target is one modulo its GN degree

Preferred theorem:

```lean
theorem GNPositiveRepresentation.target_modEq_one_degree_of_target_prime
    {p d x u : ℕ}
    (hrep : GNPositiveRepresentation p d x u)
    (hp : Nat.Prime p) :
    p ≡ 1 [MOD d] := by
  ...
```

This should be a thin composition of P0, `degree_prime_of_target_prime`, and the existing `prime_GN_modEq_one_of_not_dvd_x`, followed by rewriting the representation value.

## P2 — degree divides target minus one

Preferred theorem:

```lean
theorem GNPositiveRepresentation.degree_dvd_target_sub_one_of_target_prime
    {p d x u : ℕ}
    (hrep : GNPositiveRepresentation p d x u)
    (hp : Nat.Prime p) :
    d ∣ p - 1 := by
  ...
```

This is the primary GNPC-004 endpoint.

## P3 — package the degree filters

Add one ergonomic package theorem if it remains thin:

```lean
theorem GNPositiveRepresentation.prime_degree_constraints
    {p d x u : ℕ}
    (hrep : GNPositiveRepresentation p d x u)
    (hp : Nat.Prime p) :
    Nat.Prime d ∧ d ∣ p - 1 ∧ 2 ^ d - 1 ≤ p := by
  ...
```

The floor term should come from `GNPositiveRepresentation.bounds`; do not reprove it.

If conjunction ordering is more natural in Lean, adjust it, but document the exact final theorem type.

---

# 4. Proof architecture guidance

Prefer this dependency chain:

```text
GNPositiveRepresentation p d x u
        + Nat.Prime p
        ↓
degree_prime_of_target_prime
        ↓
Nat.Prime d
        + bounds gives d < p
        ↓
assume d ∣ x
        ↓
prime_GN_modEq_rightBoundary
        ↓
GN d x u ≡ 0 [MOD d]
        ↓
d ∣ GN d x u = p
        ↓
d = p
        ↓ contradiction with d < p
        ↓
¬ d ∣ x
        ↓
prime_GN_modEq_one_of_not_dvd_x
        ↓
GN d x u ≡ 1 [MOD d]
        ↓ rewrite target
p ≡ 1 [MOD d]
        ↓
d ∣ p - 1
```

Do not re-expand `GN` into a binomial sum in GNPC-004 unless absolutely necessary.  The point of this checkpoint is to connect existing GN layers.

---

# 5. Important edge cases

The theorem surface is intentionally restricted to `GNPositiveRepresentation`, so the following are already excluded:

```text
d ≤ 1
x = 0
u = 0
```

Do not weaken the positive-representation vocabulary in this checkpoint.

The target `p` is explicitly prime.  Therefore `p > 1`; no theorem should need an additional `1 < p` hypothesis.

Do not assume `d ∤ x` as an input hypothesis in P1/P2.  Proving that it is automatic is one of the main GNPC-004 results.

---

# 6. Optional executable degree filter

Only if the required P0–P3 surface is already clean and build-stable, an optional finite candidate set may be added.

For fixed prime target `p`, define a `Finset ℕ` of degree candidates satisfying at least:

```text
Nat.Prime d
d ∣ p - 1
2 ^ d - 1 ≤ p
```

and prove that every positive GN representation degree belongs to it.

Suggested concept only:

```lean
def GNPrimeDegreeCandidates (p : ℕ) : Finset ℕ := ...

theorem GNPositiveRepresentation.degree_mem_primeDegreeCandidates
    {p d x u : ℕ}
    (hrep : GNPositiveRepresentation p d x u)
    (hp : Nat.Prime p) :
    d ∈ GNPrimeDegreeCandidates p := by
  ...
```

This is optional.  Do not delay P0–P3 for executable filtering.

---

# 7. Regression anchors

Use only tiny checks.  Good candidates:

- target `p = 31`:
  candidate prime degrees satisfying `d ∣ 30` are `2`, `3`, `5`;
- `GN 5 1 1 = 31` should satisfy `5 ∣ 30`;
- `GN 3 4 1 = 31` should satisfy `3 ∣ 30`.

Do not add a large native-decide search campaign.

---

# 8. Forbidden scope expansion in GNPC-004

Do not implement in this checkpoint:

- cyclotomic factorization;
- uniqueness/classification of `(x,u)` representations;
- primitive-prime or Zsigmondy existence;
- converse claims such as `d ∣ p - 1 → ∃ x u, GN d x u = p`;
- sufficiency of prime degree for GN primality;
- ABC / FLT / Legendre / RH applications;
- logarithmic or root-based optimization of the search box;
- arbitrary semiring generalization;
- repository-wide GN renaming/refactor.

GNPC-004 stops at the prime-target residue/degree-divisibility filter.

---

# 9. Validation

Build at least the final owner module, expected:

```text
lake build DkMath.NumberTheory.GNPrimeTargetResidue
```

If another owner is chosen, build that module instead.

If an aggregator is changed, build it as well.

Requirements:

- no new `sorry`;
- no new `axiom`;
- no warning-producing unused arguments in the final theorem surface;
- keep imports as thin as practical.

---

# 10. Required report

Write:

```text
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-004.md
```

Include:

1. Outcome A / B / C.
2. Exact existing DkMath congruence theorems reused.
3. Exact Mathlib theorem(s) used for prime-divisor equality and ModEq-to-divisibility conversion, or the local bridge if needed.
4. Final owner module and imports.
5. Changed files.
6. Final theorem types for P0–P3.
7. Build results.
8. Whether the optional executable degree filter was added.
9. Deferred items.

---

# 11. Stop condition

STOP when the following logical chain is formally available and validated:

```text
positive GN representation of prime p
        ↓
d is prime
        ↓
d ∤ x
        ↓
p ≡ 1 [MOD d]
        ↓
d ∣ p - 1
```

Do not continue automatically into cyclotomic or representation-classification work.
