# Codex Instruction — PRIM-044 Global Seat Refinement Cardinality

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-043 is complete.

The current refinement surface includes:

```text
DkMath.NumberTheory.Primitive.PrimeWorldRefinement
  knownPrimeScales_insert
  primeWorldChild
  primeWorldChildIndices
  reservedChildIndices
  survivingChildIndices
  existsUnique_child_dvd_new_prime
  reservedChildIndices_eq_singleton
  card_survivingChildIndices
  mem_survivingChildIndices_iff_supportDisjointFrom_insert
  card_supportDisjointFrom_insert_prime_children
```

For a certified finite prime world `S`, a fresh prime `q`, and an old period representative `r`, PRIM-043 now proves:

```text
old support-disjoint seat r
  → exactly q - 1 bounded child indices survive
```

where

```text
primeWorldChild S r j = r + j * primeWorldModulus S
```

and `j < q`.

The concrete PHZ30 layer also proves that each of its eight old candidate residues has exactly six surviving child indices after insertion of `7`.

User-reported verification of PRIM-043:

```text
lake build DkMath.NumberTheory.Primitive.PrimeWorldRefinement
lake build DkMath.NumberTheory.Primitive.PHZ30
lake build DkMath.NumberTheory.Primitive
lake build DkMath.NumberTheory.Legendre
lake build DkMath
git diff --check
```

No new `sorry`, `admit`, `native_decide`, or `axiom` were introduced.

Treat this as the accepted starting checkpoint.

---

# Review finding

PRIM-043 counts survivors for **one parent seat**.

To count the whole refined observer without enumerating residues, the missing fact is that the mixed coordinates

```text
(r, j) ↦ r + j * M
```

are injective when

```text
r < M
j < q
M = primeWorldModulus S.
```

Thus child families of distinct old period representatives do not collide.

Once this coordinate injectivity is available, a finite old-seat set `R` with every member support-disjoint and below `M` has exactly

```text
R.card * (q - 1)
```

support-disjoint children after inserting fresh prime `q`.

For PHZ30 and `q = 7`, this should yield

```text
8 * 6 = 48
```

without listing the 48 PHZ210 residues.

This checkpoint should formalize that global finite counting mechanism and stop before an Euler-totient or arbitrary iteration theorem.

---

# Goal

Extend the Primitive refinement API from per-parent counting to finite-family counting.

Preferred owner:

```text
DkMath/NumberTheory/Primitive/PrimeWorldRefinement.lean
```

The concrete `48` corollary belongs in `PHZ30.lean` or a small `PHZ210.lean` only if that makes ownership materially clearer.

Do not introduce an application dependency.

---

# Required reconnaissance

Before defining the global child family, inspect Mathlib for the most convenient existing APIs around:

```text
Finset.product
Finset.sigma / biUnion / bind
Finset.image
Finset.card_product
Finset.card_image_iff
Set.InjOn / Function.Injective
Finset.filter
Finset.sum_card_image / card_biUnion where useful
Nat.mod_eq_of_lt
Nat.add_mul_mod_self_left/right
Nat.mul_left_cancel / mul_right_cancel
```

Prefer a representation whose cardinality proof is simple and whose semantics remain readable.

Do not build a custom finite-set framework if `Finset.product` plus `filter` plus `image` is enough.

---

# Required implementation surface

Names below are preferred, not mandatory. Report final names.

## 1. Parent-child coordinate injectivity

Let

```text
M = primeWorldModulus S.
```

Prove a generic theorem of the form:

```lean
theorem primeWorldChild_eq_iff_of_lt_modulus
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {r₁ r₂ j₁ j₂ : ℕ}
    (hr₁ : r₁ < primeWorldModulus S)
    (hr₂ : r₂ < primeWorldModulus S) :
    primeWorldChild S r₁ j₁ = primeWorldChild S r₂ j₂ ↔
      r₁ = r₂ ∧ j₁ = j₂
```

An implication-only injectivity theorem is acceptable if it is cleaner:

```lean
primeWorldChild S r₁ j₁ = primeWorldChild S r₂ j₂
→ r₁ = r₂ ∧ j₁ = j₂
```

The child-index bounds `j < q` are not mathematically needed for injectivity once both parents are canonical representatives below `M`; do not add them unless the chosen proof requires them.

Use the positivity of the certified modulus from the existing infrastructure. If the current positive-modulus theorem is private and needed publicly here, promote only the minimal reusable fact with an appropriate docstring rather than duplicating its proof.

Preferred proof idea:

```text
r₁ + j₁*M = r₂ + j₂*M
  → reduce modulo M
  → r₁ = r₂ because r₁,r₂ < M
  → cancel the common parent and positive M
  → j₁ = j₂
```

Equivalent arithmetic proofs are fine.

## 2. Global survivor pair set

Define a finite coordinate set for surviving children of a finite parent set `R`.

Preferred conceptual shape:

```lean
def survivingChildPairs
    (S : Finset ℕ) (q : ℕ) (R : Finset ℕ) : Finset (ℕ × ℕ) :=
  (R.product (primeWorldChildIndices q)).filter
    (fun pair => pair.2 ∈ survivingChildIndices S q pair.1)
```

A definition using an equivalent `Finset` construction is acceptable.

Provide a membership theorem exposing exactly:

```text
r ∈ R
j < q
¬ q ∣ primeWorldChild S r j
```

Do not bake `SupportDisjointFrom` into the raw pair-set definition; keep the per-parent wave-avoidance structure reusable.

## 3. Global survivor-pair cardinality

Assume:

```text
KnownPrimeScales S
Nat.Prime q
q ∉ S
∀ r ∈ R, r < primeWorldModulus S
```

Then prove:

```lean
theorem card_survivingChildPairs
    ... :
    (survivingChildPairs S q R).card = R.card * (q - 1)
```

The theorem should reuse `card_survivingChildIndices` for each parent. Do not repeat the unique-reserved-child argument.

The proof may use a product/filter cardinality theorem, a sum over fibers, or a Finset equivalence. Choose the smallest robust Mathlib route.

Note: support-disjointness of the parents is **not needed merely to count indices avoiding the new q-wave**. Keep the cardinality theorem at the weakest correct hypothesis level.

## 4. Refined surviving seat set

Define the actual natural-number child seats as the image of the surviving coordinate pairs:

```lean
def refinedSurvivingSeats
    (S : Finset ℕ) (q : ℕ) (R : Finset ℕ) : Finset ℕ :=
  (survivingChildPairs S q R).image
    (fun pair => primeWorldChild S pair.1 pair.2)
```

Then prove, using section 1 injectivity, that under canonical-parent bounds:

```lean
theorem card_refinedSurvivingSeats
    ... :
    (refinedSurvivingSeats S q R).card = R.card * (q - 1)
```

The proof should visibly separate:

```text
coordinate count
  + injective coordinate encoding
  = seat count
```

Do not prove the result by recomputing divisibility over the entire new modulus.

## 5. Semantic refined-seat theorem

When every old parent is a valid old-world seat,

```text
∀ r ∈ R, SupportDisjointFrom S r,
```

prove that every seat in `refinedSurvivingSeats S q R` is support-disjoint from `insert q S`.

Preferred shape:

```lean
theorem supportDisjointFrom_of_mem_refinedSurvivingSeats
    {S : Finset ℕ} {q : ℕ} {R : Finset ℕ}
    (hq : Nat.Prime q)
    (hRseat : ∀ r ∈ R, SupportDisjointFrom S r)
    {n : ℕ}
    (hn : n ∈ refinedSurvivingSeats S q R) :
    SupportDisjointFrom (insert q S) n
```

Reuse `mem_survivingChildIndices_iff_supportDisjointFrom_insert` or `supportDisjointFrom_insert_prime_child_iff`.

This theorem is what turns a combinatorial child count into a refined Primitive observer count.

## 6. Optional exact bounded classification

If it is inexpensive after the above, prove that when `R` is the **complete** set of old support-disjoint representatives below `M`, `refinedSurvivingSeats` is the complete set of support-disjoint representatives below `q*M` for `insert q S`.

This is optional in PRIM-044.

Do not let this exact-surjectivity step block the required global cardinality result. If it becomes awkward, stop with the injection/cardinality/semantic inclusion theorems and report the missing reverse-classification lemma.

---

# Concrete PHZ30 → PHZ210 certificate

Use the existing explicit old set:

```text
phzResidues30 = {1,7,11,13,17,19,23,29}
```

and fresh prime `7`.

Do **not** enumerate the 48 new residues.

Add a named finite set only if useful, for example:

```lean
def phzResidues210 : Finset ℕ :=
  refinedSurvivingSeats primeWorld235 7 phzResidues30
```

If introduced, clearly document that this is a constructive definition from refinement, not a literal 48-element list.

Required concrete result:

```lean
theorem card_phzResidues210 :
    phzResidues210.card = 48
```

or an equivalent theorem directly on `refinedSurvivingSeats`.

Derive it structurally from:

```text
phzResidues30.card = 8
q - 1 = 6
8 * 6 = 48
```

Do not use `interval_cases` over `0..209` to establish the count.

If `phzResidues30.card = 8` is not already exposed, add a tiny certificate theorem for it.

Also prove that every member of the constructed 210-seat set is support-disjoint from `insert 7 primeWorld235`.

If the optional exact bounded classification from section 6 is completed, then a global theorem of the form

```text
SupportDisjointFrom (insert 7 primeWorld235) m
  ↔ m % 210 ∈ phzResidues210
```

is allowed, but it is **not required** for this checkpoint.

---

# Important mathematical invariants

The global multiplication theorem must mean:

```text
number of old parent seats
× surviving children per parent
= number of distinct refined seats
```

The distinctness factor is not automatic. It must be justified by the parent-child coordinate injectivity theorem.

Do not silently assume child families are disjoint.

The result remains a finite support observer statement. It does not imply that the surviving seats are prime.

---

# Explicit non-goals

Do not implement in PRIM-044:

```text
literal enumeration of all 48 PHZ210 residues
arbitrary iteration over a list/Finset of fresh primes
closed formula ∏ (p - 1)
Euler totient / Nat.totient bridge
prime density or asymptotics
proof of SquareAnchoredSupportEscape
proof of LegendreConjecture
PNT / Mertens
RH / CFBRC
von Mangoldt weights
category-theory abstractions
```

Do not replace the existing concrete PHZ30 list with a new abstraction.

Do not introduce a new CRT abstraction; PRIM-042 already owns the necessary CRT arithmetic.

---

# Public aggregation

If no new module is created, `Primitive.lean` may need no change because `PrimeWorldRefinement` is already imported.

If a new generic module is created, import it in `DkMath.NumberTheory.Primitive` after `PrimeWorldRefinement`.

If a concrete `PHZ210.lean` is created, place it after the generic refinement layer and avoid making generic modules import it.

---

# Verification

Run at least:

```sh
lake build DkMath.NumberTheory.Primitive.PrimeWorldRefinement
lake build DkMath.NumberTheory.Primitive.PHZ30
# plus PHZ210 module if created
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
2. final parent-child injectivity theorem name;
3. global survivor pair/seat definitions;
4. exact global cardinality theorem names;
5. whether semantic support-disjointness of every refined seat was proved;
6. whether exact bounded reverse classification was attempted/completed;
7. whether a named `phzResidues210` was introduced;
8. the theorem proving the concrete total `48` without residue enumeration;
9. build results;
10. confirmation that no Euler-totient bridge, arbitrary iteration, Legendre provider, or 48-element literal list was introduced.

Stop after PRIM-044.

The next review will decide between:

```text
PRIM-045  iterated fresh-prime refinement and product cardinality
PRIM-046  Euler-totient bridge for certified squarefree prime worlds
PRIM-L005 square-window localization against the refined observer
```
