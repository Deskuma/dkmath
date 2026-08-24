# Codex Instruction — PRIM-043 Survivor Cardinality / Iterated Refinement

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-042 is complete.

The current generic refinement surface is:

```text
DkMath.NumberTheory.Primitive.PrimeWorldRefinement
  supportDisjointFrom_insert_prime_iff
  primeWorldModulus_insert
  prime_coprime_primeWorldModulus_of_not_mem
  primeWorldChild
  supportDisjointFrom_child_iff
  supportDisjointFrom_insert_prime_child_iff
  existsUnique_child_dvd_new_prime
  exists_unique_reserved_child_and_other_children_survive
```

The main certified refinement fact is:

```text
old support-disjoint seat r
+ fresh prime q
+ old modulus M

children: r + j*M, 0 <= j < q

=> exactly one child lies on the new q-wave
=> every other bounded child survives in insert q S
```

The concrete PHZ30 layer additionally certifies:

```text
primeWorld235 = primeScalesUpTo 5
primeWorldModulus primeWorld235 = 30
primeWorldModulus (insert 7 primeWorld235) = 210
```

PHZ210 residues have not been enumerated.

User-reported verification of PRIM-042:

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

PRIM-042 already proves existence and uniqueness of the reserved child index. Therefore the mathematical content

```text
q children = 1 reserved + (q - 1) survivors
```

is present propositionally, but it is not yet exposed as a finite cardinality theorem.

Also, to iterate refinement cleanly, the enlarged finite world should carry forward a `KnownPrimeScales` certificate.

The next checkpoint should therefore convert the existential refinement theorem into a reusable Finset/cardinality API and make one-step refinement composable.

This checkpoint is **not** a PHZ210 residue-enumeration task.

---

# Goal

Create the first counting layer for finite prime-world refinement.

Preferred location:

```text
DkMath/NumberTheory/Primitive/PrimeWorldRefinement.lean
```

A sibling file such as

```text
DkMath/NumberTheory/Primitive/PrimeWorldRefinementCount.lean
```

is acceptable only if the existing file would become materially clearer by splitting. Avoid module fragmentation for a small amount of code.

The principal new fact is:

```text
an old support-disjoint seat has exactly q - 1 surviving bounded children
```

for a fresh prime `q`.

---

# Required reconnaissance

Before adding definitions, inspect Mathlib for the current forms of:

```text
Finset.filter
Finset.range
Finset.card_filter
Finset.card_erase
Finset.card_erase_of_mem
Finset.card_range
Finset.filter_eq_erase
Finset.filter_not
Finset.ext
Finset.card_congr
Nat.card_sub
```

Prefer a short proof from the already-proved unique reserved child. Do not redo the CRT argument inside a cardinality proof.

The expected strategy is conceptually:

```text
child indices = range q
reserved indices = exactly {j0}
survivor indices = range q \ {j0}
card = q - 1
```

Equivalent Finset formulations are acceptable.

---

# Required implementation surface

Names below are preferred, not mandatory. Report final names.

## 1. Preserve the certified-prime-world invariant under insertion

Prove:

```lean
theorem knownPrimeScales_insert
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q : ℕ} (hq : Nat.Prime q) :
    KnownPrimeScales (insert q S)
```

This theorem does **not** require `q ∉ S`; repeated insertion does not invalidate the certificate.

Keep it elementary and semantic.

This is the main composability certificate for repeated refinement.

## 2. Bounded child-index set

Introduce a compact reusable child-index set if it improves theorem statements:

```lean
def primeWorldChildIndices (q : ℕ) : Finset ℕ :=
  Finset.range q
```

This alias is optional. If it adds no value, use `Finset.range q` directly.

Do not create aliases merely for naming symmetry.

## 3. Reserved child-index set

Prefer a semantic Finset of bounded child indices hit by the new `q`-wave:

```lean
def reservedChildIndices
    (S : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun j => q ∣ primeWorldChild S r j)
```

If repository naming suggests a better spelling, use it.

The key theorem should identify this set as a singleton under the PRIM-042 hypotheses.

Conceptual target:

```lean
theorem reservedChildIndices_eq_singleton
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q r : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hr : r < primeWorldModulus S) :
    ∃ j0,
      j0 < q ∧
      reservedChildIndices S q r = {j0}
```

Prefer deriving this from `existsUnique_child_dvd_new_prime` rather than rebuilding modular arithmetic.

An equivalent theorem that directly proves `.card = 1` is acceptable, but singleton equality is more useful downstream if it stays simple.

## 4. Survivor child-index set

Define conceptually:

```lean
def survivingChildIndices
    (S : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun j => ¬ q ∣ primeWorldChild S r j)
```

At this level the definition refers only to avoidance of the new prime. For an old support-disjoint parent, use `supportDisjointFrom_insert_prime_child_iff` to reinterpret it as refined-world survival.

Required exact semantic theorem:

```lean
theorem mem_survivingChildIndices_iff
    {S : Finset ℕ} {q r j : ℕ} :
    j ∈ survivingChildIndices S q r ↔
      j < q ∧ ¬ q ∣ primeWorldChild S r j
```

If simp already gives this for free, expose only if it materially improves later proofs.

## 5. Main cardinality theorem

This is the central checkpoint result.

Prove:

```lean
theorem card_survivingChildIndices
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q r : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hr : r < primeWorldModulus S) :
    (survivingChildIndices S q r).card = q - 1
```

The proof should reuse the unique reserved-child theorem.

Do not re-prove CRT or modular uniqueness.

Mathematical invariant:

```text
q bounded children
- exactly one reserved child
= q - 1 survivors
```

Because `Nat.Prime q` implies `1 < q`, no awkward `q = 0` or `q = 1` exception should need to leak into the public theorem.

## 6. Refined-world survival interpretation

For a support-disjoint parent seat, prove that survivor-index membership is exactly support disjointness in the enlarged world.

Conceptual target:

```lean
theorem mem_survivingChildIndices_iff_supportDisjointFrom_insert
    {S : Finset ℕ} {q r j : ℕ}
    (hq : Nat.Prime q)
    (hrSeat : SupportDisjointFrom S r) :
    j ∈ survivingChildIndices S q r ↔
      j < q ∧
      SupportDisjointFrom (insert q S) (primeWorldChild S r j)
```

Use the existing `supportDisjointFrom_insert_prime_child_iff`.

This theorem should make the cardinality statement visibly about actual refined-world candidate seats, not merely `¬ q ∣ ...`.

## 7. Cardinality theorem in support language

If section 6 is clean, add one theorem exposing the exact count of refined support-disjoint children.

A Finset of indices is preferred over a Finset of child values to avoid injectivity bookkeeping unless a child-value set is clearly useful.

Conceptual theorem:

```text
for an old support-disjoint seat r,
there are exactly q - 1 indices j < q
whose child remains SupportDisjointFrom (insert q S)
```

The exact Lean shape may reuse `survivingChildIndices` rather than defining a duplicate filtered set.

---

# Optional concrete PHZ30 → PHZ210 count certificate

After the generic theorem is complete, add a thin concrete certificate in `PHZ30.lean` only if it is genuinely small.

For each `r ∈ phzResidues30`, insertion of `7` gives exactly six surviving child indices:

```text
card = 7 - 1 = 6
```

A preferred theorem may quantify over `r`:

```lean
theorem card_seven_refinement_survivors_of_mem_phzResidues30
    {r : ℕ}
    (hr : r ∈ phzResidues30) :
    (survivingChildIndices primeWorld235 7 r).card = 6
```

You may need the existing one-period theorem to derive:

```text
r < 30
SupportDisjointFrom primeWorld235 r
```

from membership in the explicit residue set. If membership alone does not directly imply the bound in a clean way, add a tiny helper theorem:

```text
r ∈ phzResidues30 -> r < 30
```

Do not enumerate the 48 PHZ210 residues.

A global theorem that the total number of refined residue seats is `8 * 6 = 48` is **optional**, and should only be attempted if it follows from a clean disjoint-union/cardinality argument without substantial new machinery.

Do not force it in this checkpoint.

---

# Iteration boundary

Do not yet define a recursive prime-world construction over a list/finset of primes unless the one-step cardinality API makes it nearly trivial.

The next review should decide whether to proceed to:

```text
PRIM-044A  total PHZ210 count = 48 without enumeration
PRIM-044B  iterated refinement / product of (p - 1)
PRIM-044C  Euler-phi bridge for certified squarefree prime worlds
```

PRIM-043 should make those routes possible but should not collapse them into one oversized checkpoint.

---

# Explicit non-goals

Do not implement:

```text
explicit 48-residue PHZ210 list
proof that surviving seats are prime
proof of LegendreConjecture
proof of SquareAnchoredSupportEscape
prime-density estimates
PNT / Mertens
RH / CFBRC imports
von Mangoldt weights
new abstract CRT framework
category theory
recursive global sieve engine
```

Do not introduce a theorem parameter or structure field that assumes any conjecture-equivalent provider.

---

# Public aggregation

If no new sibling module is created, no aggregator change should be necessary beyond the existing `PrimeWorldRefinement` import.

If a new `PrimeWorldRefinementCount.lean` module is created, import it from:

```text
DkMath/NumberTheory/Primitive.lean
```

after `PrimeWorldRefinement` and before concrete PHZ modules.

Keep dependency direction:

```text
FinitePrimeWorld
    ↓
PeriodicPrimeWorld
    ↓
PrimeWorldRefinement
    ↓
Refinement cardinality
    ↓
PHZ30 concrete certificate
```

---

# Verification

Run at least:

```sh
lake build DkMath.NumberTheory.Primitive.PrimeWorldRefinement
lake build DkMath.NumberTheory.Primitive.PHZ30
lake build DkMath.NumberTheory.Primitive
lake build DkMath.NumberTheory.Legendre
lake build DkMath
git diff --check
```

If a new sibling module is created, build it explicitly as well.

Check all touched Lean files for newly introduced:

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
3. whether `KnownPrimeScales (insert q S)` is certified generically;
4. the final survivor-index Finset definition, if introduced;
5. the theorem identifying the unique reserved index / singleton reserved set;
6. the theorem proving exactly `q - 1` surviving child indices;
7. the theorem translating survivor-index membership into refined-world `SupportDisjointFrom`;
8. whether a concrete PHZ30 → 7-refinement `card = 6` certificate was added;
9. whether any total `48` theorem was added (optional only);
10. build results;
11. confirmation that no explicit PHZ210 residue enumeration, Legendre provider, or primality claim was introduced.

Stop after PRIM-043.