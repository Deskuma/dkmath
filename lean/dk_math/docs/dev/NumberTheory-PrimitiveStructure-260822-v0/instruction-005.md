# Codex Instruction — PRIM-042 Prime-Direction Observer Refinement

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-041C is complete.

The current reusable observer surface includes:

```text
DkMath.NumberTheory.Primitive.FinitePrimeWorld
  primeScalesUpTo
  SupportDisjointFrom bridge

DkMath.NumberTheory.Primitive.PeriodicPrimeWorld
  primeWorldModulus
  supportDisjointFrom_add_mul_primeWorldModulus_iff
  supportDisjointFrom_mod_primeWorldModulus_iff
  supportDisjointFrom_centered_mirror_iff

DkMath.NumberTheory.Primitive.PHZ30
  primeWorld235
  phzResidues30
  primeWorldModulus_primeWorld235
  supportDisjointFrom_primeWorld235_iff_mod_mem_phzResidues30
```

The concrete certified classification is:

```text
SupportDisjointFrom {2,3,5} m
  ↔ m % 30 ∈ {1,7,11,13,17,19,23,29}
```

This is candidate-seat classification only.  No primality theorem or Legendre provider is contained in it.

User-reported verification of PRIM-041C:

```text
lake build DkMath.NumberTheory.Primitive.PHZ30
lake build DkMath.NumberTheory.Primitive
lake build DkMath.NumberTheory.Legendre
lake build DkMath
git diff --check
```

Touched files contain no new `sorry`, `admit`, `native_decide`, or `axiom`.

Treat this as the accepted starting checkpoint.

---

# Mathematical target

PRIM-041 built a static finite-world observer.  PRIM-042 should formalize how that observer changes when one fresh prime direction is added.

Let

```text
S = old finite prime world
q = new prime direction, q ∉ S
M = primeWorldModulus S
```

An old residue seat `r` lifts to the `q` children

```text
r + 0*M
r + 1*M
...
r + (q-1)*M.
```

All `q` children have the same old-`S` support state by periodicity.

Because `q` is fresh and therefore coprime to `M`, exactly one of those `q` children is divisible by `q`.  The other `q-1` children remain support-disjoint after passing from `S` to `insert q S`.

The intended picture is:

```text
old seat r modulo M
       |
       | split into q children
       v
r + j*M, 0 ≤ j < q
       |
       | exactly one child hits q-wave
       v
q-1 surviving seats modulo q*M
```

This is the generic observer refinement rule behind the concrete transition

```text
{2,3,5}  →  {2,3,5,7}
30       →  210.
```

Do not enumerate all 48 period-210 survivors in this checkpoint.

---

# Required reconnaissance

Before proving the existence/uniqueness statement, inspect the current Mathlib APIs for:

```text
Nat.ModEq
Nat.chineseRemainder
Nat.chineseRemainder_lt_mul
Nat.modEq_zero_iff_dvd
Nat.modEq_iff_exists_eq_add
Nat.ModEq.cancel_left_of_coprime
Nat.ModEq.cancel_right_of_coprime
Finset.prod_insert
Finset.mem_insert
```

Prefer these existing modular/CRT tools over hand-building a modular inverse theory.

The proof may use `Nat.chineseRemainder` to construct the unique child hit by the new `q`-wave.

Do not introduce a new CRT abstraction if Mathlib already provides the needed theorem.

---

# Preferred module

Create:

```text
DkMath/NumberTheory/Primitive/PrimeWorldRefinement.lean
```

Import only the Primitive modules needed for the generic theorem and Mathlib modular arithmetic.

Recommended dependency:

```text
PrimitiveDirection
      ↓
FinitePrimeWorld
      ↓
PeriodicPrimeWorld
      ↓
PrimeWorldRefinement
      ↓
PHZ concrete update examples
```

`Legendre` must not be imported.

---

# Required implementation surface

Names below are preferred, not mandatory.  Report final names if changed.

## 1. Exact semantic update under insertion of one prime

Prove:

```lean
theorem supportDisjointFrom_insert_prime_iff
    {S : Finset ℕ} {q n : ℕ}
    (hq : Nat.Prime q) :
    SupportDisjointFrom (insert q S) n ↔
      SupportDisjointFrom S n ∧ ¬ q ∣ n
```

This theorem should not require `q ∉ S`; semantically it is valid even if insertion is redundant.

This is the core observer-update identity:

```text
new-world survival
  ↔ old-world survival AND avoidance of new q-wave.
```

Keep `FreshPrimeDirection`, `SupportDisjointFrom`, and primality of the candidate seat distinct.

## 2. Modulus update under a genuinely fresh insertion

Prove:

```lean
theorem primeWorldModulus_insert
    {S : Finset ℕ} {q : ℕ}
    (hqS : q ∉ S) :
    primeWorldModulus (insert q S) =
      q * primeWorldModulus S
```

Use `Finset.prod_insert` or the current equivalent.

Do not call this a primorial theorem: `S` is still arbitrary.

## 3. Fresh prime is coprime to the old modulus

For a certified old prime world, prove:

```lean
theorem prime_coprime_primeWorldModulus_of_not_mem
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    Nat.Coprime q (primeWorldModulus S)
```

Either prove this directly from finite-product prime divisibility or reuse
`supportDisjointFrom_iff_coprime_primeWorldModulus` through a thin semantic argument.

This theorem is the arithmetic condition that makes the child update bijective modulo `q`.

## 4. Child-seat coordinate

A small definition is encouraged if it improves readability:

```lean
def primeWorldChild (S : Finset ℕ) (r j : ℕ) : ℕ :=
  r + j * primeWorldModulus S
```

If the raw expression is clearer and no reusable definition is needed, omit this definition.

Do not introduce a structure/class for child seats yet.

## 5. Old support state is inherited by every child

Prove, with the chosen child notation:

```lean
theorem supportDisjointFrom_child_iff
    {S : Finset ℕ} {r j : ℕ} :
    SupportDisjointFrom S (r + j * primeWorldModulus S) ↔
      SupportDisjointFrom S r
```

This should be a thin wrapper over the existing generic periodicity theorem.

Do not duplicate the divisibility proof.

## 6. Refined child survival criterion

Combine sections 1 and 5:

```lean
theorem supportDisjointFrom_insert_prime_child_iff
    {S : Finset ℕ} {q r j : ℕ}
    (hq : Nat.Prime q) :
    SupportDisjointFrom (insert q S)
      (r + j * primeWorldModulus S) ↔
    SupportDisjointFrom S r ∧
      ¬ q ∣ (r + j * primeWorldModulus S)
```

This theorem should be a composition theorem, not a new arithmetic proof.

## 7. Exactly one child is reserved by the new q-wave

This is the main PRIM-042 theorem.

Assume:

```text
KnownPrimeScales S
Nat.Prime q
q ∉ S
r < primeWorldModulus S
```

The residue bound on `r` makes it a canonical old-period representative and supports a clean CRT construction.

Prove an existence-uniqueness theorem equivalent to:

```lean
theorem existsUnique_child_dvd_new_prime
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q r : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hr : r < primeWorldModulus S) :
    ∃! j : ℕ,
      j < q ∧
      q ∣ (r + j * primeWorldModulus S)
```

An equivalent formulation using a bounded subtype or `Fin q` is acceptable if it substantially simplifies uniqueness, but do not force a type-level `Fin q` design if it expands the public API unnecessarily.

Preferred proof strategy:

```text
1. derive q.Coprime M;
2. use Nat.chineseRemainder for residues
     0 mod q
     r mod M;
3. use z < q*M and z ≡ r [MOD M]
   to write z = r + j*M with j < q;
4. derive q ∣ z from z ≡ 0 [MOD q];
5. for uniqueness, if children i and j are both divisible by q,
   cancel the shared r and then cancel M modulo q using coprimality;
6. i,j < q converts modular equality into ordinary equality.
```

Use an equivalent clean route if Mathlib exposes a more direct affine-residue permutation theorem.

Do not replace this with brute-force finite enumeration: the theorem must be generic in `S` and `q`.

## 8. Package the q-1 survivor statement

If the existence-uniqueness theorem is clean, derive a user-facing refinement theorem:

```lean
theorem exists_unique_reserved_child_and_other_children_survive
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q r : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hrPeriod : r < primeWorldModulus S)
    (hrSeat : SupportDisjointFrom S r) :
    ∃ j0,
      j0 < q ∧
      q ∣ (r + j0 * primeWorldModulus S) ∧
      ∀ j, j < q → j ≠ j0 →
        SupportDisjointFrom (insert q S)
          (r + j * primeWorldModulus S)
```

The exact name and tuple shape may be adjusted for proof ergonomics.

This theorem should expose the semantic meaning:

```text
one reserved child + all other bounded children survive.
```

A stronger cardinality theorem saying the survivor index finset has cardinality `q - 1` is welcome only if it follows cheaply from the uniqueness theorem.  Do not let Finset counting dominate this checkpoint.

---

# Small PHZ30 bridge / concrete sanity certificate

Add the previously identified canonical-world bridge, preferably in `PHZ30.lean`:

```lean
theorem primeWorld235_eq_primeScalesUpTo_five :
    primeWorld235 = primeScalesUpTo 5
```

This records that PHZ30 is the concrete `P = 5` canonical bounded prime world, not an unrelated example.

Then add only a small PRIM-042 concrete certificate, for example:

```lean
@[simp] theorem primeWorldModulus_insert_seven_primeWorld235 :
    primeWorldModulus (insert 7 primeWorld235) = 210
```

and, if cheap, one theorem saying each `r ∈ phzResidues30` has exactly one `j < 7` for which

```text
7 ∣ r + 30*j.
```

Do not enumerate the 48 survivors modulo `210`.

Do not introduce a separate `phzResidues210` in this checkpoint.

---

# Public aggregation

Update:

```text
DkMath/NumberTheory/Primitive.lean
```

to import `PrimeWorldRefinement` after `PeriodicPrimeWorld` and before or alongside concrete PHZ observer modules as dependency ordering requires.

If `PHZ30.lean` imports the refinement module only for the small concrete certificate, ensure there is no import cycle.  A clean order is:

```text
PeriodicPrimeWorld
PrimeWorldRefinement
PHZ30
SquareBody
```

If the existing `PHZ30` module remains independent and the concrete 210 certificate belongs better in a tiny sibling module, that is acceptable.  Avoid circular dependencies.

---

# Explicit non-goals

Do not implement:

```text
full PHZ210 residue enumeration
48-survivor explicit finset
recursive sieve over all primes
Legendre provider
proof of LegendreConjecture
prime density / PNT / Mertens
von Mangoldt weighting
RH / CFBRC imports
category theory
new modular inverse framework
new CRT framework
```

Do not claim that a surviving child is prime.  It is only support-disjoint from the enlarged finite prime world.

Do not assume an old seat exists in every interval; that would move toward the unresolved Legendre-equivalent localization provider.

---

# Mathematical invariants to preserve

The conceptual distinction must remain:

```text
old support-disjoint seat
      ≠ prime

fresh prime direction q
      ≠ fresh prime divisor of every child

one q-reserved child
      + q-1 enlarged-world candidate children
```

PRIM-042 is a finite observer update theorem, not a prime-existence theorem.

The dependency graph remains:

```text
finite prime semantics
      ↓
periodic observer
      ↓
prime-direction refinement
      ↓
concrete PHZ examples
      ↓
applications
```

No application dependency may flow back into the Primitive core.

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
3. exact insertion/update equivalence for `SupportDisjointFrom`;
4. modulus-insertion theorem;
5. fresh-prime / old-modulus coprimality theorem;
6. child-seat periodic inheritance theorem;
7. exact existence-uniqueness theorem for the new `q`-reserved child;
8. whether the packaged `q-1` survivor theorem was completed;
9. whether `primeWorld235 = primeScalesUpTo 5` was added;
10. whether the concrete modulus `210` certificate was added;
11. build results;
12. confirmation that no PHZ210 enumeration, Legendre provider, or primality claim was introduced.

Stop after PRIM-042.  The next review will decide whether to proceed to:

```text
PRIM-043  recursive finite-world refinement / observer tower
PRIM-L003 residue-cover bridge specialized to square anchors
Primitive Origin/Depth facade work
```
