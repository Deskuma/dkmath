# PUU-L008 — Global Wheel Replication / Cardinality Recurrence

## Goal

Globalize PUU-L007's per-old-survivor unique-deletion theorem.

Let

```text
M := finitePrimeBasisProduct S
```

with `S.Nonempty`, `IsFinitePrimeBasis S`, and let `q` be a fresh prime
`q ∉ S`.  Every survivor in the enlarged wheel for `insert q S` must be
represented uniquely as

```text
primeBasisWheelLift S r j = r + j*M
```

with

```text
r ∈ primeBasisWheelSurvivors S
j < q
q ∤ primeBasisWheelLift S r j.
```

Conversely every such surviving lift belongs to the enlarged wheel.

The target global recurrence is

```text
(primeBasisWheelSurvivors (insert q S)).card
  = (q - 1) * (primeBasisWheelSurvivors S).card
```

for nonempty finite prime bases.

This is the exact wheel-replication law:

```text
old survivor fiber
  -> q lifts
  -> exactly one fresh-prime deletion
  -> q-1 surviving children

all old fibers
  -> disjoint union
  -> global enlarged wheel
```

## Important edge condition

Do **not** state the recurrence for arbitrary `S` without handling the empty
basis separately.

With the current PUU-L006 survivor convention

```text
0 < r < finitePrimeBasisProduct S
```

we have `finitePrimeBasisProduct ∅ = 1`, hence the empty-basis wheel has no old
survivor seats, while the `{q}` wheel contains `1, ..., q-1`.  Therefore the
simple recurrence from the old survivor set requires `S.Nonempty` (or an
explicit separate base case).

For this checkpoint, prefer the clean assumption

```lean
hSne : S.Nonempty
```

rather than changing the established survivor definition.

## Suggested module

```text
DkMath/NumberTheory/PrimorialUniverse/WheelReplication.lean
```

Import at least:

```lean
import DkMath.NumberTheory.PrimorialUniverse.FreshPrimeLift
```

and export it through

```text
DkMath.NumberTheory.PrimorialUniverse
```

## Required mathematics

### 1. Old period is genuinely larger than one

From `S.Nonempty` and `IsFinitePrimeBasis S`, prove a usable lemma such as

```lean
theorem one_lt_finitePrimeBasisProduct_of_nonempty
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty) :
    1 < finitePrimeBasisProduct S
```

or an equivalent API.

This is needed so an enlarged survivor cannot have remainder `0 mod M` while
remaining coprime to the old product.

### 2. Canonical quotient/remainder decomposition

For any enlarged-wheel seat `x`, define conceptually

```text
r := x % M
j := x / M
```

and prove

```text
x = r + j*M
r < M
j < q
```

using

```text
x < q*M.
```

For an enlarged survivor, prove additionally

```text
0 < r
¬ ReservedByPrimeBasis S r
```

so that

```text
IsPrimeBasisWheelSurvivor S r.
```

The preferred semantic theorem is of the shape

```lean
theorem enlargedWheelSurvivor_iff_exists_oldSurvivorLift
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S)
    {x : ℕ} :
    IsPrimeBasisWheelSurvivor (insert q S) x ↔
      ∃ r j : ℕ,
        IsPrimeBasisWheelSurvivor S r ∧
        j < q ∧
        x = primeBasisWheelLift S r j ∧
        ¬ q ∣ x
```

Equivalent theorem shapes are acceptable if they expose the same exact
information and are convenient for later Finset/cardinality use.

### 3. Uniqueness / fiber disjointness

Prove that the lift representation is unique inside

```text
0 < r < M,  j < q.
```

For example:

```lean
theorem primeBasisWheelLift_injective_on_period
    ... :
    primeBasisWheelLift S r j = primeBasisWheelLift S r' j' ->
      r = r' ∧ j = j'
```

under the appropriate old-period bounds.

Quotient/remainder uniqueness is the natural route.

This theorem is important: global cardinality must not count the same enlarged
seat through two old survivor fibers.

### 4. Local surviving-index set

Package the surviving indices for one old survivor, for example

```lean
noncomputable def freshPrimeSurvivingLiftIndices
    (S : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  (Finset.range q).filter
    (fun j => ¬ q ∣ primeBasisWheelLift S r j)
```

or an equivalent structure.

Using PUU-L007's

```text
existsUnique_freshPrime_dvd_lift
```

prove the local cardinality

```text
card = q - 1.
```

Do not reprove modular unique deletion from scratch if the L007 theorem can be
consumed directly.

### 5. Global decomposition / bijection

Build an exact correspondence between

```text
Σ r ∈ primeBasisWheelSurvivors S,
  freshPrimeSurvivingLiftIndices S q r
```

(or an equivalent Finset product/filter representation)

and

```text
primeBasisWheelSurvivors (insert q S).
```

The important facts are:

```text
soundness     : every surviving lift is an enlarged survivor
completeness  : every enlarged survivor comes from an old survivor lift
injectivity   : two different `(r,j)` pairs cannot name the same seat
```

### 6. Main cardinality recurrence

Conclude an exact theorem such as

```lean
theorem card_primeBasisWheelSurvivors_insert_fresh
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S) :
    (primeBasisWheelSurvivors (insert q S)).card =
      (q - 1) * (primeBasisWheelSurvivors S).card
```

The multiplication order may differ if Lean simplification prefers it.

## Regressions

Record at least the visible wheel growth

```text
{2,3}:       card = 2
insert 5:    card = 8 = (5-1)*2
```

If convenient, also record

```text
{2,3,5}:     card = 8
insert 7:    card = 48 = (7-1)*8
```

The regression may use `decide`, `norm_num`, or the general recurrence theorem.
Prefer demonstrating the general recurrence when convenient.

## Semantic interpretation

After this checkpoint the exact finite theorem should read:

```text
fresh prime q
  does not redesign the old wheel arbitrarily;
  it replicates every old survivor q times
  and deletes exactly one child from each fiber.
```

Hence

```text
R_{S ∪ {q}}
  = surviving lifts of R_S
```

and

```text
|R_{S ∪ {q}}| = (q-1)|R_S|.
```

This is the first global self-replication theorem of the primorial reservation
sheet.

## Boundary

Stop after the exact global decomposition and cardinality recurrence.

Do not yet add:

```text
Euler phi identification as the main proof route
closed-form product ∏(p-1)
wheel-gap sequence transport
nested-wheel projection chains
square-anchor orbit
Legendre consumer
PowerSwap
GN / CosmicFormula
PNT / RH / analytic sieve
```

An optional compatibility corollary with `Nat.totient` is acceptable only if
it is trivial from existing Mathlib API and does not replace the structural
lift/deletion proof.

The point of PUU-L008 is to derive the cardinal recurrence from the PUU
reservation-sheet generation mechanism, not to import the result from Euler's
totient formula.

## Report

Create a report under the same dev directory describing:

```text
- the exact decomposition theorem
- the empty-basis edge case and chosen boundary
- the local q-1 theorem
- the global bijection / disjointness mechanism
- the final cardinal recurrence
- 6 -> 30 (and optionally 30 -> 210) regression
- explicit statement that survivor != prime
```

Stop at PUU-L008.