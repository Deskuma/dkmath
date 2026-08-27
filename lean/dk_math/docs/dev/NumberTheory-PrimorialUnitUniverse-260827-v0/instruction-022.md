# PUU-L022 — Fresh-Prime Lift-Index Trichotomy / `-a / 0 / +a` Geometry

## Goal

PUU-L021 proved that, for a coprime anchor and a fresh odd prime `q`, the two-sheet square-phase projection fiber is a subcover of the `q - 1`-seat wheel-survivor projection fiber.

PUU-L022 must identify **which raw lift indices** those seats occupy.

For an old fiber representative `b` and old period

```text
M = finitePrimeBasisProduct S,
```

the raw fresh-prime lifts are

```text
primeBasisWheelLift S b j = b + j*M,
0 <= j < q.
```

Under the enlarged coprime-anchor hypothesis, the `q` raw indices must split into three distinguished residue classes modulo `q`:

```text
+a : exactly one phase lift
-a : exactly one phase lift
 0 : exactly one deleted lift
```

with all three indices distinct.  Every remaining index is a surviving wheel lift but not a square-phase lift.  Hence the remaining neutral index set has cardinality `q - 3`.

This is a provider-side local structure theorem.  Do not introduce Legendre or escape-existence vocabulary.

---

## Preferred module

```text
DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhaseLiftIndex.lean
```

Suggested imports:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseSurvivorSubcover
import Mathlib.Tactic
```

Export it from:

```text
DkMath.NumberTheory.PrimorialUniverse
```

Do not import the Legendre facade or consumer modules.

---

## 1. Raw lift-index residue predicates / Finsets

Introduce small index-level vocabulary.  Exact names may be adjusted if a cleaner API emerges.

Recommended predicates:

```lean
def IsFreshPrimePlusLiftIndex
    (S : Finset ℕ) (q a b j : ℕ) : Prop :=
  j < q ∧
    ((primeBasisWheelLift S b j : ZMod q) = (a : ZMod q))

def IsFreshPrimeMinusLiftIndex
    (S : Finset ℕ) (q a b j : ℕ) : Prop :=
  j < q ∧
    ((primeBasisWheelLift S b j : ZMod q) = -(a : ZMod q))

def IsFreshPrimeDeletedLiftIndex
    (S : Finset ℕ) (q b j : ℕ) : Prop :=
  j < q ∧ q ∣ primeBasisWheelLift S b j
```

A Finset API is strongly preferred for later cardinality and partition statements.  For example:

```lean
noncomputable def freshPrimePhaseLiftIndices
    (S : Finset ℕ) (q a b : ℕ) : Finset ℕ := ...

noncomputable def freshPrimeNeutralLiftIndices
    (S : Finset ℕ) (q a b : ℕ) : Finset ℕ := ...
```

A natural definition of the neutral set is:

```text
freshPrimeSurvivingLiftIndices S q b
  \ freshPrimePhaseLiftIndices S q a b
```

Reuse `freshPrimeSurvivingLiftIndices`; do not create a parallel wheel-survivor index theory.

---

## 2. Unique `+a`, `-a`, and `0` indices

Assume throughout the main theorems:

```lean
hS   : IsFinitePrimeBasis S
hSne : S.Nonempty
hq   : Nat.Prime q
hqS  : q ∉ S
hq2  : q ≠ 2
hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S))
hb   : b ∈ squareAnchorPhaseFiber S a
```

Prove existence and uniqueness of the plus and minus lift indices:

```lean
theorem existsUnique_freshPrime_plus_phase_lift_index ... :
    ∃! j : ℕ, IsFreshPrimePlusLiftIndex S q a b j

theorem existsUnique_freshPrime_minus_phase_lift_index ... :
    ∃! j : ℕ, IsFreshPrimeMinusLiftIndex S q a b j
```

For the zero/deleted index, wrap or reuse the existing theorem:

```lean
existsUnique_freshPrime_dvd_lift
```

Do not re-prove the deletion theorem from scratch.

The plus/minus existence should connect to the public L020 phase-lift API where convenient.  Uniqueness should use the fresh-prime coprimality / CRT uniqueness already available in the provider stack, not numerical search.

---

## 3. Pairwise distinct `-a / 0 / +a`

Choose the unique indices `jplus`, `jminus`, `jzero` and prove they are pairwise distinct.

The mathematical reason must be explicit:

- `q ∤ a` follows from `hcop`;
- therefore `+a != 0` and `-a != 0` in `ZMod q`;
- because `q` is odd, `+a != -a`.

A theorem may package this as:

```lean
theorem freshPrime_three_distinguished_lift_indices_pairwise ... :
    jplus ≠ jminus ∧
    jplus ≠ jzero ∧
    jminus ≠ jzero
```

or as a `Set.Pairwise` / `Finset` cardinality statement if that is cleaner.

Do not infer sign distinctness merely from cardinalities.  The local residue reason is the semantic point of this checkpoint.

---

## 4. Phase index set is exactly the two sign indices

Prove that the phase-selected raw lift indices are exactly the plus/minus pair.

Preferred shape:

```lean
theorem freshPrimePhaseLiftIndices_eq_pair ... :
    freshPrimePhaseLiftIndices S q a b = {jplus, jminus}
```

and consequently:

```lean
theorem card_freshPrimePhaseLiftIndices ... :
    (freshPrimePhaseLiftIndices S q a b).card = 2
```

Connect this index set to the seat-level L020 projection fiber.  A desirable theorem is:

```lean
theorem squareAnchorPhaseProjectionFiber_eq_phaseLiftIndexImage ... :
    squareAnchorPhaseProjectionFiber S q a b =
      (freshPrimePhaseLiftIndices S q a b).image
        (primeBasisWheelLift S b)
```

If the exact image theorem causes disproportionate engineering, an elementwise iff connecting seat membership to existence of a phase lift index is acceptable.  The key requirement is that L020's two seats and L022's two indices are demonstrably the same structure.

---

## 5. Deleted index is the unique complement from all wheel-surviving indices

Use the existing wheel index API:

```lean
freshPrimeSurvivingLiftIndices S q b
```

and the unique deletion theorem to record the zero seat.

The phase indices must lie inside the surviving index set:

```lean
freshPrimePhaseLiftIndices S q a b ⊆
  freshPrimeSurvivingLiftIndices S q b
```

The deleted index must not lie in the phase index set.

Do not duplicate L021's seat-level inclusion theorem; this checkpoint is the index-level refinement of that theorem.

---

## 6. Neutral surviving indices and exact `q - 3` count

Define the neutral surviving indices as the wheel survivors not selected by the square phase:

```lean
freshPrimeNeutralLiftIndices S q a b :=
  freshPrimeSurvivingLiftIndices S q b \
    freshPrimePhaseLiftIndices S q a b
```

Prove:

```lean
theorem card_freshPrimeNeutralLiftIndices ... :
    (freshPrimeNeutralLiftIndices S q a b).card = q - 3
```

Use the exact existing counts:

```text
surviving indices = q - 1
phase indices     = 2
```

plus the subset theorem.  Do not hand-count `Finset.range q` unless needed for a local regression.

This theorem is the desired refinement:

```text
q raw lifts
 = 1 deleted zero lift
 + 2 phase lifts (+a, -a)
 + (q - 3) neutral surviving lifts.
```

A packaged cardinality identity is welcome:

```text
q = 1 + 2 + (q - 3)
```

under the odd-prime hypotheses, but it is secondary to the Finset structure.

---

## 7. Explain the `q = 3` and `3 < q` branches structurally

Derive provider-side corollaries:

### Fresh `q = 3`

```lean
freshPrimeNeutralLiftIndices S 3 a b = ∅
```

Thus the two phase indices are **all** surviving indices.  This should explain the L021 theorem

```lean
squareAnchorPhaseProjectionFiber_eq_wheelProjectionFiber_of_q_eq_three
```

from the raw lift-index trichotomy.

It is acceptable to state the index-level equality and cite L021 for the seat-level equality rather than re-prove the latter.

### Fresh `3 < q`

```lean
0 < (freshPrimeNeutralLiftIndices S q a b).card
```

so there is at least one surviving lift which is not a phase lift.  This gives the structural reason for L021's proper subcover result.

Do not turn this into any gap or escape theorem.

---

## 8. Visible regressions

### `6 -> 30`, old representative `b = 1`

Use:

```text
S = {2,3}
M = 6
q = 5
a = 1
b = 1
```

The five raw lifts are:

```text
j : 0   1   2   3   4
x : 1   7  13  19  25
```

Modulo `5`:

```text
j=0 : +a   -> phase seat 1
j=3 : -a   -> phase seat 19
j=4 :  0   -> deleted seat 25
j=1,2      -> neutral survivor seats 7,13
```

Record enough Lean regressions to make this visible.

### Optional second old representative `b = 5`

```text
lifts : 5,11,17,23,29
j=0   : deleted
j=1   : +a
j=4   : -a
j=2,3 : neutral
```

### Optional `q = 3` minimal regression

For `S={2}`, `a=b=1`, `M=2`, the raw lifts are `1,3,5`:

```text
j=0 : +a
j=1 : 0 deleted
j=2 : -a
```

There are no neutral indices.

---

## 9. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-fresh-prime-lift-index-trichotomy-260828.md
```

The report must explicitly state:

1. fresh odd-prime raw lift fiber has `q` indices;
2. exactly one index hits `+a`;
3. exactly one distinct index hits `-a`;
4. exactly one further distinct index hits `0` and is deleted;
5. the remaining `q - 3` indices survive but are not square-phase lifts;
6. `q=3` has no neutral seats, explaining phase/wheel fiber equality;
7. `q>3` has neutral survivors, explaining proper subcover;
8. this is finite provider-side congruence geometry only.

---

## STOP / scope boundary

Do **not** add in PUU-L022:

- Legendre or `escapingSquareOffsets` imports,
- square-shell escape existence,
- wheel-gap or Jacobsthal bounds,
- claims that neutral survivors are composite or prime,
- density / probability arguments,
- PowerSwap,
- GN / CosmicFormula,
- PNT / RH,
- prime-power modulus generalization,
- arbitrary-anchor sign-degeneracy classification beyond what is needed here.

The target is the exact fresh-prime local trichotomy:

```text
-a   0   +a
 |   |    |
phase delete phase
```

inside the `q` raw lift indices.

---

## Outcome A+ criteria

PUU-L022 is A+ when all of the following are present:

1. index-level plus/minus/deleted vocabulary;
2. unique plus index;
3. unique minus index;
4. deleted index reuses existing unique-deletion API;
5. three distinguished indices are pairwise distinct for fresh odd `q` and coprime anchor;
6. phase index set is exactly two indices;
7. phase indices are surviving indices;
8. seat-level L020 phase projection fiber is connected to the index-level pair;
9. neutral surviving set has exact cardinality `q - 3`;
10. `q=3` neutral-empty corollary;
11. `3<q` neutral-nonempty corollary;
12. `6 -> 30` regression records the `+a / neutral / -a / 0` placement;
13. provider-only dependency direction and no escape/Legendre overclaim;
14. report documents the structural meaning and scope boundary.
