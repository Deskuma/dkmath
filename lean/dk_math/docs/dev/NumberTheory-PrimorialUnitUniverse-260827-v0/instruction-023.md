# PUU-L023 — Fresh-Prime Lift-Index Affine Midpoint / Reflection Geometry

## Goal

Refine PUU-L022 from a three-way classification of distinguished raw lift indices to the exact affine relation among them.

Let

- `M := finitePrimeBasisProduct S`,
- `q` be a fresh odd prime,
- `a` be coprime to the enlarged product,
- `b ∈ squareAnchorPhaseFiber S a`,
- `jplus` be the unique `+a` lift index,
- `jminus` be the unique `-a` lift index,
- `jzero` be the unique deleted (`0 mod q`) lift index.

PUU-L022 gives existence, uniqueness, and pairwise distinctness.  PUU-L023 should prove that `jzero` is the affine midpoint of the two phase indices on the `ZMod q` index circle.

Conceptually:

```text
raw lift residue map
  j |-> b + j*M  in ZMod q

jplus  |-> +a
jzero  |->  0
jminus |-> -a
```

Since `q` is fresh, `M` is nonzero / invertible modulo `q`.  Therefore

```text
jplus - jzero = -(jminus - jzero)  in ZMod q
```

and equivalently

```text
jplus + jminus = 2 * jzero  in ZMod q.
```

This is provider-side finite affine geometry only.

## Preferred module

```text
DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhaseLiftIndexAffine.lean
```

Prefer importing only:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndex
import Mathlib.Tactic
```

Export the module from `DkMath.NumberTheory.PrimorialUniverse` and update its module docstring.

## Required API

### 1. Raw lift map is affine modulo the fresh prime

Add a small public theorem exposing the residue map, preferably in `ZMod q`:

```lean
theorem primeBasisWheelLift_cast_freshPrime
    {S : Finset ℕ} {q b j : ℕ} :
    ((primeBasisWheelLift S b j : ℕ) : ZMod q) =
      (b : ZMod q) + (j : ZMod q) * (finitePrimeBasisProduct S : ZMod q)
```

An equivalent orientation is acceptable.

Also expose that the old period is nonzero modulo a fresh prime:

```lean
theorem finitePrimeBasisProduct_cast_ne_zero_of_freshPrime
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    (finitePrimeBasisProduct S : ZMod q) ≠ 0
```

Do not introduce a new inverse API unless Lean genuinely benefits from it.

### 2. Offsets from the deleted index are opposite

For witnesses satisfying the PUU-L022 predicates, prove:

```lean
theorem freshPrime_phase_offsets_opposite
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b jplus jminus jzero : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hplus : IsFreshPrimePlusLiftIndex S q a b jplus)
    (hminus : IsFreshPrimeMinusLiftIndex S q a b jminus)
    (hzero : IsFreshPrimeDeletedLiftIndex S q b jzero) :
    ((jplus : ZMod q) - (jzero : ZMod q)) =
      -((jminus : ZMod q) - (jzero : ZMod q))
```

The proof should come from the three raw-lift residue equations and cancellation of the nonzero coefficient `M mod q`.

Do not prove this by finite case enumeration.

### 3. Exact midpoint theorem

Derive the cleaner symmetric form:

```lean
theorem freshPrime_deleted_index_is_phase_midpoint
    ... :
    (jplus : ZMod q) + (jminus : ZMod q) =
      2 * (jzero : ZMod q)
```

Equivalent multiplication orientation is fine.

This is the main semantic theorem of the checkpoint.

### 4. Midpoint uniqueness for odd fresh prime

Because `q` is odd, `2 : ZMod q` is nonzero.  Show that the deleted index is the unique midpoint of the phase pair, at least at the `ZMod q` level:

```lean
theorem freshPrime_phase_midpoint_unique
    ...
    {z : ZMod q}
    (hz : (jplus : ZMod q) + (jminus : ZMod q) = 2 * z) :
    z = (jzero : ZMod q)
```

If a more convenient theorem shape is needed, an iff is acceptable:

```text
2*z = jplus+jminus <-> z=jzero
```

under the same hypotheses.

### 5. Reflection interpretation

At minimum prove the equivalent reflection identity:

```lean
theorem freshPrime_plus_reflects_to_minus_about_deleted
    ... :
    (jminus : ZMod q) =
      2 * (jzero : ZMod q) - (jplus : ZMod q)
```

and the symmetric converse for `jplus` if useful.

Do **not** yet build a full `Fin q` involution or neutral-pair orbit decomposition unless it falls out trivially.  That belongs naturally to a later checkpoint.

### 6. Regression: `6 -> 30`

Use the existing concrete data:

```text
S = {2,3}
M = 6
q = 5
a = b = 1
jplus  = 0
jminus = 3
jzero  = 4
```

Verify in `ZMod 5`:

```text
0 - 4 = -(3 - 4)
0 + 3 = 2*4
3 = 2*4 - 0
```

The regression should exercise the public affine theorem(s), not be only an isolated `decide` calculation.

## Semantic interpretation to record in the report

PUU-L022 gave the count decomposition

```text
q raw indices
 = 1 deleted
 + 2 phase
 + (q-3) neutral survivors.
```

PUU-L023 should add the stronger geometric statement:

```text
phase pair is centrally symmetric about the deleted index
on the fresh-prime index circle.
```

Equivalently, the raw affine map sends the index-circle triple

```text
jminus, jzero, jplus
```

to the residue triple

```text
-a, 0, +a.
```

The midpoint relation is independent of the absolute old representative `b`; `b` translates the three raw residue equations together and disappears after subtraction.

This checkpoint should make clear that the `q = 3` coincidence from PUU-L021/L022 is not merely cardinality arithmetic.  At `q = 3`, the centrally symmetric phase pair plus its center exhausts the entire three-point index circle.  For `q > 3`, additional neutral points remain.

## STOP / do not add

- no full neutral reflection-orbit pairing yet;
- no claim that neutral seats are prime or composite;
- no Legendre / `escapingSquareOffsets` / escape provider;
- no Jacobsthal or wheel-gap theorem;
- no PowerSwap;
- no GN / CosmicFormula;
- no PNT / RH;
- no arbitrary-anchor classification;
- no prime-power modulus generalization.

## Expected outcome

```text
Outcome A+ — FRESH-PRIME INDEX MIDPOINT / REFLECTION GEOMETRY COMPLETE
```

if the affine opposite-offset law, midpoint theorem, and midpoint uniqueness are all proved provider-side.

## Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-fresh-prime-lift-index-affine-midpoint-260828.md
```

The report should distinguish:

1. L022 count/trichotomy facts;
2. new affine residue-map fact;
3. midpoint/reflection theorem;
4. why `q = 3` exhausts the circle and `q > 3` leaves neutral points;
5. remaining boundary: no escape/primality conclusion.
