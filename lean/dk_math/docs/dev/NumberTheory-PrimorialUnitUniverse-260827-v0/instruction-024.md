# PUU-L024 — Fresh-Prime Lift-Index Reflection Involution / Neutral Two-Cycle Geometry

## Goal

PUU-L023 proved that the deleted raw-lift index is the affine midpoint of the `+a` and `-a` phase indices.  Promote that midpoint relation to an involutive reflection of the **entire fresh-prime raw lift-index circle**.

The target is provider-side finite congruence geometry only.

For a fresh odd prime `q`, old period `M = finitePrimeBasisProduct S`, old representative `b`, and deleted index `jzero`, define the reflection centered at `jzero` by

```text
rho(j) = 2*jzero - j   in ZMod q.
```

Use this reflection to show that the fresh-prime raw residue map is negated, hence phase indices are exchanged, the deleted index is fixed, surviving indices are preserved, and neutral indices occur in fixed-point-free two-cycles.

Do not introduce Legendre consumers, escape existence, gap/Jacobsthal arguments, PowerSwap, GN/CosmicFormula, PNT, RH, or primality claims about neutral seats.

---

## Preferred module

```text
DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhaseLiftIndexReflection.lean
```

Preferred import:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndexAffine
```

Export through:

```text
DkMath.NumberTheory.PrimorialUniverse
```

Add concise module/public theorem docstrings.

---

## 1. Reflection coordinate

Introduce a small provider-side reflection API.  Representation may be either:

1. directly on `ZMod q`, or
2. as the unique canonical natural representative `< q`.

Prefer the representation that keeps proofs short and reuses existing `ZMod` facts.

Conceptually:

```lean
freshPrimeLiftIndexReflection jzero j = 2 * jzero - j
```

on the `ZMod q` index circle.

Required identities:

```text
rho(jzero) = jzero
rho(rho(j)) = j
```

If a Nat representative API is introduced, also provide the `< q` range theorem and a cast-to-`ZMod q` theorem.

Do not introduce an unnecessarily general affine-geometry framework.

---

## 2. Raw residue negation under reflection

Let

```text
F(j) = b + j*M  (mod q).
```

Assume `jzero` is a deleted index, so `F(jzero)=0`.

Prove the central identity

```text
F(rho(j)) = - F(j)
```

in `ZMod q`.

This should follow from the affine formula from PUU-L023 and the zero-residue equation at `jzero`.

This theorem is the main structural result of L024.

---

## 3. Exchange of the two phase signs

Under the usual fresh odd prime / coprime-anchor assumptions, prove:

```text
plus index  -> reflected index is minus
minus index -> reflected index is plus
```

If using Nat representatives, preserve the `< q` component of the index predicates.

Also connect this with the existing L023 theorem

```text
freshPrime_plus_reflects_to_minus_about_deleted
```

rather than duplicating the midpoint proof.

---

## 4. Deleted center is fixed and uniquely fixed

Prove:

```text
deleted center is fixed by rho
```

and for odd fresh prime:

```text
rho(j) = j  ->  j = jzero   modulo q
```

If both indices are canonical naturals `< q`, strengthen the latter to Nat equality.

Mathematical reason: `2` is nonzero/invertible modulo an odd prime.

Do not claim such uniqueness for `q = 2`.

---

## 5. Survivor preservation

Prove reflection preserves fresh-prime nondeletion:

```text
q ∤ primeBasisWheelLift S b j
  <->
q ∤ primeBasisWheelLift S b (rho j)
```

or the equivalent membership theorem for `freshPrimeSurvivingLiftIndices` when using canonical Nat representatives.

The proof should use the raw-residue negation theorem, not a new counting argument.

---

## 6. Neutral-index preservation

Prove that reflection preserves the neutral set:

```text
j ∈ freshPrimeNeutralLiftIndices S q a b
  ->
rho(j) ∈ freshPrimeNeutralLiftIndices S q a b
```

Prefer an iff if convenient.

Reason:

```text
nonzero residue remains nonzero under negation
not (+a or -a) remains not (+a or -a)
```

Reuse PUU-L022 phase/survivor membership theorems.

---

## 7. Neutral indices form fixed-point-free two-cycles

For every neutral index `j`, obtain a reflected partner `k` with:

```text
k is neutral
k != j
rho(k) = j
```

The exact API may be a theorem about a canonical Nat reflection, or an existence/uniqueness theorem if reflection is represented in `ZMod q`.

Preferred semantic theorem shape:

```text
neutral j -> exists unique reflected neutral partner k != j
```

Also add, if straightforward, a parity corollary:

```text
Even (freshPrimeNeutralLiftIndices S q a b).card
```

This parity corollary is optional if it causes disproportionate Finset/Equiv engineering.  The fixed-point-free involution / two-cycle theorem is the required result.

Do not replace the structural pairing proof with only the already-known arithmetic fact that `q - 3` is even.

---

## 8. `q = 3` and `q > 3` interpretation

Reuse existing PUU-L022 results rather than reprove cardinalities.

Record concise corollaries/remarks:

```text
q = 3:
  no neutral orbit exists

3 < q:
  at least one neutral two-cycle exists
```

For the second statement, combine neutral nonemptiness with the new reflection partner theorem.

---

## 9. Visible `6 -> 30` regression

Use:

```text
S = {2,3}
M = 6
q = 5
a = b = 1
jzero = 4
```

Verify the reflection pattern modulo `5`:

```text
rho(0) = 3
rho(3) = 0
rho(1) = 2
rho(2) = 1
rho(4) = 4
```

and connect it to the existing classification:

```text
phase   : 0 <-> 3
neutral : 1 <-> 2
deleted : 4 fixed
```

Prefer a theorem using the public reflection API, not merely `norm_num` on an unrelated expression.

---

## A+ rubric

L024 is Outcome A+ if all of the following are present:

1. fresh-prime index-circle reflection API;
2. reflection involutive and deleted center fixed;
3. raw lift residue is negated under reflection;
4. `+a` and `-a` phase indices are exchanged;
5. deleted center is the unique fixed point for odd fresh prime;
6. survivor status is reflection-invariant;
7. neutral status is reflection-invariant;
8. every neutral index has a distinct reflected neutral partner and the reflection returns it;
9. `6 -> 30` regression shows `0<->3`, `1<->2`, `4` fixed;
10. facade export, docstrings, and implementation report.

---

## STOP / boundary

Do **not** claim:

- a neutral seat is prime or composite;
- a neutral pair gives a square-shell escape;
- a wheel-gap or Jacobsthal bound;
- Legendre propagation;
- arbitrary prime-power modulus classification;
- PowerSwap / GN / CosmicFormula conclusions;
- PNT / RH consequences.

This checkpoint should end with a finite local statement:

```text
fresh-prime raw lift circle
  = one fixed deleted center
    + one reflected phase pair
    + reflected neutral pairs.
```

The likely next frontier after L024 is to normalize the index circle at the deleted center and express the two phase positions explicitly as

```text
jplus  = jzero + a * M^{-1}
jminus = jzero - a * M^{-1}
```

in `ZMod q`, but do not implement that inverse-coordinate formula in L024 unless it falls out essentially for free.

---

## Report

Write:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
primorial-unit-universe-fresh-prime-lift-index-reflection-involution-260828.md
```

Report the exact theorem strengths, the role of oddness/coprimality, the neutral two-cycle interpretation, the `6 -> 30` regression, and the STOP boundary.
