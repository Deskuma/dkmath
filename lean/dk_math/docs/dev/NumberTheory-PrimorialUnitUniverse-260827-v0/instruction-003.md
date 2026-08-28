# PUU-L003 — Coprime Unit Synchronization / Canonical Common-Lattice Fiber

## 0. Context

PUU-L001 fixed finite prime-basis reservation escape.

PUU-L002 fixed unit-relative natural coordinates and synchronized integer refinement:

```text
coarse = k * fine
coordinate n @ coarse
  -> coordinate n*k @ fine
```

It also proved that a prime coordinate may become nonprime under refinement while the original prime factor persists, and connected that persistence to `PrimeSupportContainedIn`.

PUU-L003 now studies **two positive unit universes at once**.

The mathematical target is not yet a full rational/irrational classification.  First fix the exact finite arithmetic core:

```text
a * u₁ = b * u₂
Nat.Coprime a b
0 < a, 0 < b
```

and prove that every common lattice point has coordinates on the single fiber

```text
(m,n) = (a*t, b*t).
```

This is the canonical common-lattice theorem needed later for prime-to-prime bridges and for reading a primorial as a synchronization period of several prime-scale universes.

## 1. New module

Preferred file:

```text
DkMath/NumberTheory/PrimorialUniverse/CommonLattice.lean
```

Import at minimum:

```lean
import DkMath.NumberTheory.PrimorialUniverse.UnitCoordinateRefinement
```

Update:

```text
DkMath/NumberTheory/PrimorialUniverse.lean
```

with the new public import.

Do not add a separate top-level facade beyond the existing one.

## 2. Synchronization relation

Introduce a small exact predicate or structure for a coprime integer synchronization of two positive units.

One acceptable shape is:

```lean
def UnitSynchronizesBy
    (u₁ u₂ : PositiveUnit) (a b : ℕ) : Prop :=
  0 < a ∧
  0 < b ∧
  Nat.Coprime a b ∧
  (a : ℝ) * u₁.val = (b : ℝ) * u₂.val
```

A structure is also acceptable if it improves theorem ergonomics.

Semantic reading:

```text
a coordinates in universe u₁
and
b coordinates in universe u₂
name the same positive absolute point.
```

Do not call the absolute point prime or composite.

## 3. Common-point vocabulary

Introduce minimal common-lattice vocabulary using the existing `HasUnitCoordinate`.

Preferred concept:

```lean
def HasCommonUnitCoordinates
    (u₁ u₂ : PositiveUnit) (m n : ℕ) (X : ℝ) : Prop :=
  HasUnitCoordinate u₁ m X ∧
  HasUnitCoordinate u₂ n X
```

A separate existential `IsCommonUnitLatticePoint` is optional if useful, but avoid a large generic lattice abstraction.

Provide the canonical synchronized point from `UnitSynchronizesBy`:

```text
X₀ = a * u₁ = b * u₂
```

and prove that all positive/natural multiples are common points:

```text
t -> coordinates (a*t, b*t).
```

A theorem at the coordinate level is enough; no set-theoretic lattice object is required.

## 4. Cross-multiplication theorem

This is the first important arithmetic lemma.

If

```text
a*u₁ = b*u₂
m*u₁ = n*u₂
```

with positive units, then prove the natural-number equality

```text
b * m = a * n.
```

Recommended theorem shape:

```lean
theorem commonCoordinates_cross_mul
    {u₁ u₂ : PositiveUnit} {a b m n : ℕ}
    (hsync : (a : ℝ) * u₁.val = (b : ℝ) * u₂.val)
    (hcommon : (m : ℝ) * u₁.val = (n : ℝ) * u₂.val) :
    b * m = a * n
```

Positivity/nonzero of `u₁.val`, `u₂.val` may be used for cancellation.

The theorem may instead consume `UnitSynchronizesBy` and `HasCommonUnitCoordinates` if that gives a cleaner API.

## 5. Coprime divisibility packet

Assume the synchronization coefficients are coprime.

From

```text
b*m = a*n
Nat.Coprime a b
```

prove:

```text
a ∣ m
b ∣ n
```

Recommended public theorem:

```lean
theorem commonCoordinates_divisible_by_syncCoordinates
    ... :
    a ∣ m ∧ b ∣ n
```

Use standard `Nat.Coprime` divisibility lemmas.  Do not reimplement Euclid's lemma manually if Mathlib already supplies it.

## 6. Canonical common-lattice fiber — main theorem

This is the mathematical center of PUU-L003.

For a coprime positive synchronization

```text
a*u₁ = b*u₂
```

and any common coordinate pair `(m,n)`, prove that there exists one natural `t` such that

```text
m = a*t
n = b*t.
```

Preferred theorem shape:

```lean
theorem commonCoordinates_eq_sync_mul
    {u₁ u₂ : PositiveUnit} {a b m n : ℕ}
    (hsync : UnitSynchronizesBy u₁ u₂ a b)
    (hcommon :
      ∃ X : ℝ,
        HasUnitCoordinate u₁ m X ∧
        HasUnitCoordinate u₂ n X) :
    ∃ t : ℕ,
      m = a * t ∧
      n = b * t
```

Equivalent argument order / conjunction order is fine.

Also provide the converse constructor:

```text
for every t,
(a*t, b*t) is a common coordinate pair.
```

Then package an `iff` if it is cheap:

```text
(m,n) is common
iff
∃ t, m=a*t ∧ n=b*t.
```

The `iff` is preferred for Outcome A+ but should not force a brittle abstraction.

## 7. Uniqueness of the fiber parameter

Because `a > 0` and `b > 0`, the parameter `t` should be unique.

Provide one useful theorem such as:

```lean
theorem sync_mul_parameter_unique
    {a b t s : ℕ}
    (ha : 0 < a)
    (h : a * t = a * s) :
    t = s
```

or directly a uniqueness theorem for common-coordinate fiber representations.

Do not create a generic fiber library in this checkpoint.

## 8. Prime-to-prime bridge consumer

This is the first actual "prime pattern connection between universes" consumer.

Let `p` and `q` be **distinct primes** and suppose

```text
p * u₁ = q * u₂.
```

Then `Nat.Coprime p q` is available, so the canonical common-lattice theorem gives:

```text
all common coordinate pairs = (p*t, q*t).
```

Prove that if a common point has prime coordinates in both universes, then necessarily

```text
t = 1,
```

hence the coordinate pair is exactly

```text
(p,q).
```

Preferred theorem shape:

```lean
theorem distinctPrimeSynchronization_unique_primeCoordinatePair
    {u₁ u₂ : PositiveUnit} {p q r s : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpq : p ≠ q)
    (hsync : (p : ℝ) * u₁.val = (q : ℝ) * u₂.val)
    (hr : Nat.Prime r)
    (hs : Nat.Prime s)
    (hcommon :
      ∃ X : ℝ,
        HasUnitCoordinate u₁ r X ∧
        HasUnitCoordinate u₂ s X) :
    r = p ∧ s = q
```

Equivalent theorem decomposition is fine.

Important interpretation:

```text
distinct prime-scale universes may share a prime-to-prime point,
but under the coprime synchronization fiber it is the unique positive
common point whose coordinates are prime in both universes.
```

Do not infer that there is only one common lattice point.  There are infinitely many common points `(p*t,q*t)`; only the **prime-coordinate / prime-coordinate** bridge is unique.

## 9. Same-prime synchronization sanity theorem

If the same positive natural coordinate synchronizes two positive units,

```text
p*u₁ = p*u₂
0 < p
```

then prove

```text
u₁.val = u₂.val.
```

A prime hypothesis is optional; positivity/nonzero of `p` is enough.

This records the full-coincidence edge case needed later:

```text
same prime coordinate + same absolute point
-> same unit scale.
```

Do not yet build a theorem saying the entire lattice sets are equal; equality of unit values is enough.

## 10. Regressions

Add cheap explicit examples if useful.

Preferred examples:

```text
3 * 1 = 2 * (3/2)
```

so the canonical common coordinate pair is `(3,2)`.

Then the next common pair is `(6,4)`, which is not prime-to-prime.

If introducing a positive unit with value `3/2` causes coercion noise, a simpler integer-valued pair is acceptable, e.g.

```text
2 * 3 = 3 * 2 = 6.
```

The general theorems matter more than the regression.

No `native_decide` just for examples.

## 11. Connection to PUU-L001/L002

This checkpoint should preserve the conceptual chain:

```text
L001:
finite old prime basis
  -> new q outside basis

L002:
q @ coarse unit
  -> q*k @ synchronized fine unit
  -> coordinate can become nonprime
  -> factor q persists

L003:
two synchronized units
  -> all common coordinate pairs form one coprime fiber
  -> distinct prime scales have at most one prime-to-prime bridge
```

A direct theorem combining L001 with L003 is not required yet.

## 12. STOP / non-goals

Do **not** proceed to:

- `u₂/u₁ ∈ ℚ` as a Mathlib `Rat` / `Irrational` classification;
- proof that irrational unit ratios have no positive common lattice point;
- generic additive subgroup / lattice / module theory;
- lcm of three or more unit universes;
- primorial product or primorial wheel;
- reduced residues;
- reflection symmetry;
- next-prime lift / deletion / replication;
- PowerSwap;
- GN / CosmicFormula normalization;
- Legendre or square-anchor arguments.

The purpose of L003 is only to make the **two-universe common-lattice fiber exact**.

## 13. Outcome A+

Outcome A+ requires:

1. minimal synchronization vocabulary;
2. common-coordinate vocabulary;
3. canonical synchronized point / multiple constructor;
4. cross-multiplication equality;
5. coprime divisibility packet;
6. exact `∃ t, (m,n)=(a*t,b*t)` common-lattice theorem;
7. converse, preferably an `iff`;
8. uniqueness of `t` or equivalent cancellation consumer;
9. distinct-prime synchronization gives a unique prime-coordinate pair;
10. same-coordinate synchronization collapses to equal unit values;
11. facade import;
12. report documenting the semantic boundary.

## 14. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-common-lattice-fiber-260827.md
```

The report must explicitly distinguish:

```text
unique prime-to-prime common point
```

from

```text
unique common lattice point
```

The second statement is false in the synchronized case and must not be claimed.
