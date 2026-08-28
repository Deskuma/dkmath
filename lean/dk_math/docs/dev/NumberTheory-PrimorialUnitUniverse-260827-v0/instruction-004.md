# PUU-L004 — Unit Intersection Trichotomy / Commensurability Closure

## 0. Purpose

PUU-L001 fixed finite prime-basis escape.
PUU-L002 fixed unit-relative coordinates and synchronized integer refinement.
PUU-L003 fixed the canonical common-lattice fiber once one positive coprime synchronization

```text
(a : ℝ) * u₁ = (b : ℝ) * u₂
```

is already given.

PUU-L004 must now close the preceding existence question:

> When do two positive unit universes have any positive common lattice point at all?

The target is the exact lattice trichotomy suggested by the mathematical story:

```text
1. complete synchronization
2. partial / periodic synchronization
3. no positive common lattice point
```

Do not introduce primorial wheels, PowerSwap, Legendre, GN, analytic number theory, or generic lattice/category machinery in this checkpoint.

Recommended module:

```text
DkMath.NumberTheory.PrimorialUniverse.UnitIntersectionClassification
```

Suggested file:

```text
DkMath/NumberTheory/PrimorialUniverse/UnitIntersectionClassification.lean
```

Import only the existing PrimorialUniverse layers required from PUU-L001–L003.

---

## 1. Commensurability predicate

Define the finite arithmetic notion by reusing the already canonical coprime synchronization predicate.

```lean
def UnitsCommensurable (u₁ u₂ : PositiveUnit) : Prop :=
  ∃ a b : ℕ, UnitSynchronizesBy u₁ u₂ a b
```

This is intentionally a lattice notion.

Do **not** identify it yet with Mathlib's `Irrational` / rational-real API unless that bridge is completely trivial after the main checkpoint is closed.

The primary language in this checkpoint is:

```text
commensurable     = has a positive integer synchronization
incommensurable   = no such synchronization
```

---

## 2. Positive common-point predicate

Define a positive common lattice point without attaching prime/composite meaning to the absolute real point.

Suggested shape:

```lean
def HasPositiveCommonLatticePoint
    (u₁ u₂ : PositiveUnit) : Prop :=
  ∃ m n : ℕ,
    0 < m ∧
    0 < n ∧
    ∃ X : ℝ,
      HasCommonUnitCoordinates u₁ u₂ m n X
```

Equivalent packaging is acceptable if it keeps later consumers simple.

Prove immediately:

```lean
theorem unitsCommensurable_hasPositiveCommonLatticePoint
    {u₁ u₂ : PositiveUnit} :
    UnitsCommensurable u₁ u₂ →
      HasPositiveCommonLatticePoint u₁ u₂
```

This direction should use the canonical synchronization point from PUU-L003.

---

## 3. Normalize an arbitrary positive common point

This is the main mathematical target of PUU-L004.

Suppose

```text
m*u₁ = n*u₂
m > 0
n > 0
```

but `m,n` need not be coprime.

Let

```text
g := gcd(m,n)
a := m / g
b := n / g
```

and prove that the common point induces a coprime synchronization.

Required content:

```text
0 < a
0 < b
gcd(a,b)=1
a*u₁ = b*u₂
```

The preferred public theorem is conceptually:

```lean
theorem exists_coprimeSynchronization_of_positiveCommonCoordinates
    {u₁ u₂ : PositiveUnit} {m n : ℕ} {X : ℝ}
    (hm : 0 < m)
    (hn : 0 < n)
    (hcommon : HasCommonUnitCoordinates u₁ u₂ m n X) :
    ∃ a b : ℕ,
      UnitSynchronizesBy u₁ u₂ a b
```

It is fine to expose helper lemmas for gcd normalization if useful.

Do not hide the crucial step behind a theorem about prime infinitude or any unrelated number-theory API.

The point of the theorem is exactly:

```text
arbitrary positive intersection
  ↓ divide out gcd
canonical coprime synchronization
```

---

## 4. Main equivalence

Close the existence question exactly.

```lean
theorem hasPositiveCommonLatticePoint_iff_unitsCommensurable
    (u₁ u₂ : PositiveUnit) :
    HasPositiveCommonLatticePoint u₁ u₂
      ↔ UnitsCommensurable u₁ u₂
```

Then expose the negated form:

```lean
theorem noPositiveCommonLatticePoint_iff_not_unitsCommensurable
    (u₁ u₂ : PositiveUnit) :
    (¬ HasPositiveCommonLatticePoint u₁ u₂)
      ↔ ¬ UnitsCommensurable u₁ u₂
```

This is the exact formal version of:

> two positive unit lattices either admit an integer synchronization or have no positive common lattice point at all.

Zero is not the subject here.  The classification concerns **positive** lattice points.

---

## 5. Complete synchronization

Define or theoremize the equal-unit case.

At minimum prove:

```lean
theorem equalUnits_unitsCommensurable
    {u₁ u₂ : PositiveUnit}
    (h : u₁.val = u₂.val) :
    UnitsCommensurable u₁ u₂
```

using the canonical pair `(1,1)`.

Also prove the full same-coordinate overlap:

```lean
theorem equalUnits_allCoordinates_common
    {u₁ u₂ : PositiveUnit}
    (h : u₁.val = u₂.val)
    (n : ℕ) :
    ∃ X : ℝ,
      HasCommonUnitCoordinates u₁ u₂ n n X
```

Conversely, PUU-L003 already contains
`sameCoordinate_synchronization_unit_eq`.
Reuse it rather than re-proving cancellation machinery.

If convenient, expose an iff such as:

```text
u₁.val = u₂.val
↔ positive same-coordinate synchronization exists
```

but do not overbuild an equality theory for `PositiveUnit` structures.

---

## 6. Proper partial synchronization

For commensurable but unequal units, record the intended semantic classification.

A minimal definition is acceptable:

```lean
def UnitsPartiallySynchronize (u₁ u₂ : PositiveUnit) : Prop :=
  UnitsCommensurable u₁ u₂ ∧ u₁.val ≠ u₂.val
```

Then show that a partial synchronization has positive common lattice points, but cannot have a positive common point with the **same** natural coordinate on both sides.

Suggested theorem:

```lean
theorem partiallySynchronized_no_positive_sameCoordinateCommonPoint
    {u₁ u₂ : PositiveUnit}
    (hpartial : UnitsPartiallySynchronize u₁ u₂) :
    ¬ ∃ n : ℕ,
      0 < n ∧
      ∃ X : ℝ,
        HasCommonUnitCoordinates u₁ u₂ n n X
```

Use the existing same-coordinate unit-equality theorem from PUU-L003.

This theorem is enough to distinguish partial synchronization from complete synchronization.

Do **not** claim the common lattice itself is finite.  PUU-L003 proves it contains all multiples `(a*t,b*t)` and is therefore infinite in coordinate pairs.

---

## 7. Trichotomy theorem

Expose one clean classification theorem.

Exact shape is flexible, but it should be equivalent to:

```text
exactly one of:

A. u₁.val = u₂.val
B. UnitsCommensurable u₁ u₂ ∧ u₁.val ≠ u₂.val
C. ¬ UnitsCommensurable u₁ u₂
```

A simple disjunction theorem is sufficient:

```lean
theorem unitIntersection_trichotomy
    (u₁ u₂ : PositiveUnit) :
    u₁.val = u₂.val ∨
      UnitsPartiallySynchronize u₁ u₂ ∨
      ¬ UnitsCommensurable u₁ u₂
```

If exclusivity is easy, also prove pairwise incompatibility or an `ExactlyOne`-style theorem.  It is not required for Outcome A+ if it causes needless API work; the semantic disjointness already follows directly from the definitions.

Interpretation to record in the module docstring/report:

```text
complete synchronization:
  same unit scale; every natural coordinate matches itself

partial synchronization:
  one canonical coprime common-lattice fiber and all its multiples,
  but no positive same-coordinate common point

incommensurable:
  no positive common lattice point
```

---

## 8. Optional ratio bridge — only after the core closes

Do not make this a blocker.

If Mathlib's rational-real coercion API makes it genuinely short, an optional theorem may connect a synchronization

```text
a*u₁ = b*u₂
```

to the real ratio

```text
u₂/u₁ = a/b.
```

But do **not** spend this checkpoint proving a full `Irrational` characterization.

The intended later statement is conceptually:

```text
positive common lattice point exists
  ↔ unit ratio is rational
```

PUU-L004 only needs the integer commensurability form above.

---

## 9. Regression examples

Keep examples tiny.

Recommended examples:

### Complete

```text
u₁ = 1, u₂ = 1
```

show coordinate `3` is common as `(3,3)`.

### Partial

Use the existing PUU-L003 units:

```text
u₁ = 3, u₂ = 2
2*3 = 3*2
```

show:

```text
UnitsCommensurable regressionUnitThree regressionUnitTwo
regressionUnitThree.val ≠ regressionUnitTwo.val
```

and therefore partial synchronization.

Do not invent an irrational numerical regression unless Mathlib already supplies a painless proof.  The abstract incommensurable branch is sufficient for this checkpoint.

---

## 10. Connection to the next layer

The report must explain why this closes the **two-unit lattice foundation** needed before primorial wheels.

After PUU-L004, the branch will have:

```text
PUU-L001
finite prime basis cannot reserve everything

PUU-L002
same absolute point can have prime / nonprime coordinates under unit refinement,
but the old prime factor persists

PUU-L003
one coprime synchronization determines the entire common-lattice fiber

PUU-L004
positive intersection exists iff the units are commensurable,
with complete / partial / no-positive-intersection classification
```

This is enough to move next toward the finite multi-scale synchronization object behind a primorial wheel.

The likely next mathematical object is not another arbitrary real-unit theorem.  It is the finite synchronization period generated by several integer prime scales, ultimately

```text
lcm(2,3,5,...,pₖ) = 2*3*5*...*pₖ
```

for distinct primes.

Do not implement that in PUU-L004.

---

## 11. Outcome

### Outcome A+ — UNIT INTERSECTION TRICHOTOMY COMPLETE

Require:

1. `UnitsCommensurable`.
2. positive common-point predicate.
3. arbitrary positive common pair -> coprime synchronization via gcd normalization.
4. positive common point iff commensurable.
5. no positive common point iff not commensurable.
6. equal units -> complete same-coordinate synchronization.
7. commensurable unequal units -> no positive same-coordinate common point.
8. a clean complete / partial / none trichotomy theorem.
9. semantic boundary preserved: prime/composite remains coordinate-relative.

### Outcome B — NORMALIZATION REMAINDER FOUND

Use only if gcd normalization reveals a genuine missing arithmetic theorem/API that prevents the equivalence from being stated exactly.  Name the missing remainder precisely.

### Outcome C — ENGINEERING BLOCKER

Use only if the mathematics is clear but Lean elaboration / gcd-division API blocks implementation.

---

## 12. STOP boundary

Do not proceed to:

- full Mathlib `Irrational` classification
- arbitrary field/unit abstractions
- three-or-more-unit synchronization
- lcm/primorial products
- reduced residue wheel
- reflection / next-prime lift
- PowerSwap
- GN / CosmicFormula
- Legendre / square anchors
- analytic sieve / PNT / RH

Stop once the two-unit intersection trichotomy is exact.

---

## 13. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-unit-intersection-trichotomy-260827.md
```

Record:

- definitions introduced
- gcd normalization route
- main iff
- complete / partial / no-intersection meanings
- any optional ratio bridge, clearly marked optional
- exact non-goals
- Outcome
