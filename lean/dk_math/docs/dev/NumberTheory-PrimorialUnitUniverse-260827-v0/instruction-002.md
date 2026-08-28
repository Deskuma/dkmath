# PUU-L002 — Unit Coordinate Refinement / Prime-to-Composite Same-Point Bridge

## Status

Implement this checkpoint on branch:

```text
wip/number-theory-primorial-unit-universe-260827-v0
```

PUU-L001 is accepted as **Outcome A+**.  Its finite Euclidean layer is now the
fixed ordinary-`Nat.Prime` foundation:

- finite prime basis,
- finite basis product,
- finite reservation escape,
- new prime divisor outside the basis,
- prime-support persistence under multiplication.

PUU-L002 begins the **Unit Universe** layer.  It must not yet implement the
primorial wheel, rational/irrational common-lattice classification, PowerSwap,
or Legendre.

---

# 1. Mathematical target

The same absolute real point can carry different natural-number coordinates in
different positive unit universes.

For a positive real unit `u`, coordinate `n : ℕ`, and absolute point `X : ℝ`,
use the relation

```text
X = n * u.
```

If two units satisfy an integer refinement relation

```text
u₁ = k * u₂,
```

then a point with coarse coordinate `n` has fine coordinate `n*k`:

```text
X = n*u₁ = (n*k)*u₂.
```

The key arithmetic consequence is:

```text
coarse coordinate p is prime
k > 1
--------------------------------
fine coordinate p*k is composite / not prime
```

but the old primitive factor persists:

```text
p ∣ p*k.
```

This checkpoint formalizes that distinction:

> primality is a property of a coordinate in a chosen discrete unit universe,
> not an absolute property of the underlying real point.

Do **not** claim that an ordinary natural prime is composite in `ℕ`.  The two
coordinates belong to different unit-coordinate presentations of the same
absolute point.

---

# 2. Recommended module

Create:

```text
DkMath.NumberTheory.PrimorialUniverse.UnitCoordinateRefinement
```

at:

```text
lean/dk_math/DkMath/NumberTheory/PrimorialUniverse/UnitCoordinateRefinement.lean
```

Import at least:

```lean
DkMath.NumberTheory.PrimorialUniverse.FiniteReservationEscape
```

Add it to:

```text
DkMath.NumberTheory.PrimorialUniverse
```

and keep the top-level `DkMath` facade reachable through the existing facade
chain.

Use `ℝ` for the absolute scale.  Do not introduce a general ordered-field type
unless it makes the implementation strictly simpler.

---

# 3. Positive unit and coordinate relation

A small structure is recommended so that `u = 0` is excluded at the type/API
boundary.

For example:

```lean
structure PositiveUnit where
  val : ℝ
  pos : 0 < val
```

Naming may be adjusted if there is a better collision-free project name.

Define the coordinate relation, e.g.

```lean
def HasUnitCoordinate
    (u : PositiveUnit) (n : ℕ) (X : ℝ) : Prop :=
  X = (n : ℝ) * u.val
```

Required basic API:

```lean
@[simp] theorem hasUnitCoordinate_iff ...
```

and coordinate uniqueness at a fixed positive unit:

```lean
theorem unitCoordinate_unique
    {u : PositiveUnit} {m n : ℕ} {X : ℝ}
    (hm : HasUnitCoordinate u m X)
    (hn : HasUnitCoordinate u n X) :
    m = n
```

This theorem is important: a point may have different coordinates across
*different* units, but not two different natural coordinates inside one fixed
positive-unit universe.

Use positivity/nonzero of `u.val`; do not appeal to choice or quotient
machinery.

---

# 4. Integer unit refinement

Define an explicit relation for a coarse unit being an integer multiple of a
fine unit.

A proposition is sufficient, e.g.

```lean
def UnitRefinesBy
    (fine coarse : PositiveUnit) (k : ℕ) : Prop :=
  coarse.val = (k : ℝ) * fine.val
```

Choose argument order carefully and document it.  The intended reading should
be unambiguous:

```text
coarse = k * fine.
```

Require the main transport theorem:

```lean
theorem unitCoordinate_refine
    {fine coarse : PositiveUnit} {k n : ℕ} {X : ℝ}
    (href : UnitRefinesBy fine coarse k)
    (hX : HasUnitCoordinate coarse n X) :
    HasUnitCoordinate fine (n * k) X
```

Mathematically:

```text
X = n*coarse = n*(k*fine) = (n*k)*fine.
```

Also prove the direct same-point equality form if useful:

```lean
theorem unitRefinement_samePoint
    ... :
    (n : ℝ) * coarse.val = ((n * k : ℕ) : ℝ) * fine.val
```

Do not define division-based unit changes yet.

---

# 5. Prime-to-composite coordinate bridge

Define only the minimum coordinate predicates needed for readable public
statements.  For example:

```lean
def HasPrimeCoordinate (u : PositiveUnit) (X : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ HasUnitCoordinate u p X
```

For the fine side, either use `Nat.Composite` if its Mathlib API is convenient,
or define a local/readable `HasCompositeCoordinate` predicate using explicit
natural factors greater than one.  Prefer a definition whose theorem is easy
to consume later.

The essential theorem is not the wrapper predicate but the explicit coordinate
packet:

```lean
theorem prime_coordinate_becomes_nonprime_under_nontrivial_refinement
    {fine coarse : PositiveUnit} {p k : ℕ} {X : ℝ}
    (href : UnitRefinesBy fine coarse k)
    (hX : HasUnitCoordinate coarse p X)
    (hp : Nat.Prime p)
    (hk : 1 < k) :
    HasUnitCoordinate fine (p * k) X ∧
      ¬ Nat.Prime (p * k)
```

If a clean `Nat.Composite (p*k)` theorem is readily available, add it as a
consumer.  Do not spend the checkpoint fighting a specific `Nat.Composite`
API if `¬ Nat.Prime` plus an explicit nontrivial factorization is cleaner.

Recommended stronger packet:

```lean
theorem prime_coordinate_refinement_packet
    ... :
    HasUnitCoordinate fine (p * k) X ∧
      ¬ Nat.Prime (p * k) ∧
      p ∣ p * k
```

The third field is conceptually important: the old primitive prime is not
removed by refinement; it survives as a factor of the fine coordinate.

---

# 6. Connection to PUU-L001 support persistence

Provide a small bridge showing that the coordinate change does not evade the
finite prime-support theorem from L001.

A suitable theorem shape is:

```lean
theorem refined_coordinate_not_supported_by_old_basis
    {S : Finset ℕ}
    {fine coarse : PositiveUnit}
    {q k : ℕ} {X : ℝ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hk : 1 < k)
    (href : UnitRefinesBy fine coarse k)
    (hX : HasUnitCoordinate coarse q X) :
    HasUnitCoordinate fine (q * k) X ∧
      ¬ PrimeSupportContainedIn S (q * k)
```

The support conclusion should come directly from
`newPrime_mul_not_primeSupportContainedIn`.

This theorem encodes the intended false beam:

> changing to a finer *synchronized integer unit* may turn the coordinate into
> a composite number, but it cannot make a genuinely new prime factor belong
> to the old finite basis.

Do not introduce a factorization structure.

---

# 7. Required concrete regressions

Include at least one exact real-unit example for the motivating phenomenon.

Recommended easiest presentation:

```text
coarse unit = 5
fine unit   = 1
absolute X  = 15
```

Then:

```text
X = 3 * 5 = 15 * 1.
```

Required regression meaning:

```text
coarse coordinate = 3, and 3 is prime
fine coordinate   = 15, and 15 is not prime / is composite
```

A theorem may state this as a conjunction using concrete `PositiveUnit`
values.

If straightforward, add one of the user-motivated variants such as coordinate
`22` or `1463`, but these are optional.  Do not add numerical examples at the
expense of the general theorem.

---

# 8. Semantic boundary / STOP

PUU-L002 stops after **integer synchronized unit refinement**.

Do NOT implement in this checkpoint:

- `u₂ / u₁ ∈ ℚ` common-lattice iff theorems,
- irrational-unit nonintersection,
- arbitrary rational refinements,
- gcd/lcm classification of two unit lattices,
- primorial wheel / reduced residues,
- reflection `r ↔ M-r`,
- wheel lift / unique deletion,
- PowerSwap imports or exponent-fiber bridges,
- GN / cosmic-formula normalization,
- Legendre / square anchors,
- analytic prime counting,
- category theory or generic lattice abstractions.

In particular, do not say that the absolute real point itself is prime or
composite.  Only its **natural coordinate relative to a chosen positive unit**
gets that arithmetic label.

---

# 9. Outcome rubric

## Outcome A+

All of the following are present:

1. positive real unit API;
2. natural coordinate relation;
3. fixed-unit coordinate uniqueness;
4. integer unit-refinement relation;
5. coordinate transport `n ↦ n*k`;
6. general prime-coordinate → nonprime fine-coordinate theorem for `k>1`;
7. persistence `p ∣ p*k` included in a public packet or direct consumer;
8. bridge to L001 `PrimeSupportContainedIn` false beam;
9. concrete `3 @ unit 5 = 15 @ unit 1` regression;
10. no later-stage wheel / PowerSwap / Legendre machinery.

## Outcome A

Core coordinate/refinement and prime-to-nonprime theorem compile, but one of
coordinate uniqueness, L001 support bridge, or regression is deferred for a
small Lean-engineering reason.

## Outcome E

Only if the proposed positive-unit wrapper causes disproportionate coercion
engineering.  In that case keep `u : ℝ` plus explicit `0 < u` hypotheses and
report the minimal blocker.  Do not replace the checkpoint with a broad unit
abstraction.

---

# 10. Report

Write:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-unit-coordinate-refinement-260827.md
```

Record:

- public definitions/theorems,
- the exact interpretation of relative primality,
- the `3 @ 5 = 15 @ 1` regression,
- the L001 support-persistence connection,
- whether `Nat.Composite` was used or avoided and why,
- verification performed,
- explicit confirmation that rational/irrational common-lattice and PowerSwap
  work were not started.
