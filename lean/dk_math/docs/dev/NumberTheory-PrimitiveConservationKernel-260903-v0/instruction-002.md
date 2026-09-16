# PCK-001 — Half-unit zero-conjugate algebra

Date: 2026-09-04  
Branch: `wip/number-theory-primitive-conservation-kernel-260903-v0`  
Base project: `develop`  
Predecessor: `report-001.md` / PCK-000 reconnaissance

## 0. Mission

PCK-001 formalizes the **prime-free fine-coordinate geometry** discovered in the Primitive Conservation Kernel campaign.

For an arbitrary real anchor `q`, define the half-unit and the zero-conjugate quadratic

$$
u(q):=\frac q2,
$$

$$
Z_q(x):=\left(x-\frac q2\right)^2-\left(\frac q2\right)^2.
$$

The required exact normal form is

$$
Z_q(x)=x(x-q).
$$

Hence the two roots are exactly

$$
x=0\quad\text{or}\quad x=q,
$$

and the midpoint value is

$$
Z_q\left(\frac q2\right)=-\left(\frac q2\right)^2.
$$

This checkpoint contains **no primality, primorial, RH, PHZ, zeta, or finite-source theorem**. Its purpose is to expose the `q`-indexed fine depth coordinate as a thin algebraic API that later NumberTheory and RH consumers may reuse.

PCK-000 classified this layer as `THIN-ADAPTER-NEEDED`.

## 1. Source of truth

Before editing, inspect the current branch versions of at least:

```text
DkMath/CosmicFormula/CoreBeamGap.lean
DkMath/CosmicFormula/CosmicFormulaPythagoras.lean
DkMath/NumberTheory/PrimorialUniverse/UnitCoordinateRefinement.lean
lean/dk_math/docs/dev/NumberTheory-PrimitiveConservationKernel-260903-v0/report-001.md
```

Relevant existing algebra includes:

```text
DkMath.CosmicFormula.Pythagoras.sq_sub_sq_gap_beam
DkMath.CosmicFormula.Pythagoras.sq_diff_of_gap
```

`CoreBeamGap` already owns the generic `Big = Core + Beam + Gap` decomposition. Do not duplicate that theory.

`UnitCoordinateRefinement` already owns positive real units and coordinate refinement. Do not redefine `PositiveUnit`, `HasUnitCoordinate`, or `UnitRefinesBy` in this checkpoint.

## 2. Preferred owner

Preferred new focused module:

```text
DkMath/CosmicFormula/HalfUnitZeroConjugate.lean
```

Use namespace:

```lean
namespace DkMath.CosmicFormula.HalfUnitZeroConjugate
```

This is preferred over placing the definitions under `NumberTheory` because the construction is pure real algebra and does not depend on primes.

If repository reconnaissance finds an already-existing owner with exactly this semantic role, reuse it and explain the change in `report-002.md`. Do not create duplicate public definitions.

## 3. Minimal definitions

Prefer a deliberately small API.

Suggested shapes:

```lean
def halfUnit (q : ℝ) : ℝ := q / 2

def halfUnitDepth (q : ℝ) : ℝ := -(halfUnit q) ^ 2

def zeroConjugateUniverse (q x : ℝ) : ℝ :=
  (x - halfUnit q) ^ 2 - (halfUnit q) ^ 2
```

Do not introduce a structure merely to package these three values.

Do not parameterize over an unnecessarily general field in PCK-001. The project requires the real midpoint/depth coordinate and the existing unit-coordinate layer is real-valued. A later generalization may be considered only if there is a concrete consumer.

## 4. Required theorem surface

### PCK-001-A — exact factorization

Required:

```lean
theorem zeroConjugateUniverse_eq_mul (q x : ℝ) :
    zeroConjugateUniverse q x = x * (x - q) := by
  ...
```

This is the main normal form. Reuse an existing difference-of-squares theorem when it keeps the proof thin; a direct `ring` normalization is acceptable if that is the clearer dependency-minimal proof.

### PCK-001-B — two canonical roots

Required:

```lean
@[simp] theorem zeroConjugateUniverse_zero (q : ℝ) :
    zeroConjugateUniverse q 0 = 0 := by
  ...

@[simp] theorem zeroConjugateUniverse_anchor (q : ℝ) :
    zeroConjugateUniverse q q = 0 := by
  ...
```

These should preferably follow from `zeroConjugateUniverse_eq_mul` rather than re-expanding squares independently.

### PCK-001-C — exact zero-set classification

Required:

```lean
theorem zeroConjugateUniverse_eq_zero_iff (q x : ℝ) :
    zeroConjugateUniverse q x = 0 ↔ x = 0 ∨ x = q := by
  ...
```

The proof should go through the product normal form and `mul_eq_zero`, not through square roots or discriminants.

No assumption `q ≠ 0` is required: when `q = 0`, the disjunction simply has coincident roots.

### PCK-001-D — midpoint and depth

Required:

```lean
@[simp] theorem zeroConjugateUniverse_halfUnit (q : ℝ) :
    zeroConjugateUniverse q (halfUnit q) = halfUnitDepth q := by
  ...
```

Also expose a transparent scalar normal form:

```lean
theorem halfUnitDepth_eq (q : ℝ) :
    halfUnitDepth q = -(q / 2) ^ 2 := by
  rfl
```

If useful and proof-trivial, also add exactly one of the following equivalent forms, but do not create a synonym farm:

```lean
halfUnitDepth q = -(q ^ 2 / 4)
```

or

```lean
4 * halfUnitDepth q = -(q ^ 2)
```

Choose the form that simplifies the future Nat/Real transport expected in PCK-002/PCK-006.

### PCK-001-E — axis symmetry

Required if it remains one or two algebraic lines:

```lean
theorem zeroConjugateUniverse_reflection (q x : ℝ) :
    zeroConjugateUniverse q (q - x) = zeroConjugateUniverse q x := by
  ...
```

This records that the midpoint `q/2` is the reflection center of the two-root world.

Prefer deriving it from the factorized normal form or by `ring`; do not introduce analytic vertex machinery.

## 5. Preferred mirror-world corollary

The project discussion also uses the reflected anchor `-q`, whose roots are `0` and `-q`.

Do **not** define a second universe unless necessary. Prefer reusing `zeroConjugateUniverse (-q)`.

If cheap, add:

```lean
theorem zeroConjugateUniverse_neg_anchor_eq_mul (q x : ℝ) :
    zeroConjugateUniverse (-q) x = x * (x + q) := by
  ...

theorem zeroConjugateUniverse_neg_neg (q x : ℝ) :
    zeroConjugateUniverse (-q) (-x) = zeroConjugateUniverse q x := by
  ...
```

These are optional in PCK-001. Include them only if they fall out immediately from the required normal form and improve the semantic API.

## 6. Semantic interpretation to record in docstrings

Keep the implementation mathematically literal.

The intended interpretation is:

```text
q                 : fine anchor / root separation
0 and q           : the two exact zero solutions
q/2               : their midpoint / half-unit
-(q/2)^2          : midpoint depth
x ↦ q - x         : reflection exchanging the two roots
```

Do not put primality into these declarations.

The importance of this separation is that later checkpoints may specialize `q` to:

```text
an arbitrary natural fine anchor,
a primorial coarse anchor,
a finite analytic cutoff,
```

without changing the underlying algebra.

## 7. Explicit firewalls

PCK-001 must not do any of the following:

1. Do not define or prove `PrimeCompleteUpTo`; PCK-000 found `primeScalesUpTo` already canonical.
2. Do not add `squareBody_mono`; that is PCK-002.
3. Do not add coarse-to-fine prime certification; that is PCK-002/PCK-006.
4. Do not import `DkMath.RH` or any CFBRC/PHZ module.
5. Do not use `Nat.Prime`, primorials, von Mangoldt, zeta, Xi, or zero ordinates in the new module.
6. Do not claim that the depth identifies a prime or a zeta zero.
7. Do not define a generic `PrimitiveKernel` class/structure.
8. Do not create a second unit-coordinate framework parallel to `PrimorialUniverse.PositiveUnit`.
9. No `sorry`, `admit`, `native_decide`, or project-specific axiom.
10. Do not refactor `CoreBeamGap` or `CosmicFormulaPythagoras` merely to shorten this adapter.

## 8. Import policy

Keep the dependency surface thin.

Preferred imports are approximately:

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
```

If an existing Cosmic Formula theorem is genuinely reused, importing its focused owner is acceptable. Do not import the full `DkMath` aggregator.

The report must state the final exact imports and why each is needed.

## 9. Public aggregator policy

Do not automatically modify `DkMath.CosmicFormula.Basic` or `DkMath.lean` in this checkpoint.

First build the focused module independently. If the repository convention clearly requires a focused CosmicFormula aggregator update for new public modules, make only the minimal import addition and build that aggregator too. Explain the choice in the report.

## 10. Verification

Required at minimum:

```text
lake build DkMath.CosmicFormula.HalfUnitZeroConjugate
git diff --check
```

If an aggregator is modified, build it too.

Check the new load-bearing theorem axioms where practical, for example:

```lean
#print axioms DkMath.CosmicFormula.HalfUnitZeroConjugate.zeroConjugateUniverse_eq_mul
#print axioms DkMath.CosmicFormula.HalfUnitZeroConjugate.zeroConjugateUniverse_eq_zero_iff
#print axioms DkMath.CosmicFormula.HalfUnitZeroConjugate.zeroConjugateUniverse_halfUnit
```

Expected footprint must be no stronger than ordinary Mathlib foundations; no project-specific axiom is permitted.

Search the new source for `sorry` / `axiom` before closeout.

## 11. Required report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveConservationKernel-260903-v0/report-002.md
```

Include at least:

- Outcome
- repository branch and starting HEAD
- changed files
- exact owner module and namespace
- definitions added
- theorem surface
- whether existing `sq_sub_sq_gap_beam` / `sq_diff_of_gap` was reused or why direct ring normalization was preferable
- exact imports
- focused build result
- `git diff --check`
- axiom/sorry audit
- optional mirror-world corollaries added or deferred
- explicit statement that no prime/RH theorem was introduced
- authorization for PCK-002 only

## 12. Success criterion

PCK-001 is complete when DkMath has one canonical thin real-algebra API establishing

$$
\left(x-\frac q2\right)^2-\left(\frac q2\right)^2
=x(x-q),
$$

its exact roots `0` and `q`, its midpoint `q/2`, its depth `-(q/2)^2`, and its reflection symmetry.

The next checkpoint is then authorized to connect natural fine anchors by proving `squareBody_mono` and the first coarse-to-fine square certification wrapper.
