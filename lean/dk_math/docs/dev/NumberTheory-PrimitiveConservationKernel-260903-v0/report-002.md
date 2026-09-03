# PCK-001 — Half-unit zero-conjugate algebra report

Date: 2026-09-04  
Branch: wip/number-theory-primitive-conservation-kernel-260903-v0  
Base project: develop  
Predecessor: report-001.md / PCK-000

## 1. Outcome

PCK-001 is complete. The repository now has one focused, prime-free real
algebra owner for the half-unit zero-conjugate quadratic:

    DkMath.CosmicFormula.HalfUnitZeroConjugate

It establishes the exact factorization, the two endpoint roots, the midpoint
depth, and reflection symmetry. No NumberTheory, primality, primorial, RH,
PHZ, zeta, Xi, or finite-source theorem was introduced.

## 2. Repository state and changed files

- Starting HEAD:
  56140194843b73868cb29d105273daafa15bc93d
  (docs(PCK): add PCK-001 half-unit zero-conjugate algebra instructions).
- Starting worktree status was clean.
- Added:
  DkMath/CosmicFormula/HalfUnitZeroConjugate.lean
  docs/dev/NumberTheory-PrimitiveConservationKernel-260903-v0/report-002.md
- No existing Lean source or public aggregator was modified.
- DkMath/CosmicFormula/Basic.lean, DkMath/CosmicFormula.lean, and
  DkMath.lean were intentionally left unchanged.

## 3. Owner and dependency surface

Owner module:

    DkMath/CosmicFormula/HalfUnitZeroConjugate.lean

Namespace:

    DkMath.CosmicFormula.HalfUnitZeroConjugate

Exact imports:

    import Mathlib.Data.Real.Basic
    import Mathlib.Tactic

Mathlib.Data.Real.Basic supplies the real-valued domain and its arithmetic
operations. Mathlib.Tactic supplies ring normalization. The existing
CosmicFormula.Pythagoras owner was not imported because the required identity
is most clearly and dependency-minimally proved by direct real ring
normalization. CoreBeamGap was not refactored or duplicated.

The definitions are in a noncomputable section because real division is
noncomputable in the current environment. This does not add a project-specific
axiom or change the mathematical API.

## 4. Definitions added

    def halfUnit (q : ℝ) : ℝ := q / 2

    def halfUnitDepth (q : ℝ) : ℝ :=
      -(halfUnit q) ^ 2

    def zeroConjugateUniverse (q x : ℝ) : ℝ :=
      (x - halfUnit q) ^ 2 - (halfUnit q) ^ 2

The meanings are literal:

| expression | meaning |
|---|---|
| q | fine anchor and root separation |
| 0 and q | exact zero-conjugate endpoints |
| halfUnit q | midpoint q/2 |
| halfUnitDepth q | midpoint value -(q/2)^2 |
| q - x | reflection about q/2 |

No structure was introduced.

## 5. Theorem surface

    theorem zeroConjugateUniverse_eq_mul (q x : ℝ) :
        zeroConjugateUniverse q x = x * (x - q)

This is the required exact normal form.

    @[simp] theorem zeroConjugateUniverse_zero (q : ℝ) :
        zeroConjugateUniverse q 0 = 0

    @[simp] theorem zeroConjugateUniverse_anchor (q : ℝ) :
        zeroConjugateUniverse q q = 0

These endpoint theorems are derived from the factorized normal form.

    theorem zeroConjugateUniverse_eq_zero_iff (q x : ℝ) :
        zeroConjugateUniverse q x = 0 ↔ x = 0 ∨ x = q

This uses the real product zero theorem and requires no q ≠ 0 assumption.
When q = 0, the two alternatives correctly coincide.

    @[simp] theorem zeroConjugateUniverse_halfUnit (q : ℝ) :
        zeroConjugateUniverse q (halfUnit q) = halfUnitDepth q

    theorem halfUnitDepth_eq (q : ℝ) :
        halfUnitDepth q = -(q / 2) ^ 2

    theorem zeroConjugateUniverse_reflection (q x : ℝ) :
        zeroConjugateUniverse q (q - x) = zeroConjugateUniverse q x

The midpoint and reflection results are algebraic only; no vertex or analytic
machinery is introduced.

## 6. Existing difference-of-squares API

PCK-000 identified sq_sub_sq_gap_beam and sq_diff_of_gap as nearby identities.
PCK-001 does not reuse either theorem. Direct ring normalization is preferable
here because:

- the new owner has only the two required Mathlib imports;
- the target already lives entirely in ℝ;
- importing the Pythagoras module would add unrelated Cosmic Formula
  dependencies;
- the proof keeps the exact half-unit substitution visible and local.

This is an adapter, not a duplicate of the existing Core + Beam + Gap theory.

## 7. Optional mirror-world corollaries

The optional theorems for the reflected anchor -q were deferred. The existing
universe can be reused directly as zeroConjugateUniverse (-q), so adding a
second named universe or a synonym family is not necessary for PCK-001.

## 8. Verification

Focused build:

    lake build DkMath.CosmicFormula.HalfUnitZeroConjugate

Result:

    Build completed successfully (2997 jobs).

The build emitted only the environment profile permission message before
running Lean and no source warning or error.

Difference check:

    git diff --check

Result: successful.

Forbidden-construct audit on the new source:

    rg -n -i "sorry|admit|native_decide|^axiom|Nat.Prime|DkMath.RH|primorial|zeta|Xi|von Mangoldt|zero ordinate" DkMath/CosmicFormula/HalfUnitZeroConjugate.lean

Result: no matches.

Axiom checks:

    #print axioms DkMath.CosmicFormula.HalfUnitZeroConjugate.zeroConjugateUniverse_eq_mul
    #print axioms DkMath.CosmicFormula.HalfUnitZeroConjugate.zeroConjugateUniverse_eq_zero_iff
    #print axioms DkMath.CosmicFormula.HalfUnitZeroConjugate.zeroConjugateUniverse_halfUnit

All three report only:

    propext, Classical.choice, Quot.sound

These are ordinary Lean/Mathlib foundations. No project-specific axiom is
present.

## 9. Next authorization

Authorize exactly one next checkpoint:

> PCK-002 — implement and verify squareBody_mono and the first thin
> coarse-to-fine square certification wrapper.

PCK-002 may consume this real algebra owner if useful, but PCK-001 does not
authorize RH integration, a generic PrimitiveKernel abstraction, or changes to
the prime-support and wheel APIs.
