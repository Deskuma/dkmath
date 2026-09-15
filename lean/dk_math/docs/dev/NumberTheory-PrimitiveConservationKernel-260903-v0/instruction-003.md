# PCK-002 — Fine square-anchor monotonicity implementation instructions

Date: 2026-09-04  
Branch: `wip/number-theory-primitive-conservation-kernel-260903-v0`  
Predecessor: `report-002.md` / PCK-001

## 0. Authorization

This checkpoint is intentionally narrow.

Implement and verify the first missing arithmetic adapter identified by PCK-000:

```lean
squareBody_mono
```

Do not proceed to the coarse-to-fine primality wrapper, prime-expansion operator, primorial bridge, RH/PHZ bridge, or generic `PrimitiveKernel` abstraction in this checkpoint.

PCK-002 is complete when the monotonicity theorem is available in the canonical square-Body owner and the focused verification/report are green.

## 1. Source of truth

Work on the current branch and inspect the current file before editing:

```text
DkMath/NumberTheory/Primitive/SquareBody.lean
```

Reuse the existing definitions and theorems there, in particular:

```lean
def squareBody (P : ℕ) : ℕ := P ^ 2 + 2 * P

theorem squareBody_add_one_eq (P : ℕ) :
    squareBody P + 1 = (P + 1) ^ 2
```

Do not redefine `squareBody`.

## 2. Required theorem

Add one load-bearing theorem in namespace:

```text
DkMath.NumberTheory.Primitive
```

Preferred statement:

```lean
/-- The natural square Body is monotone in its anchor. -/
theorem squareBody_mono {q P : ℕ} (h : q ≤ P) :
    squareBody q ≤ squareBody P := by
  ...
```

Equivalent argument order is acceptable only if it materially matches existing local style better.

The theorem should be proved from the current arithmetic definition or a minimal existing Nat monotonicity theorem. Do not introduce a new definition or auxiliary structure merely for this proof.

## 3. Mathematical meaning

The theorem fixes the fine-anchor nesting fact

$$
q\le P
\Longrightarrow
q(q+2)\le P(P+2).
$$

Using the existing endpoint identity, this is the arithmetic core behind the later inclusion

$$
(q+1)^2-1
\le
(P+1)^2-1.
$$

PCK-002 itself stops at the monotonicity theorem. It does not yet package the later primality-certification consequence.

## 4. Owner policy

Preferred owner:

```text
DkMath/NumberTheory/Primitive/SquareBody.lean
```

Reason: `squareBody_mono` is a basic property of the existing canonical `squareBody` definition and is expected to be reused by later fine/coarse wrappers.

Do not create `SquareBodyFineAnchor.lean` unless current source inspection reveals a concrete ownership or dependency problem. If ownership is changed, record the exact reason in the report.

Do not alter public aggregators for one theorem added to an already-public module.

## 5. Optional theorem policy

Do not add speculative companion APIs.

In particular, do not add any of the following unless the proof of `squareBody_mono` genuinely cannot be expressed cleanly without one tiny local helper:

```text
squareBoundary_mono
prime_of_coarseAnchor_...
PrimeCompleteUpTo
fineAnchor...
coarseAnchor...
squarePrimeExpansion
```

If a helper is absolutely necessary, keep it private/local when possible and explain it in the report.

## 6. Firewalls

PCK-002 must not:

1. modify `HalfUnitZeroConjugate.lean`;
2. import the half-unit module into NumberTheory merely for this theorem;
3. add any `Nat.Prime` theorem beyond what already exists in `SquareBody.lean`;
4. add primorial/wheel logic;
5. add a coarse-to-fine primality wrapper yet;
6. add RH, zeta, Xi, PHZ, CFBRC, or analytic dependencies;
7. add `sorry`, `admit`, `native_decide`, or a new axiom;
8. refactor existing SquareBody theorem statements.

## 7. Regression expectations

The theorem should immediately support numeral specializations such as

$$
6\le30
\Longrightarrow
\operatorname{squareBody}(6)
\le
\operatorname{squareBody}(30),
$$

but no dedicated numeric theorem is required in PCK-002.

Do not add a `30 → 960` regression yet; that belongs to the later canonical regression checkpoint.

## 8. Verification

Run at least:

```text
lake build DkMath.NumberTheory.Primitive.SquareBody
git diff --check
```

Run an axiom check for the new theorem where practical:

```lean
#print axioms DkMath.NumberTheory.Primitive.squareBody_mono
```

Expected footprint: ordinary Lean/Mathlib foundations only, with no project-specific axiom.

Audit the modified source for newly introduced forbidden constructs.

## 9. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimitiveConservationKernel-260903-v0/report-003.md
```

Record:

- Outcome
- branch and starting HEAD
- changed files
- exact final theorem statement
- proof route / exact reused theorem(s), if any
- focused build result
- `git diff --check`
- axiom/sorry audit
- whether any helper was added
- next authorization

## 10. Next authorization

If PCK-002 is green, authorize only the next README checkpoint:

> PCK-003 — first thin coarse-to-fine square certification adapter using `squareBody_mono` and the already-existing `primeScalesUpTo` / SquareBody certification API.

Do not implement PCK-003 in this checkpoint.
