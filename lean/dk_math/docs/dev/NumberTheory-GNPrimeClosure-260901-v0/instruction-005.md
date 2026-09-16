# Codex Instruction — GNPC-005 Degree-3 GN Quadratic Form / Centered-Square Characterization

Branch: `wip/number-theory-gn-prime-closure-260901-v0`

Project: DkMath NumberTheory GN Prime Closure

Start from current GNPC-004 implementation commit:

```text
4541e2d6ae90ac242e6266c7d03db1d15f7cda23
```

Read first:

```text
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/README.md
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-004.md
lean/dk_math/DkMath/NumberTheory/GNPrimeTargetResidue.lean
lean/dk_math/DkMath/NumberTheory/TraceOneQuadratic.lean
lean/dk_math/DkMath/FLT/ThreeTraceOneBridge.lean
lean/dk_math/DkMath/FLT/GEisensteinBridge.lean
```

---

# 0. Motivation and orientation

GNPC-001–004 established the finite prime-target representation constraints.
GNPC-005 records the special geometry of degree `d = 3`.

Be careful about argument orientation.

The canonical cosmic identity is

```text
(x + u)^d - u^d = x * GN d x u.
```

For the dual difference used in the motivating calculation,

```text
(x + u)^d - x^d = u * GN d u x.
```

Therefore this checkpoint studies the **dual-oriented cubic kernel**

```lean
GN 3 u x
```

whose explicit polynomial is

$$
GN_3(u,x)=u^2+3ux+3x^2.
$$

For a target `p`, the equation

$$
GN_3(u,x)=p
$$

is therefore equivalent to the cubic finite-difference equation

$$
(x+u)^3-x^3=up.
$$

The purpose of GNPC-005 is to expose the exact quadratic-form and centered-square structure hidden in this cubic difference.

---

# 1. Existing DkMath structure to reuse

Repository reconnaissance already found the following relevant theory.

`DkMath.NumberTheory.TraceOneQuadratic` defines

```lean
def norm (x : TraceOneInt s) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - s * x.snd ^ 2
```

and at `s = -1`:

```lean
theorem traceOneNorm_neg_one (a b : ℤ) :
    norm (⟨a, b⟩ : TraceOneInt (-1)) = a ^ 2 + a * b + b ^ 2
```

as well as the general discriminant identity

```lean
theorem four_mul_traceOneNorm_eq_discriminant ...
```

The existing FLT bridge already records related cubic/Eisenstein facts:

```lean
DkMath.FLT.GN_three_sub_eq_traceOneNorm_negOne
DkMath.FLT.eisensteinNorm_shift_eq_traceOneNorm_negOne
```

and `DkMath.FLT.GEisensteinBridge` contains the standard `d = 3` expansion path.

There is also an existing declaration named `GN_three_explicit` in the repository. Before implementation, locate its canonical owner and exact namespace/type. Reuse it if the import direction remains thin and appropriate. Do **not** import a heavy FLT/Zsigmondy application module into a new NumberTheory owner merely to save a one-line polynomial expansion. If necessary, prove the cubic expansion locally from the canonical `GN_eq_sum` instead.

GNPC-005 must not duplicate the FLT bridge under a new name without adding the new direct coordinate and centered-square API described below.

---

# 2. Main mathematical identities

The dual-oriented cubic kernel satisfies

$$
GN_3(u,x)=u^2+3ux+3x^2.
$$

The same value is the positive-definite binary quadratic form

$$
GN_3(u,x)=(x+u)^2+(x+u)x+x^2.
$$

Thus with

```text
a = x + u
b = x
```

it is exactly the discriminant `-3` trace-one/Eisenstein norm form

$$
a^2+ab+b^2.
$$

The key centered-square identity is

$$
4GN_3(u,x)=u^2+3(2x+u)^2.
$$

This is the exact integer form of the observed cubic "core" geometry. It avoids fractions and avoids truncated natural subtraction.

For a target `p`, therefore

$$
GN_3(u,x)=p
\iff
4p=u^2+3(2x+u)^2.
$$

Equivalently over integers, the centered residual

$$
3(2x+u)^2+u^2-4p
$$

vanishes. This is the clean formal version of the positive square core balanced against the negative target-side core.

---

# 3. Required reconnaissance before changes

Before writing the new module:

1. Search for existing declarations equivalent to any of:
   - `GN 3 u x = u^2 + 3*u*x + 3*x^2`;
   - `GN 3 u x = (x+u)^2 + (x+u)*x + x^2`;
   - `4 * GN 3 u x = u^2 + 3*(2*x+u)^2`;
   - a direct `GN 3 u x` → `TraceOneInt (-1)` norm theorem.

2. Locate the canonical owner and exact theorem type of `GN_three_explicit`.

3. Inspect the existing `TraceOneQuadratic` API and determine whether the direct NumberTheory bridge can be proved without importing FLT application modules.

4. Check whether Mathlib already has a suitable binary quadratic-form / completed-square theorem worth reusing. Do not add a heavy quadratic-form framework if elementary `ring`/`norm_num` is enough.

5. Prefer a new thin owner:

```text
DkMath/NumberTheory/GNThreeQuadratic.lean
```

Document any different ownership decision in `report-005.md`.

---

# 4. Required theorem surface

Exact names may be adjusted slightly after reconnaissance, but preserve the mathematical surface and dependency direction.

## P0 — direct cubic expansion in dual orientation

Preferred theorem:

```lean
theorem GN_three_dual_explicit (u x : ℕ) :
    DkMath.CosmicFormulaBinom.GN 3 u x =
      u ^ 2 + 3 * u * x + 3 * x ^ 2 := by
  ...
```

If the canonical existing `GN_three_explicit` already yields exactly this by argument substitution, expose only a thin ergonomic alias if that is genuinely useful. Avoid pointless duplication.

## P1 — positive-definite quadratic-form representation

Preferred theorem:

```lean
theorem GN_three_eq_discriminant_neg_three_form (u x : ℕ) :
    DkMath.CosmicFormulaBinom.GN 3 u x =
      (x + u) ^ 2 + (x + u) * x + x ^ 2 := by
  ...
```

This should make the `a^2 + ab + b^2` structure explicit without requiring FLT vocabulary.

## P2 — direct trace-one norm bridge

Preferred theorem:

```lean
theorem GN_three_eq_traceOneNorm_negOne (u x : ℕ) :
    ((DkMath.CosmicFormulaBinom.GN 3 u x : ℕ) : ℤ) =
      DkMath.NumberTheory.TraceOneQuadratic.norm
        (⟨((x + u : ℕ) : ℤ), (x : ℤ)⟩ :
          DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt (-1)) := by
  ...
```

Adjust casts/syntax as required by Lean.

This theorem is the neutral NumberTheory form of the previously FLT-local Eisenstein/trace-one bridge. Do not remove or rewrite the existing FLT theorems in this checkpoint.

## P3 — centered-square identity

This is the central GNPC-005 theorem.

Preferred theorem:

```lean
theorem four_mul_GN_three_eq_centered_square (u x : ℕ) :
    4 * DkMath.CosmicFormulaBinom.GN 3 u x =
      u ^ 2 + 3 * (2 * x + u) ^ 2 := by
  ...
```

Keep this theorem in `ℕ` if possible. The subtraction-free form is deliberate.

## P4 — exact target characterization

Preferred theorem:

```lean
theorem GN_three_eq_target_iff_centered_square
    {p u x : ℕ} :
    DkMath.CosmicFormulaBinom.GN 3 u x = p ↔
      4 * p = u ^ 2 + 3 * (2 * x + u) ^ 2 := by
  ...
```

This should be a thin consequence of P3, not a second expansion proof.

## P5 — unit-slice specialization

Expose the `u = 1` slice explicitly:

```lean
theorem GN_three_one_eq_target_iff_centered_square
    {p x : ℕ} :
    DkMath.CosmicFormulaBinom.GN 3 1 x = p ↔
      4 * p = 1 + 3 * (2 * x + 1) ^ 2 := by
  ...
```

This theorem captures the observed fact that `d = 3, u = 1` representation is a square-shell condition stronger than the GNPC-004 residue condition `3 ∣ p - 1`.

---

# 5. Centered residual / "negative core" API

If it remains thin, make the zero-level-set viewpoint explicit over integers.

Suggested definition:

```lean
def GNThreeCenteredResidual (p u x : ℤ) : ℤ :=
  3 * (2 * x + u) ^ 2 + u ^ 2 - 4 * p
```

Then prove a natural-coordinate bridge such as:

```lean
theorem GN_three_eq_target_iff_centeredResidual_eq_zero
    {p u x : ℕ} :
    DkMath.CosmicFormulaBinom.GN 3 u x = p ↔
      GNThreeCenteredResidual (p : ℤ) (u : ℤ) (x : ℤ) = 0 := by
  ...
```

This theorem is strongly preferred if the cast proof stays short and stable, because it records the exact geometric reading:

```text
positive centered square core
        + u^2
        - 4*target
        = 0
```

Do not introduce real square roots or fractions merely to state the center `-u/2`. The integral residual already contains the same geometry in a Lean-stable form.

---

# 6. Prime-target interpretation

GNPC-005 is primarily algebraic and must remain valid for arbitrary natural target `p`; do not require primality for P0–P5.

However, add a short theorem or docstring connection showing how this combines with GNPC-004 for prime targets of degree `3`.

For a positive prime-target representation at degree `3`, GNPC-004 already gives

$$
3\mid p-1.
$$

GNPC-005 adds the stronger coordinate shell

$$
4p=u^2+3(2x+u)^2.
$$

Thus the residue filter is necessary but does not by itself classify a fixed `u` slice.

Do not try to classify all primes represented by the form in this checkpoint.

---

# 7. Required regression anchors

Keep checks tiny and explanatory.

## `p = 13`, unit slice fails

Record that

```text
GN 3 1 x = 13
```

has no natural solution, if this can be proved with a short stable proof.

Preferred example/theorem shape:

```lean
example : ¬ ∃ x : ℕ, DkMath.CosmicFormulaBinom.GN 3 1 x = 13 := by
  ...
```

Do not spend excessive proof-engineering time on this regression. If it is awkward, report it as omitted rather than bloating the checkpoint.

## `p = 13`, another cubic coordinate exists

This one is mandatory and lightweight:

```lean
example : DkMath.CosmicFormulaBinom.GN 3 2 1 = 13 := by
  ...
```

Optionally also package:

```lean
example : GNPositiveRepresentation 13 3 2 1 := by
  ...
```

if importing the GNPC representation layer remains natural.

The pair of examples should document the distinction:

```text
fixed dual slice u = 1: no representation of 13
full positive d = 3 representation space: (u,x) = (2,1) does represent 13
```

---

# 8. Important interpretation note

Do not describe

$$
p=u^2+3ux+3x^2
$$

as a multiplicative factorization of the prime `p`.

The point is the opposite:

- multiplicatively, `p` remains prime;
- GN gives an additive/polynomial coordinate representation;
- at degree `3`, this representation is exactly a positive-definite discriminant `-3` quadratic norm shell;
- the centered-square identity exposes its midpoint geometry.

This distinction should appear in the module docstring/report.

---

# 9. Forbidden scope expansion

Do not implement in GNPC-005:

- full classification of primes represented by `a^2 + ab + b^2`;
- quadratic reciprocity or a theorem `p ≡ 1 [MOD 3] ↔ representation`;
- uniqueness/class number theory;
- Eisenstein integer UFD development;
- cyclotomic factorization beyond the already-existing bridge references;
- Zsigmondy / primitive-prime existence;
- general `d > 3` centered normal forms;
- real/complex geometry requiring square roots;
- ABC / FLT / Legendre / RH application work;
- repository-wide relocation of old FLT Eisenstein bridge files.

GNPC-005 stops at the exact degree-3 quadratic/norm/centered-square characterization.

---

# 10. Validation

Build at least the final owner module, expected:

```text
lake build DkMath.NumberTheory.GNThreeQuadratic
```

Requirements:

- no new `sorry`;
- no new `axiom`;
- no warning-producing unused theorem arguments;
- keep imports thin;
- do not modify existing FLT bridge behavior unless a genuinely necessary compatibility adjustment is documented.

---

# 11. Required report

Write:

```text
lean/dk_math/docs/dev/NumberTheory-GNPrimeClosure-260901-v0/report-005.md
```

Include:

1. Outcome A / B / C.
2. Existing cubic/Eisenstein/TraceOne declarations found during reconnaissance.
3. Whether `GN_three_explicit` was reused and from which canonical owner.
4. Final owner module and imports.
5. Final theorem types P0–P5.
6. Whether the centered residual API was added.
7. Regression status for `p = 13` (`u = 1` failure and `(u,x) = (2,1)` success).
8. Build results.
9. Deferred classification/generalization items.

---

# 12. Stop condition

STOP when the following degree-3 structure is formally available and validated:

```text
GN 3 u x
  = u^2 + 3*u*x + 3*x^2
  = (x+u)^2 + (x+u)*x + x^2
  = discriminant -3 trace-one norm

4 * GN 3 u x
  = u^2 + 3*(2*x+u)^2

GN 3 u x = p
  ↔ 4*p = u^2 + 3*(2*x+u)^2
```

Do not continue automatically into representation classification or reciprocity theory.
