# instruction-000 — GNIP-000 neutral gnomon algebra recovery

## Goal

Create the neutral production source for square-gnomon arithmetic that is currently duplicated or application-owned in `DkMath.Collatz.GnomonEvaluation`.

This checkpoint is recovery plus a small genuine generalization: promote the unit odd gnomon to an arbitrary side-thickness square band and prove its composition / reconstruction laws.

Do **not** touch Legendre, Collatz, GN, Pascal, Polyomino, FLT, or ABC in this checkpoint except to read them for compatibility.

## Target files

Preferred production module:

```text
DkMath/Gnomon/Algebra.lean
```

Preferred facade:

```text
DkMath/Gnomon.lean
```

Namespace:

```lean
namespace DkMath.Gnomon
```

Use the repository's normal copyright header and `#print "file: ..."` convention.

## Existing source to recover

Read first:

```text
DkMath/Collatz/GnomonEvaluation.lean
```

Existing facts there include:

```text
OddGnomonLayer n = 2*n+1
square_succ_eq_square_add_oddGnomonLayer
sum_oddGnomonLayer_eq_square
sum_odd_eq_square
square_add_eq_square_add_gnomon_sum
```

Also read the broad source design:

```text
docs/not_implements/260730-gnomon-prime-petal-pascal-polyomino-roadmap.md
```

Do not move or rewrite Collatz yet.  GNIP-002 will do the compatibility refactor after this neutral API is approved.

---

## 1. Definitions

Add:

```lean
def oddGnomon (n : ℕ) : ℕ :=
  2 * n + 1

/-- Area added when a square of side `x` grows by side-thickness `u`. -/
def squareGnomonBand (x u : ℕ) : ℕ :=
  u * (2 * x + u)

/-- Multiplication transported to odd-gnomon addresses. -/
def petalMul (a b : ℕ) : ℕ :=
  2 * a * b + a + b
```

Interpretation requirement for docstrings:

```text
u is a side-thickness, not an area increment.
u = 1 is the atomic lattice growth step.
Its induced area increment is oddGnomon x = 2*x+1.
```

Do not add a decorative constant definition for `GnomonBeam = 1`; the unit specialization theorem below is the mathematical content.

---

## 2. Basic odd-gnomon API

Implement at least:

```lean
@[simp] theorem oddGnomon_zero : oddGnomon 0 = 1

theorem oddGnomon_succ (n : ℕ) :
  oddGnomon (n + 1) = oddGnomon n + 2

theorem oddGnomon_pos (n : ℕ) :
  0 < oddGnomon n

theorem oddGnomon_odd (n : ℕ) :
  Odd (oddGnomon n)

theorem oddGnomon_injective :
  Function.Injective oddGnomon

theorem oddGnomon_eq_one_iff (n : ℕ) :
  oddGnomon n = 1 ↔ n = 0
```

Naming may be adjusted minimally to repository style, but report the final exported names.

---

## 3. Petal multiplication — old Checkpoint A recovery

Implement the pure algebraic laws from the 2026-07-30 roadmap:

```lean
@[simp] theorem petalMul_zero_left (a : ℕ) :
  petalMul 0 a = a

@[simp] theorem petalMul_zero_right (a : ℕ) :
  petalMul a 0 = a

theorem petalMul_comm (a b : ℕ) :
  petalMul a b = petalMul b a

theorem petalMul_assoc (a b c : ℕ) :
  petalMul (petalMul a b) c = petalMul a (petalMul b c)

theorem oddGnomon_petalMul (a b : ℕ) :
  oddGnomon (petalMul a b) = oddGnomon a * oddGnomon b
```

This checkpoint does **not** add `PetalAtom`, prime equivalence, unique odd-prime addresses, or typeclass structure for a custom monoid.

---

## 4. Unit square-growth theorem

Recover the application-owned square successor theorem in neutral form:

```lean
theorem square_add_oddGnomon (x : ℕ) :
  x ^ 2 + oddGnomon x = (x + 1) ^ 2
```

An orientation-equivalent theorem is acceptable, but the additive Nat form above should exist because it avoids subtraction.

---

## 5. Arbitrary-thickness square-growth theorem

This is the first required generalization beyond the existing Collatz unit layer.

Prove:

```lean
theorem square_add_squareGnomonBand (x u : ℕ) :
  x ^ 2 + squareGnomonBand x u = (x + u) ^ 2
```

Required specializations:

```lean
@[simp] theorem squareGnomonBand_zero (x : ℕ) :
  squareGnomonBand x 0 = 0

@[simp] theorem squareGnomonBand_unit (x : ℕ) :
  squareGnomonBand x 1 = oddGnomon x

@[simp] theorem squareGnomonBand_zero_anchor (u : ℕ) :
  squareGnomonBand 0 u = u ^ 2
```

The last theorem is the simplest reconstruction/inversion boundary: accumulating thickness `u` from the zero anchor produces the square body `u^2`.

---

## 6. Composition / conservation law

Prove the exact path-composition identity:

```lean
theorem squareGnomonBand_add (x u v : ℕ) :
  squareGnomonBand x (u + v) =
    squareGnomonBand x u + squareGnomonBand (x + u) v
```

Mathematical meaning:

```text
grow x by u+v in one step
=
grow x by u, then grow x+u by v.
```

This theorem is important for the later inversion/projection analysis.  It is a genuine conservation/composition statement, not just naming.

Also add the one-step corollary if useful:

```lean
squareGnomonBand x (u+1)
=
squareGnomonBand x u + oddGnomon (x+u)
```

Do not add it if it is only a noisy duplicate and not useful to the shifted-sum proof.

---

## 7. Unit-layer decomposition and inverse reconstruction

Prove the shifted unit decomposition:

```lean
theorem squareGnomonBand_eq_sum_shifted_oddGnomon
    (x u : ℕ) :
    squareGnomonBand x u =
      (Finset.range u).sum (fun i => oddGnomon (x + i))
```

Then recover the classical square reconstruction in the neutral namespace:

```lean
theorem sum_oddGnomon_eq_square (n : ℕ) :
    (Finset.range n).sum oddGnomon = n ^ 2
```

Optional compatibility alias:

```lean
theorem sum_odd_eq_square (n : ℕ) :
    (Finset.range n).sum (fun i => 2 * i + 1) = n ^ 2
```

The shifted-band theorem is more important than the alias.

---

## 8. Required concrete regressions

Kernel-check at least these values using `example` or named lightweight theorems only if they improve the API:

```text
oddGnomon 0 = 1
oddGnomon 1 = 3
oddGnomon 2 = 5
oddGnomon 30 = 61
oddGnomon 31 = 63
squareGnomonBand 30 1 = 61
squareGnomonBand 30 2 = 124 = 61 + 63
```

The `30 -> 31` values are regression anchors for the later prime-gauge audit.  They do not assert anything about primality or Legendre.

---

## 9. Dependency boundary

`DkMath.Gnomon.Algebra` must not import any of:

```text
DkMath.Collatz.*
DkMath.NumberTheory.Legendre.*
DkMath.NumberTheory.MultiGauge.*
DkMath.Lib.Cosmic.GTail
DkMath.CosmicFormula.*
DkMath.Polyomino*
DkMath.FLT*
DkMath.ABC*
```

Use the smallest neutral import that provides Nat arithmetic, `Finset`, `Odd`, and tactics.

The GTail/Cosmic connection is deliberately deferred to GNIP-001 so dependency direction remains clean.

---

## 10. Validation

Run from `lean/dk_math`:

```text
lake build DkMath.Gnomon.Algebra
lake build DkMath.Gnomon
```

If the facade is intentionally omitted, explain why in the report and build only the production module.

Also run:

```text
git diff --check
```

Scan changed Lean files for:

```text
sorry
admit
axiom
```

No new axiom declarations.

---

## 11. Deliverable report

Create:

```text
docs/dev/NumberTheory-Gnomon-Inversion-Projection-260914-v0/report-000.md
```

Report:

1. Outcome.
2. Files added/changed.
3. Final theorem names.
4. Whether the old Checkpoint A pure algebra is now recovered.
5. Whether arbitrary-thickness growth and composition were established.
6. Whether shifted unit decomposition and square reconstruction were established.
7. Exact dependency imports.
8. Build results.
9. Scope deviations.
10. Whether GNIP-001 Cosmic/GTail bridge is justified.

Outcome policy:

```text
A — RECOVERY + GENERALIZATION COMPLETE
    Neutral algebra, arbitrary band, composition, shifted sum all established.

B — RECOVERY COMPLETE / GENERALIZATION PARTIAL
    Existing unit facts recovered but one of band composition or shifted sum is blocked.
    Record the exact blocker; do not use an application import to bypass it.

C — EXISTING NEUTRAL API ALREADY SUBSUMES TARGET
    Reuse the exact existing source instead of creating duplicate definitions.
```
