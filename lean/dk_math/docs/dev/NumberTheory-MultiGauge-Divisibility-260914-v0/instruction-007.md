# instruction-007 — MG-004B general TraceOne lattice landing

## Role

Implement the neutral generalization of the approved MG-004A Eisenstein lattice
landing theorem.

MG-004A is frozen and approved. The purpose of this checkpoint is to remove the
specialization `s = -1` from the receiver theorem **without** assuming a false
global zero-fiber property for the norm.

## Read first

Read the exact current sources before coding:

```text
DkMath/NumberTheory/TraceOneQuadratic.lean
DkMath/Lib/NumberTheory/EisensteinCoordinates.lean
DkMath/Lib/NumberTheory/EisensteinLatticeLanding.lean
```

Also read:

```text
report-006.md
review-006.md
ROADMAP.md
```

Use existing theorem names and exact signatures rather than remembered forms.

---

## Mathematical objective

For arbitrary `s : ℤ`, let

```text
alpha = (a,b)
beta  = (c,d)
```

inside `TraceOneInt s`.

Production definitions already give

```text
conj beta = (c+d,-d)
norm beta = c^2 + c*d - s*d^2.
```

Therefore

```text
(alpha * conj beta).fst = a*c + a*d - s*b*d
(alpha * conj beta).snd = b*c - a*d.
```

The target theorem is:

```text
norm beta != 0
->
(beta | alpha
  <->
  norm beta | (alpha * conj beta).fst
  and
  norm beta | (alpha * conj beta).snd)
```

The explicit coordinate-polynomial form should also be exported.

This is the general integer-lattice landing criterion. No positivity or
positive-definite hypothesis is required when nonzero norm is supplied directly.

---

## Critical generalization warning

Do **not** prove or assume

```text
norm x = 0 <-> x = 0
```

for arbitrary `s`.

It is false in general. In particular, for `s = 0`:

```text
tau 0 != 0
norm (tau 0) = 0.
```

MG-004B must therefore use the explicit hypothesis

```text
norm beta != 0
```

for the reverse/cancellation direction.

---

## Task 1 — add neutral generic module

Add:

```text
DkMath/Lib/NumberTheory/TraceOneLatticeLanding.lean
```

Prefer importing only:

```text
DkMath.NumberTheory.TraceOneQuadratic
```

plus minimal Mathlib tactics if required.

Keep this module independent of:

```text
MultiGauge
PrimorialUniverse
Legendre
ABC
FLT
Petal
Eisenstein application modules
```

unless the dependency direction already requires a neutral lower import.

---

## Task 2 — generic conjugate-product coordinate formulas

Expose reusable formulas for arbitrary `TraceOneInt s`, preferably both at the
structured-element level and, if useful, the explicit coordinate level.

Expected formulas:

```text
conj ⟨c,d⟩ = ⟨c+d,-d⟩

(⟨a,b⟩ * conj ⟨c,d⟩).fst
  = a*c + a*d - s*b*d

(⟨a,b⟩ * conj ⟨c,d⟩).snd
  = b*c - a*d.
```

Do not create a second conjugation or norm API.

---

## Task 3 — generic nonzero-norm cancellation

Prove a reusable theorem of the shape

```text
theorem traceOne_mul_right_cancel_of_norm_ne_zero
    {s : ℤ} {x y z : TraceOneInt s}
    (hz : norm z != 0)
    (h : x * z = y * z) :
    x = y
```

or an equivalent orientation/name.

### Required proof mechanism

Do not use a general zero-fiber theorem for `norm`.

Let

```text
w = x - y = (p,q)
z = (c,d).
```

From `w*z = 0`, the two coordinate equations are

```text
p*c + s*q*d = 0
p*d + q*c + q*d = 0.
```

Eliminate to obtain

```text
p * (c^2 + c*d - s*d^2) = 0
q * (c^2 + c*d - s*d^2) = 0.
```

The parenthesized factor is exactly `norm z`. Since it is nonzero in `ℤ`,
conclude `p = q = 0`.

An equivalent determinant proof is acceptable if it remains local and
transparent.

Also prove or reuse

```text
norm (conj z) = norm z
```

as needed by the reverse landing proof.

---

## Task 4 — forward coordinate divisibility

Prove the generic necessary condition:

```text
beta | alpha
->
norm beta | (alpha * conj beta).fst
and
norm beta | (alpha * conj beta).snd.
```

This direction should not require `norm beta != 0`.

Recommended mechanism:

```text
alpha = beta * q
alpha * conj beta
  = (beta * conj beta) * q
  = ofInt s (norm beta) * q.
```

Then read both integer coordinates.

---

## Task 5 — reverse reconstruction and main iff

Under

```text
hNorm : norm beta != 0
```

and coordinate divisibility, obtain integers `r,t` and define

```text
q : TraceOneInt s := ⟨r,t⟩.
```

Prove

```text
alpha * conj beta
=
(beta * q) * conj beta
```

using

```text
beta * conj beta = ofInt s (norm beta).
```

Then cancel `conj beta` using the generic nonzero-norm cancellation theorem.

Export a theorem with an ergonomic shape such as:

```text
traceOne_dvd_iff_norm_dvd_mul_conj_coordinates
```

or

```text
traceOne_dvd_iff_norm_dvd_conjugate_coordinates.
```

The exact name may follow existing naming conventions.

---

## Task 6 — explicit coordinate-polynomial corollary

For

```text
alpha = ⟨a,b⟩
beta  = ⟨c,d⟩
```

export the polynomial form:

```text
(c^2 + c*d - s*d^2) != 0
->
(beta | alpha
  <->
  (c^2 + c*d - s*d^2) | (a*c + a*d - s*b*d)
  and
  (c^2 + c*d - s*d^2) | (b*c - a*d)).
```

This should be a corollary of the structured theorem, not a separate duplicate
proof if avoidable.

---

## Task 7 — norm divisibility necessity

If not already available generically, prove:

```text
beta | alpha -> norm beta | norm alpha.
```

This theorem is valid for all `s` by norm multiplicativity and does not require
nonzero norm.

Do not claim the converse.

---

## Task 8 — specialize back to Eisenstein

Audit the existing MG-004A module against the new generic theorem.

At minimum, add a regression/corollary showing that the generic theorem at
`s = -1` reproduces the approved Eisenstein landing criterion.

If a small refactor makes
`eisenstein_dvd_iff_norm_dvd_conjugate_coordinates` a direct corollary of the
generic theorem, that is welcome, but preserve all public MG-004A theorem names
and avoid unnecessary churn.

Do not weaken the existing concrete nonzero-beta API merely because the generic
theorem uses `norm beta != 0`: in the Eisenstein specialization, positive
definiteness already converts nonzero beta to nonzero norm.

---

## Task 9 — zero-norm regression

Add a small kernel-checked regression documenting why the general theorem uses
nonzero norm, for example:

```text
norm (tau 0) = 0
and
tau 0 != 0.
```

This is a scope/semantic guard, not a counterexample to the landing theorem.

Do not attempt a classification of every `s` for which the norm is definite or
anisotropic in this checkpoint.

---

## Facade

Update the neutral Lib facade so the new generic module is exported.

Recommended dependency direction:

```text
TraceOneQuadratic
  -> TraceOneLatticeLanding
  -> EisensteinCoordinates
  -> EisensteinLatticeLanding
```

Exact imports may differ if the current facade/order makes a smaller change
preferable, but avoid cycles.

---

## Required validation

Run at least:

```text
lake build DkMath.Lib.NumberTheory.TraceOneLatticeLanding
lake build DkMath.Lib.NumberTheory.EisensteinLatticeLanding
lake build DkMath.Lib
git diff --check
```

Scan changed Lean sources for:

```text
sorry
admit
new axiom declarations
```

Report any warnings attributable to the new modules.

---

## Report

Add:

```text
docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-007.md
```

Include:

```text
Outcome;
files changed;
generic conjugate-product formula;
generic cancellation mechanism;
main structured iff;
explicit polynomial iff;
norm-divisibility necessity;
Eisenstein specialization status;
zero-norm regression;
build results;
warnings / forbidden-syntax scan;
scope deviations;
MG-004C readiness.
```

---

## Outcome policy

### Outcome A — GENERAL TRACEONE LANDING ESTABLISHED

Required:

- generic nonzero-norm cancellation;
- generic coordinate divisibility forward theorem;
- generic reverse reconstruction;
- exact divisibility iff;
- explicit coordinate corollary;
- successful focused builds.

Then MG-004C may investigate power/Core-image landing.

### Outcome B — EISENSTEIN REMAINS THE STABLE RECEIVER

Use if the generic cancellation/reconstruction becomes materially obstructed or
requires a stronger algebraic assumption than `norm beta != 0`.

Record the exact obstruction and keep MG-004A as the production endpoint.

### Outcome C — REPRESENTATION MISMATCH

Use only if the current `TraceOneInt s` representation cannot support the
claimed generic coordinate theorem without redesign. Stop rather than building
parallel arithmetic infrastructure.
