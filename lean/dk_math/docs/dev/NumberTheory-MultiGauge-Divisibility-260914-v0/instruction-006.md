# instruction-006 — MG-004A Eisenstein lattice landing

## Role

Implement the first concrete Norm/lattice receiver layer after the MultiGauge front-half audit.

MG-003C is frozen as Outcome B: there is no unconditional primitive-shape `GNGaugeTransition` provider in current production. Do not repair or bypass that boundary in this checkpoint.

## Read first

Read exactly:

```text
docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/ROADMAP.md
.../report-005.md
.../review-005.md
DkMath/Lib/NumberTheory/EisensteinCoordinates.lean
DkMath/NumberTheory/TraceOneQuadratic.lean
```

Also inspect the exact current theorem signatures before coding.

## Mathematical objective

Work in the existing standard Eisenstein coordinate model

```text
eisensteinCoord a b
```

inside `TraceOneInt (-1)`.

For

```text
alpha = eisensteinCoord a b
beta  = eisensteinCoord c d
```

the existing norm is

```text
N(beta) = c^2 - c*d + d^2.
```

The conjugate-product coordinates are

```text
alpha * conj(beta)
=
eisensteinCoord
  (a*c - a*d + b*d)
  (b*c - a*d).
```

For `beta != 0`, prove the exact lattice-landing criterion:

```text
beta ∣ alpha
<->
N(beta) ∣ (a*c - a*d + b*d)
and
N(beta) ∣ (b*c - a*d).
```

This is the main required theorem.

The theorem must make the distinction explicit:

```text
N(beta) ∣ N(alpha)
```

is necessary for `beta ∣ alpha`, but is not sufficient for lattice landing.

## Placement

Preferred new production module:

```text
DkMath/Lib/NumberTheory/EisensteinLatticeLanding.lean
```

Preferred namespace:

```lean
namespace DkMath.Lib.NumberTheory
```

Import `EisensteinCoordinates` and only the tactics actually needed.

Update the appropriate Lib facade only if that facade already aggregates neighboring number-theory modules. Do not add MultiGauge, ABC, FLT, Petal, or Legendre imports to this neutral module.

## Task 1 — conjugation and numerator coordinates

Prove or expose a clean coordinate theorem for conjugation, e.g. an equivalent of:

```lean
conj (eisensteinCoord c d) = eisensteinCoord (c - d) (-d)
```

Then prove the exact conjugate-product coordinate identity:

```lean
eisensteinCoord a b * conj (eisensteinCoord c d)
  = eisensteinCoord
      (a*c - a*d + b*d)
      (b*c - a*d)
```

Do not introduce a second Eisenstein ring or a duplicate norm.

## Task 2 — nonzero norm for nonzero Eisenstein coordinates

The main iff needs cancellation by `N(beta)`. Supply the smallest reusable API showing that the positive-definite Eisenstein norm vanishes only at zero.

Suggested theorem shape:

```lean
N(eisensteinCoord c d) = 0 <-> c = 0 ∧ d = 0
```

or equivalently

```lean
eisensteinCoord c d ≠ 0 -> N(eisensteinCoord c d) ≠ 0.
```

A useful elementary identity is

```text
4 * (c^2 - c*d + d^2)
=
(2*c - d)^2 + 3*d^2.
```

Keep this proof local and elementary. Do not build a new ordered-ring hierarchy for `TraceOneInt`.

## Task 3 — necessary coordinate divisibility

Prove the forward implication:

```text
beta ∣ alpha
->
N(beta) ∣ first conjugate-product coordinate
and
N(beta) ∣ second conjugate-product coordinate.
```

Use existing ring multiplication/conjugation/norm facts where useful.

The quotient witnessing `beta ∣ alpha` is an arbitrary `TraceOneInt (-1)` element; do not assume it is already supplied in standard Eisenstein notation without proving/repackaging that fact.

## Task 4 — sufficient coordinate divisibility / quotient reconstruction

Assume `beta != 0` and both coordinate divisibilities.

Reconstruct an integral quotient from the two integer quotients and prove:

```text
beta * quotient = alpha.
```

The proof may proceed through

```text
alpha * conj(beta) = N(beta) * quotient
```

and cancellation of the nonzero scalar `N(beta)`, or by direct coordinate algebra.

Prefer a proof that makes the lattice-landing mechanism visible and maintainable.

## Task 5 — main iff theorem

Required public theorem, naming may vary slightly if consistent with local style:

```lean
theorem eisenstein_dvd_iff_norm_dvd_conjugate_coordinates
    {a b c d : ℤ}
    (hbeta : eisensteinCoord c d ≠ 0) :
    eisensteinCoord c d ∣ eisensteinCoord a b ↔
      (c^2 - c*d + d^2) ∣ (a*c - a*d + b*d) ∧
      (c^2 - c*d + d^2) ∣ (b*c - a*d)
```

Equivalent use of `TraceOneQuadratic.norm (eisensteinCoord c d)` in the statement is acceptable if it produces a cleaner API, but also provide an explicit polynomial corollary if the main theorem remains abstract.

## Task 6 — norm divisibility is necessary

Provide a small theorem/corollary:

```text
beta ∣ alpha -> N(beta) ∣ N(alpha)
```

This should reuse `traceOne_norm_mul` rather than reproving multiplicativity.

Do not state the converse.

## Task 7 — strict separation regression

Required regression: certify a concrete pair with norm divisibility but no element divisibility.

A small candidate is:

```text
alpha = eisensteinCoord (-1) 2
beta  = eisensteinCoord (-2) 1
```

Both norms are `7`, while the conjugate-product coordinates are `5` and `-3`, so the coordinate criterion fails.

Prove a theorem equivalent to:

```text
N(beta) ∣ N(alpha)
and
¬ beta ∣ alpha.
```

This regression is important: it kernel-certifies the slogan

```text
norm divisibility is necessary but not sufficient for lattice landing.
```

If this exact numeric pair is awkward, use another small verified pair and record it in the report.

## Task 8 — scope discipline

Do not implement in MG-004A:

```text
- general TraceOneInt s lattice landing;
- MultiGauge -> Eisenstein application bridge;
- ABC beta*gamma^2 existence;
- FLT or Petal bridge;
- power/square-image landing;
- Euclidean-domain/UFD infrastructure;
- analytic counting;
- MG-002 automaton.
```

The point is one concrete exact receiver theorem.

## Validation

Run at minimum:

```text
lake build DkMath.Lib.NumberTheory.EisensteinLatticeLanding
```

and any changed facade build.

Also run:

```text
git diff --check
```

and scan changed Lean files for `sorry`, `admit`, and new `axiom` declarations.

## Deliverable

Add:

```text
docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-006.md
```

Report:

```text
- outcome;
- files changed;
- exact conjugate-product coordinate formula;
- nonzero-norm lemma used;
- main divisibility iff theorem;
- quotient reconstruction method;
- norm-divisibility necessary corollary;
- concrete norm-only counterexample;
- builds / warnings / forbidden syntax scan;
- whether MG-004B general TraceOne landing is now justified.
```

## Outcome policy

```text
Outcome A — LATTICE LANDING IFF ESTABLISHED
  Exact Eisenstein element-divisibility iff coordinate-divisibility theorem,
  plus norm-only counterexample, is production-proved.
  MG-004B general TraceOne audit is justified.

Outcome B — NECESSARY HALF ONLY
  Norm/conjugate-coordinate necessity is proved, but quotient reconstruction
  is blocked by the current API. Record the exact blocker; do not invent a
  field/fraction API just to force the converse.

Outcome C — EXISTING API ALREADY SUBSUMES TARGET
  If an exact existing theorem already proves the same iff, do not duplicate
  it. Record and reuse it instead.
```
