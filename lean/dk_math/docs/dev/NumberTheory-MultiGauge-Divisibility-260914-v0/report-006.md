# MG-004A Eisenstein lattice landing

## Outcome

**Outcome A — LATTICE LANDING IFF ESTABLISHED**

The neutral Eisenstein coordinate layer now has an exact element-divisibility
criterion inside the existing `TraceOneInt (-1)` carrier.  The implementation
reuses the existing multiplication, conjugation, and norm APIs and adds no
second ring, field, Euclidean-domain, or application bridge.

## Files changed

Added:

```text
DkMath/Lib/NumberTheory/EisensteinLatticeLanding.lean
docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-006.md
```

Updated:

```text
DkMath/Lib.lean
docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/ROADMAP.md
```

The requested `DkMath/Lib/NumberTheory/TraceOneQuadratic.lean` path does not
exist in the current tree.  The existing carrier implementation is
`DkMath/NumberTheory/TraceOneQuadratic.lean`, which is already imported by
`DkMath.Lib.NumberTheory.EisensteinCoordinates` and was used unchanged.

## Coordinate and norm API

The new conjugation theorem is:

```text
conj (eisensteinCoord c d)
  = eisensteinCoord (c - d) (-d)
```

The exact conjugate-product formula is:

```text
eisensteinCoord a b * conj (eisensteinCoord c d)
  = eisensteinCoord
      (a*c - a*d + b*d)
      (b*c - a*d)
```

This is `eisensteinCoord_mul_conj` and is proved from the existing
`eisensteinCoord_mul` theorem.

For the positive-definite standard norm, the new zero-fiber theorem is:

```text
norm (eisensteinCoord c d) = 0 ↔ c = 0 ∧ d = 0
```

The proof uses the elementary identity

```text
4 * (c^2 - c*d + d^2) = (2*c - d)^2 + 3*d^2.
```

The reusable arbitrary-element form is
`traceOne_neg_one_norm_eq_zero_iff`; it supports cancellation for arbitrary
quotients in `TraceOneInt (-1)`.  Consequently a nonzero Eisenstein element
has nonzero norm, and right multiplication by an element of nonzero norm is
cancelable in this carrier.

## Main lattice-landing theorem

The public theorem is:

```text
eisenstein_dvd_iff_norm_dvd_conjugate_coordinates
```

For nonzero `eisensteinCoord c d`, it proves:

```text
eisensteinCoord c d ∣ eisensteinCoord a b ↔
  norm (eisensteinCoord c d) ∣ (a*c - a*d + b*d) ∧
  norm (eisensteinCoord c d) ∣ (b*c - a*d)
```

The explicit polynomial statement is also exported as
`eisenstein_dvd_iff_polynomial_norm_dvd_conjugate_coordinates`.

The forward direction takes an arbitrary TraceOne quotient `q`, multiplies by
the conjugate, uses
`beta * conj beta = ofInt (-1) (norm beta)`, and reads the two coordinates.
It does not assume that the quotient was already written in standard
Eisenstein coordinates.

For the converse, coordinate divisibility supplies integers `r,s` with the
two displayed products equal to `norm beta * r` and `norm beta * s`.  The
quotient is reconstructed as `eisensteinCoord r s`.  The proof establishes

```text
alpha * conj beta = (beta * quotient) * conj beta
```

and cancels the nonzero conjugate using norm multiplicativity and the
positive-definite zero-fiber lemma.

## Norm divisibility is only necessary

The corollary

```text
eisenstein_dvd_imp_norm_dvd_norm
```

proves `beta ∣ alpha -> norm beta ∣ norm alpha` directly from the existing
`traceOne_norm_mul` theorem.  No converse is stated at the norm level.

The kernel-checked regression is:

```text
alpha = eisensteinCoord (-1) 2
beta  = eisensteinCoord (-2) 1
```

Both norms are `7`, while the conjugate-product coordinates are `5` and `-3`:

```text
norm beta = 7
norm alpha = 7
alpha * conj beta = eisensteinCoord 5 (-3)
```

Thus `norm beta ∣ norm alpha`, but the main iff rejects `beta ∣ alpha` because
`7` divides neither `5` nor `-3`.  This certifies that norm divisibility alone
does not establish integral lattice landing.

## Scope and next layer

No general `TraceOneInt s` landing theorem, MultiGauge bridge, ABC/FLT/Petal
bridge, power-image theorem, Euclidean-domain/UFD infrastructure, or analytic
result was added.

MG-004B general `TraceOneInt s` lattice landing is now justified as a future
audit/implementation target: the concrete `s = -1` receiver is production
complete and exposes exactly which positive-definite and coordinate-cancellation
lemmas must be generalized.  MG-004B itself is not implemented here.

## Validation

Commands were run from `lean/dk_math` on branch
`wip/number-theory-multi-gauge-divisibility-260914-v0`:

```text
lake build DkMath.Lib.NumberTheory.EisensteinLatticeLanding
lake build DkMath.Lib
```

Both completed successfully, with `8658` and `8668` jobs respectively.  The
successful builds emitted no Lean warning diagnostics from the new module or
facade.  Existing `#print axioms` output contains only the pre-existing kernel
logical foundations (`propext`, `Classical.choice`, and `Quot.sound`); no
`sorryAx` appears for the new declarations.

`git diff --check` completed successfully.  The changed Lean sources were
scanned for `sorry`, `admit`, and new `axiom` declarations; none were found.
The shell profile emitted `/opt/wonderful/bin/wf-env: Permission denied`
during commands; this was environmental noise and did not affect the builds.
