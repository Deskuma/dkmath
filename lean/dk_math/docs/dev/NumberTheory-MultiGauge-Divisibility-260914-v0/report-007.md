# MG-004B general TraceOne lattice landing

## Outcome

**Outcome A — GENERAL TRACEONE LANDING ESTABLISHED**

The existing `TraceOneInt s` carrier now has a neutral exact lattice-landing
criterion for arbitrary `s : ℤ`, under the direct hypothesis that the divisor
has nonzero norm.  The implementation does not assume a positive-definite
norm or a general zero-fiber theorem.

## Files changed

Added:

```text
DkMath/Lib/NumberTheory/TraceOneLatticeLanding.lean
docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-007.md
```

Updated:

```text
DkMath/Lib.lean
DkMath/Lib/NumberTheory/EisensteinLatticeLanding.lean
docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/ROADMAP.md
```

The instruction's path `DkMath/Lib/NumberTheory/TraceOneQuadratic.lean` does
not exist in the current tree.  The carrier source is
`DkMath/NumberTheory/TraceOneQuadratic.lean`; it was read and left unchanged.

## Generic conjugate-product formulas

The new neutral module exports:

```text
traceOne_conj_coordinates
traceOne_mul_conj_fst
traceOne_mul_conj_snd
traceOne_norm_conj
```

For arbitrary `s` and integer coordinates:

```text
conj ⟨c,d⟩ = ⟨c+d,-d⟩

(⟨a,b⟩ * conj ⟨c,d⟩).fst = a*c + a*d - s*b*d
(⟨a,b⟩ * conj ⟨c,d⟩).snd = b*c - a*d
```

These reuse the existing `TraceOneQuadratic` multiplication, conjugation, and
norm definitions; no parallel arithmetic API was introduced.

## Generic cancellation mechanism

`traceOne_mul_right_cancel_of_norm_ne_zero` is proved by reducing equality to
`(x - y) * z = 0`.  Writing `x - y = (p,q)` and `z = (c,d)`, the two zero
product coordinates are:

```text
p*c + s*q*d = 0
p*d + q*c + q*d = 0
```

The local determinant identities give:

```text
p * (c^2 + c*d - s*d^2) = 0
q * (c^2 + c*d - s*d^2) = 0
```

The common factor is exactly `norm z`.  The supplied nonzero-norm hypothesis
therefore forces `p = 0` and `q = 0`, after which `TraceOneInt` extensionality
gives cancellation.  The reverse landing proof also uses
`traceOne_norm_conj` to transfer the nonzero-norm hypothesis to the
conjugate.

## Main structured iff

The public theorem is:

```text
traceOne_dvd_iff_norm_dvd_mul_conj_coordinates
```

For `hNorm : norm beta ≠ 0`, it proves:

```text
beta ∣ alpha ↔
  norm beta ∣ (alpha * conj beta).fst ∧
  norm beta ∣ (alpha * conj beta).snd
```

The forward theorem
`traceOne_dvd_imp_norm_dvd_mul_conj_coordinates` needs no nonzero-norm
hypothesis.  It writes `alpha = beta * q`, uses
`beta * conj beta = ofInt s (norm beta)`, and reads both coordinates.

The reverse theorem
`traceOne_dvd_of_norm_dvd_mul_conj_coordinates` obtains integer witnesses
`r,t`, reconstructs `q = ⟨r,t⟩`, proves

```text
alpha * conj beta = (beta * q) * conj beta
```

and cancels `conj beta` using the determinant cancellation theorem.

## Explicit polynomial iff

The corollary
`traceOne_dvd_iff_polynomial_norm_dvd_mul_conj_coordinates` exports:

```text
(c^2 + c*d - s*d^2) ≠ 0 ->
  (⟨c,d⟩ ∣ ⟨a,b⟩ ↔
    (c^2 + c*d - s*d^2) ∣ (a*c + a*d - s*b*d) ∧
    (c^2 + c*d - s*d^2) ∣ (b*c - a*d))
```

It is derived from the structured iff and the generic coordinate formulas.

## Norm-divisibility necessity

`traceOne_dvd_imp_norm_dvd_norm` proves, for every `s`:

```text
beta ∣ alpha -> norm beta ∣ norm alpha
```

This is obtained from norm multiplicativity.  No converse from norm
divisibility to element divisibility is claimed.

## Eisenstein specialization status

The approved MG-004A public theorem names and concrete nonzero-beta API remain
unchanged.  In addition,
`eisenstein_dvd_iff_norm_dvd_conjugate_coordinates_via_generic` checks the
generic theorem at `s = -1` using the existing convention
`eisensteinCoord a b = ⟨a,-b⟩`, and reproduces the approved coordinate
criterion.  The neutral facade import order is now:

```text
TraceOneQuadratic
  -> TraceOneLatticeLanding
  -> EisensteinCoordinates
  -> EisensteinLatticeLanding
```

No MultiGauge, ABC, FLT, Legendre, Petal, application bridge, or power-image
dependency was added.

## Zero-norm regression

`traceOne_zero_norm_nonzero` kernel-checks:

```text
norm (tau 0) = 0 ∧ tau 0 ≠ 0
```

This documents why the generic theorem requires `norm beta ≠ 0`.  No
classification of definite or anisotropic parameters was attempted.

## Validation

Commands were run from `lean/dk_math` on branch
`wip/number-theory-multi-gauge-divisibility-260914-v0`:

```text
lake build DkMath.Lib.NumberTheory.TraceOneLatticeLanding
lake build DkMath.Lib.NumberTheory.EisensteinLatticeLanding
lake build DkMath.Lib
git diff --check
```

The focused builds completed successfully with `8657`, `8659`, and `8669`
jobs respectively.  The final focused build output had no `warning:`
diagnostics attributable to the new modules.  The `#print axioms` output for
the new declarations contains only the existing logical/kernel foundations
(`propext`, `Classical.choice`, and `Quot.sound`); no `sorryAx` was introduced.

Changed Lean sources were scanned for `sorry`, `admit`, and new `axiom`
declarations; none were found.  `git diff --check` completed successfully.
The shell profile's `/opt/wonderful/bin/wf-env: Permission denied` message was
environmental noise and did not affect the builds.

## Scope deviations

The only source-path deviation is the nonexistent Lib path named in the
instruction; the actual carrier source under `DkMath/NumberTheory` was used.
The existing MG-004A criterion was not refactored in place, to preserve its
approved API and minimize churn; the generic specialization is an additional
regression theorem.

## MG-004C readiness

MG-004C is ready for an audit of power/Core-image landing over the generic
receiver.  MG-004B does not supply a power-image provider, prime-existence
theorem, Euclidean/UFD infrastructure, or any universal application bridge.
