# MG-004C TraceOne power/Core-image landing

## Outcome

**Outcome A — CORE LANDING ESTABLISHED**

The generic `TraceOneInt s` receiver now has an exact square/Core-image
criterion under the direct hypothesis `norm beta ≠ 0`.  The theorem is a
coordinate criterion for an already quantified square witness; it does not
provide square roots or any other power-existence theorem.

## Files changed

Added:

```text
DkMath/Lib/NumberTheory/TraceOnePowerLanding.lean
docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/report-008.md
```

Updated:

```text
DkMath/Lib.lean
docs/dev/NumberTheory-MultiGauge-Divisibility-260914-v0/ROADMAP.md
```

The existing lattice and Eisenstein modules were not refactored.  Existing
FLT5/FLT7/ABC/Petal power-related packets were audited by source search for
overlap; their application-owned theorems remain outside `DkMath.Lib`.

## Square-coordinate formula

The new theorem is:

```text
traceOne_sq_coordinates (s m n : ℤ) :
  (⟨m,n⟩ : TraceOneInt s)^2 =
    ⟨m^2 + s*n^2, 2*m*n + n^2⟩
```

It uses the existing `TraceOneInt` multiplication and `pow_two`; no second
multiplication API was introduced.

## Square/Core coordinate iff

The primary theorem is:

```text
traceOne_sq_core_landing_iff
  {s : ℤ} {alpha beta : TraceOneInt s}
  (hNorm : norm beta ≠ 0) :
  (∃ gamma, alpha = beta * gamma^2) ↔
    ∃ m n : ℤ,
      (alpha * conj beta).fst = norm beta * (m^2 + s*n^2) ∧
      (alpha * conj beta).snd = norm beta * (2*m*n + n^2)
```

The forward direction expands an existing `gamma = ⟨m,n⟩`, multiplies by the
conjugate, and reads the two coordinates of
`ofInt s (norm beta) * gamma^2`.  The reverse direction reconstructs
`gamma = ⟨m,n⟩`, proves the corresponding conjugate-product equality, and
cancels `conj beta` with the MG-004B theorem
`traceOne_mul_right_cancel_of_norm_ne_zero`.

No field quotient, UFD/PID structure, or root provider is used.

## Arbitrary-power receiver

The optional existential arbitrary-`r` receiver was not added.  It was not
needed for Outcome A and would add only a second quantified rewrite layer to
the primary square criterion.  The neutral norm helper
`traceOne_norm_pow` is generic in `r : ℕ`, and the factorization theorem
`traceOne_norm_eq_norm_mul_pow_of_eq` records the corresponding norm identity
for an already supplied equality `alpha = beta * gamma^r`.

The square specialization is also exposed as
`traceOne_norm_eq_norm_mul_sq_of_eq`.

## Norm consequences

For arbitrary `r : ℕ`:

```text
traceOne_norm_pow (x : TraceOneInt s) (r : ℕ) :
  norm (x^r) = norm x ^ r
```

and, when `alpha = beta * gamma^r`:

```text
norm alpha = norm beta * (norm gamma)^r
```

For `r = 2`, this gives the necessary square-norm identity only.  No claim
that a square norm implies square/Core landing is made.

## Strict lattice-vs-Core regression

The theorem `traceOne_lattice_landing_not_square` kernel-checks at `s = 0`:

```text
1 ∣ (⟨2,0⟩ : TraceOneInt 0)
and
¬ ∃ gamma : TraceOneInt 0,
    ⟨2,0⟩ = 1 * gamma^2
```

The non-square conclusion reduces the first square coordinate to `m^2 = 2`
and discharges the integer cases arithmetically.  This records the strict
chain from integral lattice landing to square/Core-image landing.

## Dependencies and scope

The dependency direction is:

```text
TraceOneQuadratic
  -> TraceOneLatticeLanding
  -> TraceOnePowerLanding
```

`DkMath.Lib` exports the new neutral module.  No MultiGauge, ABC, FLT, Petal,
Legendre, PrimorialUniverse, Euclidean-domain, UFD/PID, analytic, or
prime-existence dependency was added.  No optional Eisenstein specialization
was needed because the generic square theorem is already the requested
receiver layer and existing Eisenstein square APIs remain stable.

## Validation

Commands were run from `lean/dk_math` on branch
`wip/number-theory-multi-gauge-divisibility-260914-v0`:

```text
lake build DkMath.Lib.NumberTheory.TraceOnePowerLanding
lake build DkMath.Lib.NumberTheory.TraceOneLatticeLanding
lake build DkMath.Lib.NumberTheory.EisensteinLatticeLanding
lake build DkMath.Lib
git diff --check
```

The focused builds completed successfully with `8658`, `8657`, `8659`, and
`8670` jobs respectively.  The final builds emitted no `warning:` diagnostics
from the new module.  The `#print axioms` output for the new declarations
contains only existing logical/kernel foundations (`propext`,
`Classical.choice`, and `Quot.sound`); no `sorryAx` was introduced.

Changed Lean sources were scanned for `sorry`, `admit`, and new `axiom`
declarations; none were found.  `git diff --check` completed successfully.
The shell profile's `/opt/wonderful/bin/wf-env: Permission denied` message was
environmental noise and did not affect the builds.
