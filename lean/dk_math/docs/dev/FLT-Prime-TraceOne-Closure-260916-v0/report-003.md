# FPTC-003 report — arbitrary-power TraceOne Core-image landing

## Outcome

```text
Outcome A — ARBITRARY-POWER TRACEONE LANDING IFF GREEN
```

The square-only Core-image criterion has been generalized to every natural
exponent `r`, using the FPTC-002 integer recurrence and coordinate theorem.
The reverse direction uses the existing integral cancellation theorem and does
not introduce a field of fractions or division by `norm beta`.

FPTC-004 FLT packet composition, class-number statements, unit-sector
elimination, and general FLT claims were not implemented.

## Repository and scope audit

Work was performed on
`research/FLT-Prime-TraceOne-Closure-260916-v0`.  The attached instruction was
treated as the bounded implementation contract, separate from the user's
request.  The existing TraceOne carrier, lattice landing layer, FPTC-002
report, and current `TraceOnePowerLanding` APIs were read before editing.

The neutral dependency direction remains unchanged.  The production module
imports `DkMath.Lib.NumberTheory.TraceOneLatticeLanding` and imports no
`DkMath.FLT.*` or `DkMath.ABC.*` module.

## Exact API audit

The focused audit file is
`DkMathTest/Lib/NumberTheory/TraceOnePowerLandingApiAudit.lean`.  Its current
Lean 4.34 output confirms:

```text
traceOnePowCoords (s m n : ℤ) : ℕ → ℤ × ℤ
traceOnePowCoords_zero (s m n : ℤ) : traceOnePowCoords s m n 0 = (1, 0)
traceOnePowCoords_succ (s m n : ℤ) (r : ℕ) :
  traceOnePowCoords s m n (r + 1) =
    ((traceOnePowCoords s m n r).1 * m +
       s * (traceOnePowCoords s m n r).2 * n,
     (traceOnePowCoords s m n r).1 * n +
       (traceOnePowCoords s m n r).2 * m +
       (traceOnePowCoords s m n r).2 * n)

traceOne_pow_coordinates (s m n : ℤ) (r : ℕ) :
  (⟨m, n⟩ : TraceOneInt s) ^ r =
    ⟨(traceOnePowCoords s m n r).1,
     (traceOnePowCoords s m n r).2⟩

traceOne_sq_coordinates (s m n : ℤ) :
  (⟨m, n⟩ : TraceOneInt s) ^ 2 =
    ⟨m ^ 2 + s * n ^ 2, 2 * m * n + n ^ 2⟩

traceOne_norm_pow (x : TraceOneInt s) (r : ℕ) :
  norm (x ^ r) = norm x ^ r

traceOne_norm_eq_norm_mul_pow_of_eq
traceOne_sq_core_landing_iff
```

The existing algebraic declarations used by the landing proof are:

```text
traceOne_mul_conj {x : TraceOneInt s} :
  x * conj x = ofInt s (norm x)

traceOne_norm_conj (s : ℤ) (z : TraceOneInt s) :
  norm (conj z) = norm z

traceOne_mul_right_cancel_of_norm_ne_zero
  (hz : norm z ≠ 0) (h : x * z = y * z) : x = y

TraceOneInt.fst : TraceOneInt s → ℤ
TraceOneInt.snd : TraceOneInt s → ℤ
traceOne_ext : x.fst = y.fst → x.snd = y.snd → x = y
ofInt (s a : ℤ) : TraceOneInt s
conj (x : TraceOneInt s) : TraceOneInt s
```

The audit confirms the current power APIs:

```text
pow_zero (a : M) : a ^ 0 = 1
pow_succ (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a
pow_two (a : M) : a ^ 2 = a * a
Prod.fst : α × β → α
Prod.snd : α × β → β
```

The explicit qualified declaration
`DkMath.NumberTheory.TraceOneQuadratic.norm` has type
`TraceOneInt s → ℤ`.  An unqualified `#check norm` also sees the generic
`Norm.norm` declaration, so the production module uses the local `traceNorm`
notation to avoid that namespace collision.

The scalar coordinate simplification is direct:

```text
(ofInt s k * (⟨a, b⟩ : TraceOneInt s)).fst = k * a
(ofInt s k * (⟨a, b⟩ : TraceOneInt s)).snd = k * b
```

Both are closed by `simp [ofInt]`.  After rewriting with
`traceOne_pow_coordinates`, the corresponding scalar-coordinate goals in the
landing proof are also closed by `simpa [ofInt]` against the supplied witness
equalities.

## Implemented theorem

The production theorem is in
`DkMath/Lib/NumberTheory/TraceOnePowerLanding.lean`:

```lean
theorem traceOne_pow_core_landing_iff
    {s : ℤ} {alpha beta : TraceOneInt s} {r : ℕ}
    (hNorm : norm beta ≠ 0) :
    (∃ gamma : TraceOneInt s, alpha = beta * gamma ^ r) ↔
      ∃ m n : ℤ,
        (alpha * conj beta).fst =
            norm beta * (traceOnePowCoords s m n r).1 ∧
          (alpha * conj beta).snd =
            norm beta * (traceOnePowCoords s m n r).2
```

The only explicit hypothesis needed for the reverse cancellation is
`norm beta ≠ 0`; `r` is unrestricted and may be `0`, `1`, or any other natural
number.

### Forward direction

From `alpha = beta * gamma ^ r`, the proof destructures
`gamma = ⟨m,n⟩` and derives:

```text
alpha * conj beta
  = (beta * conj beta) * gamma^r
  = ofInt s (norm beta) * gamma^r.
```

It then rewrites `gamma^r` once with
`traceOne_pow_coordinates` and extracts the two projections.  The recurrence
is not re-proved or unfolded by induction here.

### Reverse direction

Given integer witnesses, the proof sets
`gamma := ⟨m,n⟩` and reconstructs

```text
ofInt s (norm beta) * gamma^r = alpha * conj beta
```

using `traceOne_pow_coordinates`, `traceOne_ext`, and the scalar projection
simplifications.  It rewrites `ofInt s (norm beta)` using
`traceOne_mul_conj`, reassociates to
`(beta * gamma^r) * conj beta`, and applies
`traceOne_mul_right_cancel_of_norm_ne_zero`.  The required nonzero condition
for `conj beta` follows from `traceOne_norm_conj` and `hNorm`.

No field of fractions, division, matrix, eigenvalue, closed form, power-root
provider, or FLT theorem is used.

## Regression coverage

The focused API audit checks the new theorem at `r = 0`, `r = 1`, and `r = 2`.
It also retains the old square theorem as a separate stable API and checks the
same square coordinate normalization:

```text
traceOnePowCoords s m n 2
  = (m^2 + s*n^2, 2*m*n + n^2)

traceOne_sq_core_landing_iff
  gives the existing square coordinate condition.
```

Concrete recurrence regressions are:

```text
traceOnePowCoords (-2) 1 1 2 = (-1, 3)
traceOnePowCoords (-1) 1 2 2 = (-3, 8)
```

The old `traceOne_sq_core_landing_iff` was not deleted, renamed, or rewritten;
the new theorem is the arbitrary-power load-bearing API.

## Failed probes and design decisions

No failed production proof/API build remained.  The only namespace observation
was that unqualified `norm` resolves to the generic `Norm.norm` in a standalone
`#check`; the audit therefore records and uses the fully qualified TraceOne
norm declaration, while production uses `traceNorm`.

A pair-valued recurrence from FPTC-002 was reused exactly as intended.  No
second scalar recurrence, matrix layer, or closed-form representation was
introduced.  The reverse proof deliberately uses the existing cancellation
layer instead of attempting to divide by the norm.

## Axiom audit

The focused axiom audit file is
`DkMathTest/Lib/NumberTheory/TraceOnePowerLandingAxiomAudit.lean`.  Its exact
result is:

```text
traceOne_pow_core_landing_iff depends on axioms:
[propext, Classical.choice, Quot.sound]
```

No DkMath-defined axiom, `sorry`, `sorryAx`, `admit`, or `unsafe` was added.

## Validation

Successful builds under Lean 4.34:

```text
lake build DkMath.Lib.NumberTheory.TraceOnePowerLanding
lake build DkMathTest.Lib.NumberTheory.TraceOnePowerLandingApiAudit
lake build DkMathTest.Lib.NumberTheory.TraceOnePowerLandingAxiomAudit
lake build DkMath.Lib
```

`git diff --check` completed with no diagnostics.  No-index checks for the new
untracked audit/report files also produced no whitespace diagnostics.  The
repository-standard forbidden-source scan over the edited production and test
Lean files found no forbidden declaration.

## Explicit boundary and next frontier

The result now available is the neutral equivalence:

```text
algebraic Core-image membership
        <->
exact integer recurrence-coordinate landing.
```

This checkpoint does not claim that any coordinate image is impossible and
does not connect to `PrimeTraceOneConditionalDescent` or either p=7 generic
endpoint.  Those consumers belong to FPTC-004.  Class-number/coprimality
results, real-sector elimination, p=3/p=5 adapters, q-adic global descent,
and general FLT remain unproved.
