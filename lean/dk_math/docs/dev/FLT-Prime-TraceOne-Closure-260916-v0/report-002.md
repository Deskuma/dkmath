# FPTC-002 report — arbitrary-power TraceOne coordinate kernel

## Outcome

```text
Outcome A — ARBITRARY-POWER TRACEONE COORDINATE KERNEL GREEN
```

The reusable integer pair recurrence and the exact arbitrary-natural-power
coordinate theorem are implemented and kernel-checked under Lean 4.34.
FPTC-003 landing iff, FLT composition, and all arithmetic closure claims remain
outside this checkpoint.

## Repository and scope audit

The implementation was made on
`research/FLT-Prime-TraceOne-Closure-260916-v0`, at commit `496262040` when
this report was prepared.  Lake builds were run from
`/home/deskuma/develop/lean/dkmath/lean/dk_math`.

The checkpoint instruction was treated as the bounded implementation contract,
separate from the user's request.  The existing `TraceOneInt` carrier,
`TraceOnePowerLanding` module, FPTC-000 class-group bridge, and FPTC-001 report
were inspected before editing.  The neutral dependency direction was
preserved: the production module imports `TraceOneLatticeLanding` and no
`DkMath.FLT.*` or `DkMath.ABC.*` module.

## API audit

The focused audit file is
`DkMathTest/Lib/NumberTheory/TraceOnePowerCoordinatesApiAudit.lean`.  Its
`#check` output confirmed the current declarations:

```text
TraceOneInt (s : ℤ) : Type
TraceOneInt.fst : TraceOneInt s → ℤ
TraceOneInt.snd : TraceOneInt s → ℤ
traceOne_ext : x.fst = y.fst → x.snd = y.snd → x = y
fst_mul : (x * y).fst = x.fst * y.fst + s * x.snd * y.snd
snd_mul : (x * y).snd = x.fst * y.snd + x.snd * y.fst + x.snd * y.snd
fst_one : (1 : TraceOneInt s).fst = 1
snd_one : (1 : TraceOneInt s).snd = 0
traceOne_sq_coordinates
traceOne_norm_pow
traceOne_norm_eq_norm_mul_pow_of_eq
```

The existing power simplification APIs `pow_zero`, `pow_succ`, and `pow_two`
were used through the current `CommRing (TraceOneInt s)` instance.  The audit
also confirms that the coordinate theorem requires no Euclidean, field,
Dedekind, number-field, or FLT-specific instance; `#synth CommRing
(TraceOneInt 0)` succeeds, and the theorem's only carrier algebra is the
existing general `TraceOneInt s` ring.

## Implemented production API

The production location is
`DkMath/Lib/NumberTheory/TraceOnePowerLanding.lean`.  The new public
pair-valued recurrence is:

```lean
def traceOnePowCoords (s m n : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | r + 1 =>
      let (a, b) := traceOnePowCoords s m n r
      (a * m + s * b * n,
       a * n + b * m + b * n)
```

The exposed equations are:

```lean
traceOnePowCoords_zero (s m n : ℤ) :
  traceOnePowCoords s m n 0 = (1, 0)

traceOnePowCoords_succ (s m n : ℤ) (r : ℕ) :
  traceOnePowCoords s m n (r + 1) =
    ((traceOnePowCoords s m n r).1 * m +
       s * (traceOnePowCoords s m n r).2 * n,
     (traceOnePowCoords s m n r).1 * n +
       (traceOnePowCoords s m n r).2 * m +
       (traceOnePowCoords s m n r).2 * n)
```

The load-bearing arbitrary-power theorem is:

```lean
theorem traceOne_pow_coordinates (s m n : ℤ) (r : ℕ) :
    (⟨m, n⟩ : TraceOneInt s) ^ r =
      ⟨(traceOnePowCoords s m n r).1,
       (traceOnePowCoords s m n r).2⟩
```

The proof is direct induction on `r`.  The zero case identifies the ring one
with the coordinate pair `(1, 0)`.  The successor case rewrites with
`pow_succ`, applies the induction hypothesis, and closes the two coordinate
goals using the actual `fst_mul`/`snd_mul` multiplication law and integer
normalization.  No existential power-root provider, matrix, closed form,
eigenvalue, or external algebraic carrier is used.

A pair-valued recurrence was chosen because it mirrors the fixed TraceOne
multiplication law in one transparent definition.  It keeps the two scalar
coordinates synchronized and gives downstream users a single integer object
whose projections are the exact coordinates, without making the theorem a
tautological projection of `((⟨m,n⟩)^r).fst` and `.snd`.

## Small-exponent and numeric regressions

The focused audit checks the recurrence at exponents 0, 1, and 2:

```text
traceOnePowCoords s m n 0 = (1, 0)
traceOnePowCoords s m n 1 = (m, n)
traceOnePowCoords s m n 2 =
  (m^2 + s*n^2, 2*m*n + n^2)
```

It separately checks the main theorem at `r = 0`, `r = 1`, and `r = 2`.  The
existing production theorem `traceOne_sq_coordinates` is retained unchanged
and is checked at exponent two against the same square coordinate expression.
Concrete arithmetic regressions are also included:

```text
traceOnePowCoords (-2) 1 1 2 = (-1, 3)
traceOnePowCoords (-1) 1 2 2 = (-3, 8)
```

These tests are coordinate/order checks only; they do not invoke FLT3, FLT7,
class-group hypotheses, or any landing theorem.

## Norm and landing boundary

The existing `traceOne_norm_pow` theorem remains the norm API and was not
duplicated.  No new norm machinery or optional coordinate/norm corollary was
needed.  In particular, this checkpoint does not multiply by `conj beta`,
prove a Core-image landing iff, or introduce an arbitrary-power root provider.

The existing square-specific declarations remain in place:

```text
traceOne_sq_coordinates
traceOne_sq_core_landing_iff
```

The arbitrary-power landing iff is explicitly deferred to FPTC-003.

## Failed probes and repairs

The first production build exposed two local Lean 4.34 proof-shape issues:

1. In the zero induction case, `simp [traceOnePowCoords]` left the structural
   equality `1 = { fst := 1, snd := 0 }`.  The proof now uses an explicit
   `change (⟨1, 0⟩ : TraceOneInt s) = ⟨1, 0⟩` followed by `rfl`.
2. In the successor case, `simp [traceOnePowCoords]` closed both coordinate
   goals, so subsequent `ring` bullets produced `No goals to be solved`.
   The redundant bullets were removed.

No production API redesign or stronger assumption was required after these
repairs.

## Axiom audit

The focused axiom audit file is
`DkMathTest/Lib/NumberTheory/TraceOnePowerCoordinatesAxiomAudit.lean`.
Its output is:

```text
traceOnePowCoords_succ does not depend on any axioms
traceOne_pow_coordinates depends on axioms: [propext]
```

The `propext` dependency is inherited from the existing `TraceOneInt` ring
proof layer; no DkMath-defined axiom, `sorryAx`, `sorry`, `admit`, or `unsafe`
was introduced.

## Validation

Successful focused builds:

```text
lake build DkMath.Lib.NumberTheory.TraceOnePowerLanding
lake build DkMathTest.Lib.NumberTheory.TraceOnePowerCoordinatesApiAudit
lake build DkMathTest.Lib.NumberTheory.TraceOnePowerCoordinatesAxiomAudit
lake build DkMath.Lib
```

The final builds completed successfully under Lean 4.34.  `git diff --check`
and no-index whitespace checks for the new untracked files produced no
diagnostics.  The repository-standard forbidden-source scan over the new
production and test files found no forbidden `sorry`, `sorryAx`, `admit`,
explicit `axiom`, or `unsafe` declaration.

## Explicit non-goals and remaining frontier

FPTC-003 landing iff and all FLT-specific composition were not implemented in
this checkpoint.  Also not implemented are class-number/coprimality results,
real-sector elimination, p=3/p=5 adapters, q-adic global descent, and any
general FLT theorem.

The reusable result now available is:

```text
TraceOne multiplication law
        -> integer pair recurrence (A_r, B_r)
        -> (<m,n> : TraceOneInt s)^r = <A_r, B_r>
```

The next bounded consumer is FPTC-003, which may use this coordinate kernel to
develop an arbitrary-power landing criterion while retaining its own explicit
nonzero-norm and factorization hypotheses.
