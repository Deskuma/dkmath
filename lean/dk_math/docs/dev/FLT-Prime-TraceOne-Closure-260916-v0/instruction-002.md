# Instruction-002 — Arbitrary-power TraceOne coordinate kernel

## Working branch

Work only on:

```text
repository: Deskuma/dkmath
branch: research/FLT-Prime-TraceOne-Closure-260916-v0
```

Read first:

```text
README.md
AGENT.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/README.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/ROADMAP.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-000.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-001.md
lean/dk_math/DkMath/NumberTheory/TraceOneQuadratic.lean
lean/dk_math/DkMath/Lib/NumberTheory/TraceOnePowerLanding.lean
```

This checkpoint is deliberately narrow.

**Implement only the reusable integer-coordinate kernel for arbitrary natural
powers in `TraceOneInt s`. Do not yet implement the arbitrary-power landing
iff, FLT composition, class-number estimates, or a new FLT theorem.**

The mathematical carrier is already fixed:

```text
TraceOneInt s = { a + b*tau | tau^2 = tau + s }
```

with multiplication coordinates

```text
(a,b) * (m,n)
  = (a*m + s*b*n,
     a*n + b*m + b*n).
```

The purpose of FPTC-002 is to expose the coordinates of

```text
(<m,n> : TraceOneInt s)^r
```

as an exact recursive pair of integers, suitable for FPTC-003 and later FLT
receivers.

---

## 0. Repository-first API audit

Before editing production code, inspect the exact current declarations and
simp lemmas for:

```lean
TraceOneInt
TraceOneInt.fst
TraceOneInt.snd
traceOne_ext
fst_mul
snd_mul
fst_one
snd_one
traceOne_sq_coordinates
traceOne_norm_pow
traceOne_norm_eq_norm_mul_pow_of_eq
```

Also inspect current Lean 4.34 APIs for recursion on `Nat`, ordered pair
projections, and simplification of powers (`pow_zero`, `pow_succ`).

Do not assume theorem names from memory.

Create and maintain:

```text
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-002.md
```

The report must record:

- exact production API added;
- any failed design/API probes;
- whether a pair-valued recurrence or two scalar recurrences was chosen and
  why;
- focused build results;
- axiom audit output;
- explicit statement that FPTC-003 landing iff and FLT composition were not
  implemented here.

---

## 1. Coordinate recurrence design

Prefer the smallest transparent integer API.

A pair-valued recurrence is the preferred starting point, conceptually:

```lean
def traceOnePowCoords (s m n : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | r + 1 =>
      let (a, b) := traceOnePowCoords s m n r
      (a * m + s * b * n,
       a * n + b * m + b * n)
```

Exact naming and implementation may be adjusted to fit repository style.

Do not define the recurrence by simply taking

```lean
((<m,n> : TraceOneInt s)^r).fst
((<m,n> : TraceOneInt s)^r).snd
```

because that would make the coordinate theorem tautological and would not
expose an independent integer recurrence for later arithmetic use.

Likewise, do not introduce matrices, linear recurrences over a new abstract
semiring, closed-form diagonalization, roots of the characteristic polynomial,
or any new algebraic-number carrier.  Those are unnecessary for this
checkpoint.

Suggested status if the recurrence itself is clean:

```text
FPTC-TRACEONE-POWER-COORD-RECURRENCE-GREEN
```

---

## 2. Base and successor equations

Expose theorem-level equations for the recurrence sufficient for downstream
rewriting.

At minimum the API should make the following facts straightforward:

```text
coords 0 = (1,0)
coords (r+1) = multiplication-update(coords r, (m,n))
```

If the definition is recursive enough that these are definitional/simp facts,
add only the lemmas that materially improve use from other modules. Avoid a
large redundant theorem surface.

If separate coordinate functions are chosen instead, the mathematical
recurrences must be exactly:

```text
A_0 = 1
B_0 = 0

A_(r+1) = A_r*m + s*B_r*n
B_(r+1) = A_r*n + B_r*m + B_r*n.
```

---

## 3. Main arbitrary-power coordinate theorem

Prove the load-bearing theorem with conceptual content:

```lean
(<m,n> : TraceOneInt s)^r
  = <A_r(s,m,n), B_r(s,m,n)>.
```

For a pair-valued API, a preferred shape is similar to:

```lean
theorem traceOne_pow_coordinates (s m n : ℤ) (r : ℕ) :
    (⟨m, n⟩ : TraceOneInt s) ^ r =
      ⟨(traceOnePowCoords s m n r).1,
       (traceOnePowCoords s m n r).2⟩ := by
  ...
```

The proof should be a direct induction on `r` using the actual TraceOne
multiplication law.  It must not use an existential power-root provider or any
FLT theorem.

Suggested status:

```text
FPTC-TRACEONE-ARBITRARY-POWER-COORDINATES-GREEN
```

---

## 4. Small-exponent regressions

Prove/check the recurrence at least at exponents `0`, `1`, and `2`.

The exponent-two result must agree with the existing production theorem:

```lean
traceOne_sq_coordinates (s m n : ℤ) :
  (⟨m,n⟩ : TraceOneInt s)^2 =
    ⟨m^2 + s*n^2,
      2*m*n + n^2⟩
```

Do not delete or silently redefine `traceOne_sq_coordinates`.

Preferred regression content is either:

```text
traceOnePowCoords s m n 2
  = (m^2 + s*n^2, 2*m*n + n^2)
```

or an equivalent theorem showing that the new general coordinate theorem
specializes to the old square theorem.

The exact normal form may differ (`m*n + n*m + n^2`, etc.); use `ring` only
where mathematically appropriate.

Also include at least one concrete numeric specialization, suggested examples:

```text
s = -2, (m,n) = (...)
s = -1, (m,n) = (...)
```

The numeric regression is only to catch coordinate/order mistakes; do not turn
this checkpoint into an FLT3/FLT7 proof.

---

## 5. Norm compatibility

The existing theorem

```lean
traceOne_norm_pow (x : TraceOneInt s) (r : ℕ) :
  norm (x^r) = norm x ^ r
```

already gives the norm law.

Do not duplicate it.

Instead, if useful and genuinely small, add one corollary connecting the new
integer coordinates to the existing norm formula, conceptually:

```text
norm(<A_r,B_r>) = norm(<m,n>)^r.
```

This is optional in FPTC-002. Prefer reusing `traceOne_norm_pow` and the main
coordinate theorem rather than creating parallel norm machinery.

Do not begin FPTC-003 by multiplying with `conj beta` or proving a Core-image
landing iff here.

---

## 6. Location and public surface

Preferred implementation location:

```text
DkMath/Lib/NumberTheory/TraceOnePowerLanding.lean
```

because this module already owns:

```text
traceOne_sq_coordinates
traceOne_norm_pow
traceOne_norm_eq_norm_mul_pow_of_eq
traceOne_sq_core_landing_iff
```

If the coordinate recurrence becomes sufficiently self-contained that a
separate neutral module is clearly cleaner, record the reason in
`report-002.md`; otherwise avoid module proliferation.

Do not introduce imports from:

```text
DkMath.FLT.*
DkMath.ABC.*
```

into the neutral coordinate layer.

If `TraceOnePowerLanding` is already exported through the appropriate facade,
do not add redundant facade changes.

---

## 7. Focused API audit

Add or extend a focused test file, suggested:

```text
DkMathTest/Lib/NumberTheory/TraceOnePowerCoordinatesApiAudit.lean
```

It should `#check` the new recurrence and load-bearing theorem and include
small local examples confirming:

```text
r = 0
r = 1
r = 2
```

where `r = 2` agrees with `traceOne_sq_coordinates`.

The audit should also check that no stronger algebraic instance than the
existing `CommRing (TraceOneInt s)` is accidentally required.

---

## 8. Axiom audit and validation

Run focused builds first, adjusted to actual module names if needed:

```text
lake build DkMath.Lib.NumberTheory.TraceOnePowerLanding
lake build DkMathTest.Lib.NumberTheory.TraceOnePowerCoordinatesApiAudit
```

Add a focused axiom-audit file if that is repository convention, suggested:

```text
DkMathTest/Lib/NumberTheory/TraceOnePowerCoordinatesAxiomAudit.lean
```

Print axioms for at least:

```text
traceOne_pow_coordinates
```

and for the recurrence theorem if it is separate and load-bearing.

Then run:

```text
lake build DkMath.Lib
git diff --check
```

and the repository-standard forbidden-source scan.

New production/test sources must contain no new:

```text
sorry
sorryAx
admit
explicit axiom
unsafe
```

Standard Lean/Mathlib foundations such as `propext`, `Classical.choice`, and
`Quot.sound` are not by themselves a failure; report the actual output.

---

## 9. Outcome classification

Use exactly one primary outcome:

```text
Outcome A — ARBITRARY-POWER TRACEONE COORDINATE KERNEL GREEN
Outcome B — RECURRENCE GREEN, GENERAL POWER THEOREM/API NORMALIZATION REMAINS
Outcome C — CURRENT TRACEONE/LEAN API BLOCKS A CLEAN INTEGER RECURRENCE
```

Outcome A requires all of:

```text
- an explicit non-tautological integer recurrence for power coordinates;
- exact arbitrary-natural-power coordinate theorem;
- r=0/1/2 regression coverage;
- consistency with existing traceOne_sq_coordinates;
- focused build success;
- axiom audit;
- report-002.md;
- no FPTC-003 or FLT-specific theorem smuggled into the checkpoint.
```

---

## 10. Hard boundaries

Do not in checkpoint 002:

- prove the arbitrary-power analogue of `traceOne_sq_core_landing_iff`;
- compose with `PrimeTraceOneConditionalDescent`;
- prove any class-number/coprimality statement;
- modify the FPTC-000/001 class-group bridges except for a necessary Lean 4.34
  compatibility repair discovered by the build;
- eliminate real `Fin p` unit sectors;
- add p=3 or p=5 adapters;
- reopen q-adic `2m-global` descent;
- claim that coordinate formulas prove FLT;
- introduce a closed-form formula whose proof depends on square roots,
  eigenvalues, or an external algebraic extension.

The desired result is a small arithmetic kernel:

```text
TraceOne multiplication law
        ↓ repeated exactly r times
integer recurrence (A_r,B_r)
        ↓
(<m,n>)^r = <A_r,B_r>
```

FPTC-003 will consume this kernel to generalize the existing square/Core-image
landing criterion.