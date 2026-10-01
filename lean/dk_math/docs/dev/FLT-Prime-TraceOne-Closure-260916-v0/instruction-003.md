# Instruction-003 — Arbitrary-power TraceOne Core-image landing criterion

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
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-002.md
lean/dk_math/DkMath/Lib/NumberTheory/TraceOnePowerLanding.lean
lean/dk_math/DkMath/Lib/NumberTheory/TraceOneLatticeLanding.lean
```

This checkpoint is deliberately narrow.

The purpose is to generalize the existing square-only theorem

```lean
traceOne_sq_core_landing_iff
```

to an arbitrary natural exponent `r`, using the FPTC-002 recurrence
`traceOnePowCoords` and theorem `traceOne_pow_coordinates`.

Do not connect to FLT packets yet.  Do not prove any class-number statement,
unit-sector elimination, p=3/p=5 adapter, or general FLT theorem.

---

## 0. Repository-first audit

Before editing production code, record the exact current signatures/imports for:

```lean
traceOnePowCoords
traceOnePowCoords_zero
traceOnePowCoords_succ
traceOne_pow_coordinates
traceOne_sq_coordinates
traceOne_norm_pow
traceOne_norm_eq_norm_mul_pow_of_eq
traceOne_sq_core_landing_iff
traceOne_mul_conj
traceOne_norm_conj
traceOne_mul_right_cancel_of_norm_ne_zero
TraceOneInt.fst
TraceOneInt.snd
traceOne_ext
ofInt
conj
norm
```

Also confirm the current multiplication-by-scalar coordinate simplification for

```lean
ofInt s k * ⟨a,b⟩
```

and whether `simp` already closes the fst/snd projections after rewriting with
`traceOne_pow_coordinates`.

Create and maintain:

```text
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-003.md
```

The report must record exact declarations, any failed proof/API probes, the
chosen theorem statement, and validation results.

---

## 1. Main arbitrary-power landing theorem

Add a production theorem in the existing neutral module

```text
DkMath/Lib/NumberTheory/TraceOnePowerLanding.lean
```

with the conceptual statement:

```text
traceOne_pow_core_landing_iff
```

For arbitrary

```text
s : ℤ
alpha beta : TraceOneInt s
r : ℕ
```

and explicit hypothesis

```text
norm beta ≠ 0
```

prove an iff of the form

```lean
(∃ gamma : TraceOneInt s, alpha = beta * gamma ^ r) ↔
  ∃ m n : ℤ,
    (alpha * conj beta).fst =
      norm beta * (traceOnePowCoords s m n r).1 ∧
    (alpha * conj beta).snd =
      norm beta * (traceOnePowCoords s m n r).2
```

Use the actual repository namespace and notation conventions.

The theorem must be genuinely arbitrary in `r : ℕ`; do not add `0 < r`,
primality, oddness, or FLT-specific assumptions unless the kernel proof truly
requires them.  Mathematically the criterion should also cover `r = 0` and
`r = 1`.

Suggested status:

```text
FPTC-TRACEONE-ARBITRARY-POWER-LANDING-IFF-GREEN
```

---

## 2. Forward direction

The forward direction should reuse the existing algebraic identity rather than
reprove a special coordinate calculation.

From

```text
alpha = beta * gamma^r
```

with `gamma = ⟨m,n⟩`, derive

```text
alpha * conj beta
  = (beta * conj beta) * gamma^r
  = ofInt s (norm beta) * gamma^r.
```

Then rewrite `gamma^r` using

```lean
traceOne_pow_coordinates
```

and extract fst/snd equalities.

Do not expand the recursive coordinate definition by induction inside the
landing theorem.  FPTC-002 already owns that proof.

---

## 3. Reverse direction

Given integer witnesses `m n` satisfying the two coordinate equalities, set

```lean
let gamma : TraceOneInt s := ⟨m,n⟩
```

and reconstruct the element equality

```text
ofInt s (norm beta) * gamma^r = alpha * conj beta
```

using `traceOne_pow_coordinates` and `traceOne_ext`.

Then rewrite

```text
ofInt s (norm beta) = beta * conj beta
```

via the existing norm/conjugation theorem and commute/reassociate to obtain

```text
alpha * conj beta = (beta * gamma^r) * conj beta.
```

Use the existing cancellation theorem

```lean
traceOne_mul_right_cancel_of_norm_ne_zero
```

with the norm of `conj beta` to conclude

```text
alpha = beta * gamma^r.
```

Do not introduce a field of fractions or divide by `norm beta`; the existing
integral cancellation layer is the intended proof route.

---

## 4. Regression against the square theorem

The existing theorem

```lean
traceOne_sq_core_landing_iff
```

must remain unchanged unless a very small refactor is clearly beneficial.

Add focused tests showing that the new arbitrary-power theorem at `r = 2`
produces the same coordinate condition as the existing square theorem.

At minimum verify the recurrence normalization

```text
traceOnePowCoords s m n 2
  = (m^2 + s*n^2, 2*m*n + n^2)
```

and demonstrate that the new theorem specializes to the old square image.

Preferred policy:

```text
- keep the old theorem as a stable public theorem;
- optionally reprove it as a short corollary of the new theorem only if this
  materially reduces duplication and does not complicate simp/rewrite behavior.
```

Do not delete or rename the old theorem.

---

## 5. Small-exponent edge regressions

Add focused API/test examples for `r = 0` and `r = 1`.

These are important because the main theorem is quantified over all `ℕ`.

Check that the theorem behaves mathematically as expected:

```text
r = 0:
  alpha = beta * 1
  ↔ coordinate image of (1,0)

r = 1:
  alpha = beta * gamma
  ↔ coordinate image of (m,n)
```

Do not impose a positivity assumption merely to avoid these cases.

---

## 6. Optional useful corollary

If genuinely tiny and useful, add a one-way receiver theorem with an already
supplied factorization:

```text
alpha = beta * gamma^r
  -> exact fst/snd coordinate equations for gamma
```

However, do not duplicate the iff theorem under several cosmetic names.
The iff theorem is the load-bearing API.

No existential power-root provider should be added.

---

## 7. Scope boundary toward FPTC-004

Do not import any `DkMath.FLT.*` module into the neutral production file.

In particular do not yet compose with:

```lean
DkMath.FLT.Prime.exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket
DkMath.FLT.Prime.exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket_seven
```

FPTC-003 ends when the neutral algebraic factorization

```text
alpha = beta * gamma^r
```

has been converted to and from exact integer recurrence coordinates.

The FLT residual consumer belongs to FPTC-004.

---

## 8. Focused tests and audit files

Add focused tests, suggested names:

```text
DkMathTest/Lib/NumberTheory/TraceOnePowerLandingApiAudit.lean
DkMathTest/Lib/NumberTheory/TraceOnePowerLandingAxiomAudit.lean
```

The API audit should check:

```text
- theorem signature for arbitrary r;
- r=0 regression;
- r=1 regression;
- r=2 / square compatibility;
- at least one concrete s=-2 or s=-1 numeric example;
- no FLT-specific typeclass/import requirement.
```

Print axioms for the load-bearing theorem.

Existing Lean axioms such as `propext`, `Classical.choice`, or `Quot.sound` are
not by themselves failures.  Record exact output.

---

## 9. Validation

Run at least:

```text
lake build DkMath.Lib.NumberTheory.TraceOnePowerLanding
lake build DkMathTest.Lib.NumberTheory.TraceOnePowerLandingApiAudit
lake build DkMathTest.Lib.NumberTheory.TraceOnePowerLandingAxiomAudit
lake build DkMath.Lib
```

Also run:

```text
git diff --check
```

and the repository-standard forbidden-source scan over newly edited production
and test files.

No new:

```text
sorry
sorryAx
admit
explicit axiom
unsafe
```

may be introduced.

---

## 10. Outcome classification

Use exactly one primary outcome:

```text
Outcome A — ARBITRARY-POWER TRACEONE LANDING IFF GREEN
Outcome B — FORWARD COORDINATE RECEIVER GREEN, REVERSE CANCELLATION/API GAP REMAINS
Outcome C — EXISTING CANCELLATION/COORDINATE API DOES NOT SUPPORT A CLEAN IFF
```

Outcome A requires all of:

```text
- arbitrary-r iff theorem in neutral production code;
- explicit nonzero norm hypothesis only where needed for reverse cancellation;
- FPTC-002 recurrence reused rather than reimplemented;
- r=0,1,2 regressions;
- compatibility with existing square theorem;
- focused build success;
- axiom audit and forbidden-source audit;
- report-003.md.
```

---

## 11. Hard boundaries

Do not in checkpoint 003:

- compose with FLT Prime packets;
- claim impossibility of any coordinate image;
- prove class-number or coprimality results;
- eliminate real `Fin p` unit sectors;
- add p=3 or p=5 carrier adapters;
- reopen q-adic `2m-global` descent;
- introduce matrix/eigenvalue/closed-form machinery for `traceOnePowCoords`;
- require `r` to be prime or positive without a genuine proof-theoretic need;
- replace the recurrence by projections of the already-computed ring power.

The desired checkpoint result is a clean, reusable equivalence:

```text
algebraic Core-image membership
        <->
exact integer recurrence-coordinate landing.
```

That equivalence is the handoff surface for FPTC-004.
