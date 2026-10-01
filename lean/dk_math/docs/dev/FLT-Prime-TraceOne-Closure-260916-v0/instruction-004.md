# Instruction-004 — Generic imaginary residual coordinate receiver

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
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-003.md
lean/dk_math/docs/refact/FLT-Prime-Generalization-260911-v0/summary-026.md
```

Inspect at least:

```text
DkMath/Lib/NumberTheory/TraceOnePowerLanding.lean
DkMath/FLT/Prime/PrimeTraceOneConditionalDescent.lean
DkMath/FLT/Prime/PrimeTraceOneClassGroupClosure.lean
DkMath/FLT/Prime/PrimeTraceOneStrippedIdeal.lean
DkMath/NumberTheory/PrimeQuadraticDiscriminant.lean
```

This checkpoint is the first FLT consumer of the neutral FPTC-002/003 coordinate machinery.

**Do not attempt the final FLT contradiction, general class-number coprimality,
real-sector elimination, p=3/p=5 adapters, or generic counterexample routing.**

The purpose is only to convert the existing generic imaginary residual exact-power
endpoint into exact integer coordinate equations.

---

## 0. Repository-first API audit

Before editing production code, record the exact current signatures/imports of:

```lean
DkMath.Lib.NumberTheory.traceOnePowCoords
DkMath.Lib.NumberTheory.traceOne_pow_coordinates
DkMath.Lib.NumberTheory.traceOne_pow_core_landing_iff

DkMath.FLT.Prime.exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket
DkMath.FLT.Prime.exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket_seven
DkMath.FLT.Prime.classGroupPTorsionFreeAt_traceOneNegTwo_seven
```

Also inspect the fields available on:

```lean
PrimeTraceOneStrippedIdealPacket
Q.residual
```

and verify simplification behavior for:

```lean
(1 : TraceOneInt s)
conj (1 : TraceOneInt s)
norm (1 : TraceOneInt s)
1 * gamma ^ p
```

Create and maintain:

```text
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-004.md
```

The report must list exact theorem signatures, import direction, failed probes,
and whether the intended `beta = 1` specialization simplifies cleanly.

---

## 1. Focused API audit test

Add a focused test, suggested:

```text
DkMathTest/FLT/Prime/PrimeTraceOneImaginaryCoordinateReceiverApiAudit.lean
```

Use `#check` and local examples to verify:

1. FPTC-003 can be specialized with `beta = 1` and `r = p`.
2. The nonzero-norm hypothesis for `beta = 1` is discharged without additional
   field/Dedekind assumptions.
3. The resulting two coordinate equations simplify to the raw coordinates of
   `alpha` rather than leaving `alpha * conj 1` or `norm 1` noise.
4. The generic imaginary endpoint and the p=7 class-group-closed endpoint can
   feed that specialization without rebuilding ideal or unit arguments.

Keep exploratory examples in the test layer only.

---

## 2. Generic conditional coordinate receiver

Add an FLT-side theorem in the nearest existing generic prime module, or a new
small module if that gives a cleaner dependency boundary.

Preferred conceptual theorem:

```text
PrimeTraceOneStrippedIdealPacket
p >= 7
p % 4 = 3
classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p
  ->
exists m n : Z,
  Q.residual.fst = (traceOnePowCoords (signedPrimeParameter p) m n p).1
  and
  Q.residual.snd = (traceOnePowCoords (signedPrimeParameter p) m n p).2
```

A suggested name is:

```lean
exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket
```

but follow current repository naming conventions if another name is clearer.

### Required proof architecture

Do not duplicate the Phase-26 ideal/class-group/unit proof.

Use:

```text
exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket
        ↓
exists delta, Q.residual = delta ^ p
        ↓
traceOne_pow_core_landing_iff with beta = 1, r = p
        ↓
integer witnesses m,n and exact residual coordinate equations
```

The FPTC-003 theorem should be a real load-bearing dependency here.  Do not
bypass it with a fresh ad hoc coordinate proof unless a concrete Lean API issue
forces that choice; if so, stop and report the mismatch before redesigning.

Do not introduce division or a fraction field.

Suggested status:

```text
FPTC-IMAGINARY-GENERIC-COORDINATE-RECEIVER-GREEN
```

---

## 3. p=7 unconditional class-group regression

Compose the new generic coordinate receiver with the FPTC-000 p=7 structural
class-group discharge.

Target conceptual content:

```text
PrimeTraceOneStrippedIdealPacket at p = 7
  ->
exists m n : Z,
  Q.residual.fst = (traceOnePowCoords (-2) m n 7).1
  and
  Q.residual.snd = (traceOnePowCoords (-2) m n 7).2
```

The actual theorem may retain `signedPrimeParameter 7` in its statement if that
avoids unnecessary casts, but the audit must explicitly verify:

```text
signedPrimeParameter 7 = -2
```

This theorem must not require a caller-supplied class-group hypothesis and must
not call the specialized FLT7 final contradiction theorem.

Prefer composing the existing theorem:

```lean
exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket_seven
```

or the new generic receiver plus
`classGroupPTorsionFreeAt_traceOneNegTwo_seven`, whichever gives the thinnest
proof without duplicating work.

Suggested status:

```text
FPTC-P7-IMAGINARY-COORDINATE-RECEIVER-GREEN
```

---

## 4. p=11 conditional regression

Add a focused regression at `p = 11` to demonstrate that the generic receiver
is not accidentally specialized to the Euclidean p=7 carrier.

Audit explicitly:

```text
11 % 4 = 3
signedPrimeParameter 11 = -3
```

The regression may and should retain the explicit assumption:

```lean
classGroupPTorsionFreeAt (TraceOneInt (-3)) 11
```

unless an already-existing theorem discharges it.  Do **not** prove or assume a
new class-number fact merely to make this regression unconditional.

The desired conclusion is the corresponding exponent-11 recurrence-coordinate
landing for `Q.residual`.

Suggested status:

```text
FPTC-P11-CONDITIONAL-COORDINATE-RECEIVER-GREEN
```

---

## 5. Consumer-shape audit

The purpose of this checkpoint is not merely to restate `Q.residual = delta^p`.
Record in `report-004.md` what additional information the coordinate receiver
makes directly available to later arithmetic arguments.

At minimum record:

```text
Q.residual.fst = A_p(s,m,n)
Q.residual.snd = B_p(s,m,n)
```

where `(A_p,B_p) = traceOnePowCoords s m n p`.

Then inspect, without implementing the next contradiction step, which existing
fields/theorems about `Q.residual` or the stripped packet constrain:

```text
residual.fst
residual.snd
norm residual
primitive/coprime coordinates
discriminant-axis stripping
```

This is an audit only.  Do not invent a contradiction or promote an observed
pattern to a theorem in FPTC-004.

If the packet already contains especially strong coordinate information that
could consume the new equations, list the exact declarations/files in the
report for the next checkpoint.

---

## 6. Module and dependency boundary

The neutral layer must remain one-way:

```text
DkMath.Lib.NumberTheory.TraceOnePowerLanding
        ↓
DkMath.FLT.Prime.* coordinate receiver
```

Never introduce:

```text
DkMath.Lib.NumberTheory -> DkMath.FLT.Prime
```

If a new production module is created, a suggested location is:

```text
DkMath/FLT/Prime/PrimeTraceOneCoordinateReceiver.lean
```

but reusing `PrimeTraceOneClassGroupClosure.lean` is acceptable if the public
surface remains coherent.  Prefer a separate module if p=11 conditional and
future coordinate consumers would otherwise make the class-group-closure file
semantically misleading.

Do not export a new module through the top-level `DkMath.FLT` facade in this
checkpoint unless an existing local facade convention clearly requires it.

---

## 7. Validation

Run narrow focused builds first.  Suggested targets, adjusted to actual module
names:

```text
lake build DkMath.Lib.NumberTheory.TraceOnePowerLanding
lake build DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
lake build DkMath.FLT.Prime.PrimeTraceOneClassGroupClosure
lake build DkMath.FLT.Prime.PrimeTraceOneCoordinateReceiver
lake build DkMathTest.FLT.Prime.PrimeTraceOneImaginaryCoordinateReceiverApiAudit
```

Add a focused axiom audit for the new load-bearing generic receiver and the p=7
specialization.  Report exact dependencies.

Also run:

```text
git diff --check
```

and the repository-standard forbidden-source scan.  No new:

```text
sorry
sorryAx
admit
explicit axiom
unsafe
```

may appear in production/test sources.

Existing standard Lean/Mathlib axioms such as `propext`, `Classical.choice`,
and `Quot.sound` are not automatically a failure; report the actual output.

---

## 8. Outcome classification

Use exactly one primary outcome:

```text
Outcome A — GENERIC IMAGINARY RESIDUAL COORDINATE RECEIVER GREEN
Outcome B — EXACT-POWER ENDPOINT GREEN, FPTC-003 COMPOSITION/API BOUNDARY REMAINS
Outcome C — CURRENT PACKET/INSTANCE SHAPE BLOCKS A CLEAN COORDINATE RECEIVER
```

Outcome A requires all of:

```text
- a generic imaginary coordinate receiver consuming the Phase-26 exact-power theorem;
- actual reuse of traceOne_pow_core_landing_iff;
- exact integer coordinate equations for Q.residual;
- p=7 regression with no caller-supplied class-group hypothesis;
- p=11 conditional regression or a precise documented reason it cannot be stated cleanly;
- focused build success;
- axiom and forbidden-source audits;
- report-004.md with the next arithmetic consumer surface recorded.
```

---

## 9. Hard boundaries

Do not in FPTC-004:

- prove a final contradiction from the coordinate equations;
- claim general FLT;
- prove a new class-number or class-group coprimality theorem for p=11 or general p;
- eliminate real `Fin p` sectors;
- implement p=3 or p=5 carrier/sector adapters;
- reopen q-adic `2m-global` descent;
- introduce a second power-coordinate recurrence;
- replace FPTC-003 with a duplicate ad hoc landing proof;
- import specialized FLT7 final contradiction theorems merely to prove the p=7 regression.

The checkpoint should end with a clean new boundary:

```text
generic imaginary FLT residual exact p-th power
        -> exact TraceOne integer recurrence coordinates
```

The following checkpoint may then inspect those coordinate equations for an
actual arithmetic obstruction.
