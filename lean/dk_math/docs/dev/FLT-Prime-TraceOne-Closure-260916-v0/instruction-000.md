# Instruction-000 — Class-group discharge audit and p=7 generic regression

## Working branch

Work only on:

```text
repository: Deskuma/dkmath
branch: research/FLT-Prime-TraceOne-Closure-260916-v0
base develop commit: 6ba1fe2ac4a1a346eb8a18db480ab3d518b348e7
```

Read first:

```text
README.md
AGENT.md
SUMMARY.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/README.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/ROADMAP.md
lean/dk_math/docs/refact/FLT-Prime-Generalization-260911-v0/summary-026.md
lean/dk_math/docs/refact/FLT-Prime-Generalization-260911-v0/report-026.md
```

This checkpoint is deliberately narrow.

**Do not attempt arbitrary-p class-number estimates, real-sector elimination,
or a general FLT theorem.**

The purpose is to determine exactly when the Phase-26 class-group hypothesis is
already automatic from existing ring structure, expose that fact through a
neutral reusable API, and verify it on the generic p=7 TraceOne route.

---

## 0. Repository-first audit

Before editing production code, locate and record the exact declarations,
instances, and import paths for at least:

```lean
DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt
classGroup_eq_one_of_pow_eq_one_of_classGroupPTorsionFreeAt
ideal_isPrincipal_of_classGroupPTorsionFreeAt
ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt

exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
exists_sector_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt

DkMath.FLT.Prime.exists_unit_mul_pow_of_primeTraceOneStrippedIdealPacket
DkMath.FLT.Prime.exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket
DkMath.FLT.Prime.exists_real_sector_mul_pow_of_primeTraceOneStrippedIdealPacket

DkMath.FLT.Seven.traceOneNegTwoEuclideanDomain
```

Also inspect the exact Mathlib API connecting:

```text
EuclideanDomain R
PrincipalIdealRing / IsPrincipalIdealRing R
ClassGroup R
ClassGroup.mk0
subsingleton / trivial class group
```

Do not assume theorem or instance names from memory. Use the current checkout.

In particular determine whether the existing Euclidean-domain instance on
`TraceOneInt (-2)` already synthesizes the principal-ideal structure required
to show its class group is trivial.

Create and maintain:

```text
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-000.md
```

The report must list exact declarations, files, import directions, failed API
probes, and any mismatch with this instruction.

---

## 1. Focused API audit test

Before production edits, add a small audit file, suggested:

```text
DkMathTest/FLT/Prime/PrimeTraceOneClassGroupClosureApiAudit.lean
```

Use `#check`, local examples, and instance synthesis to answer:

1. Can `ClassGroup R` be shown subsingleton/trivial from the existing
   principal-ideal typeclass directly?
2. Does `EuclideanDomain (TraceOneInt (-2))` synthesize the needed
   principal-ideal instance without importing the FLT7 final proof stack?
3. Can `classGroupPTorsionFreeAt (TraceOneInt (-2)) 7` be proved solely from
   that structural information?
4. What is the thinnest import set that makes the proof work?

Do not leave exploratory `example` blocks in a production module unless they
become purposeful regression tests.

---

## 2. Neutral class-group discharge module

If the audit confirms a clean reusable implication, add a neutral module,
suggested:

```text
DkMath/Lib/NumberTheory/ClassGroupTorsionBridge.lean
```

It should import the thinnest Mathlib / DkMath layer possible and must not
import FLT3/5/7.

Preferred first theorem shape:

```lean
classGroupPTorsionFreeAt_of_subsingleton_classGroup
```

with conceptual content:

```text
[Subsingleton (ClassGroup R)]
  -> classGroupPTorsionFreeAt R p.
```

If Mathlib exposes a direct principal-ideal-ring theorem, add a second reusable
bridge with conceptual content:

```text
[principal ideal structure on R]
  -> classGroupPTorsionFreeAt R p.
```

The exact assumptions and names must follow the real API discovered in Part 0.
Do not create a stronger typeclass requirement than necessary merely to make
typeclass search convenient.

The proof should be structural and independent of `p`; no primality hypothesis
is mathematically necessary once the class group is trivial.

Suggested status if successful:

```text
FPTC-CLASSGROUP-TRIVIAL-BRIDGE-GREEN
```

---

## 3. p=7 structural regression

Add an FLT-side specialization or test proving that the existing FLT7
Euclidean-domain infrastructure discharges the class-group hypothesis of the
generic prime route.

The key target is a theorem or check of the conceptual form:

```lean
classGroupPTorsionFreeAt (TraceOneInt (-2)) 7
```

obtained from structural ring instances, not from the specialized FLT7
contradiction theorem.

Do **not** prove this by importing an already completed `FLT_d7` theorem or by
using an assumption equivalent to the target.

If the signed-prime parameter needs normalization, prove/check explicitly that
for `p = 7` the generic carrier reduces to `TraceOneInt (-2)` using existing
`signedPrimeParameter` computation lemmas or `norm_num`/`decide` where
appropriate.

Suggested status:

```text
FPTC-P7-CLASSGROUP-DISCHARGED-GREEN
```

---

## 4. Compose with the generic Phase-26 endpoint

If Part 3 is green, add a focused regression theorem or probe showing that the
Phase-26 generic imaginary theorem no longer needs a caller-supplied
class-group hypothesis at `p=7`.

Conceptually:

```text
PrimeTraceOneStrippedIdealPacket at p=7
  -> exists delta : TraceOneInt (-2), residual = delta^7.
```

Use

```lean
DkMath.FLT.Prime.exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket
```

and discharge its `classGroupPTorsionFreeAt` argument with the neutral bridge.
Do not duplicate the ideal principalization or unit-sector proof.

This is a **generic-route regression**, not a new FLT7 proof.

Suggested status:

```text
FPTC-P7-GENERIC-RESIDUAL-EXACT-POWER-GREEN
```

---

## 5. Scope audit for p=3 and p=5 — report only

Checkpoint 000 should record, but not yet implement, two carrier facts relevant
to later checkpoints.

### p=3

Verify from production that:

```lean
abbrev EisensteinInt := TraceOneInt (-1)
```

and determine whether the remaining Phase-26 p=3 boundary is only a missing
`UnitPowerSectorSystem` package. Do not build the adapter yet unless it is
literally a one-line reuse needed for the Part-0 audit.

### p=5

Verify that `GoldenInt` is a distinct structure from `TraceOneInt 1`, despite
having the same quadratic multiplication law. Record the likely bridge surface
but do not implement it in checkpoint 000.

---

## 6. Optional cardinality criterion — audit only

Search Mathlib for the cleanest route to the future theorem

```text
gcd(p, Fintype.card (ClassGroup R)) = 1
  -> classGroupPTorsionFreeAt R p.
```

Record exact candidate lemmas about element order / finite group cardinality in
`report-000.md`.

Do not implement this criterion in checkpoint 000 unless it is genuinely tiny
and does not distract from the p=7 structural regression. It is scheduled for
FPTC-001.

---

## 7. Imports and public surface

Do not export a new module through `DkMath.Lib` or `DkMath.FLT` until the
focused build and axiom audit are green.

If a neutral module is added, prefer one-way dependency:

```text
DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
        ↓
DkMath.FLT.Prime ... regression/specialization
```

Never introduce:

```text
DkMath.Lib.NumberTheory -> DkMath.FLT.Seven
```

The specialized FLT7 Euclidean instance may be imported only by the FLT-side
regression/test that consumes the neutral theorem.

---

## 8. Validation

Run the narrowest available focused builds first. Suggested targets, adjusted
to actual module names if needed:

```text
lake build DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
lake build DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
lake build DkMath.FLT.Seven.QuadraticEuclidean
lake build DkMathTest.FLT.Prime.PrimeTraceOneClassGroupClosureApiAudit
```

If a new p=7 regression module is added, build it explicitly.

Also run:

```text
git diff --check
```

and the repository-standard forbidden-source scan. The new production and test
files must contain no new:

```text
sorry
sorryAx
admit
explicit axiom
unsafe
```

Print axioms for the load-bearing neutral bridge and the p=7 generic exact-power
regression.

Existing standard Lean axioms such as `propext`, `Classical.choice`, and
`Quot.sound` are not by themselves a failure; report the actual audit output.

---

## 9. Outcome classification

Use exactly one primary outcome:

```text
Outcome A — P7 CLASS-GROUP HYPOTHESIS DISCHARGED STRUCTURALLY
Outcome B — NEUTRAL BRIDGE GREEN, P7 INSTANCE/IMPORT BOUNDARY REMAINS
Outcome C — PRINCIPAL-IDEAL / CLASS-GROUP API GAP IDENTIFIED
```

Outcome A requires all of:

```text
- neutral structural class-group torsion-free bridge;
- focused build success;
- p=7 `classGroupPTorsionFreeAt` without an arithmetic hypothesis;
- generic Phase-26 p=7 residual exact-power composition;
- no use of the specialized FLT7 final contradiction theorem;
- report-000.md with exact API evidence.
```

---

## 10. Hard boundaries

Do not in checkpoint 000:

- prove or assume the general prime-discriminant class-number theorem;
- eliminate any real `Fin p` sector;
- generalize `traceOne_sq_core_landing_iff` to arbitrary powers yet;
- reopen q-adic `2m-global` descent;
- alter the completed FLT3/FLT5/FLT7 theorem stacks;
- claim that p=7 generic residual exact power alone proves FLT7;
- add a generic FLT theorem to the public facade;
- hide `classGroupPTorsionFreeAt` in a new structure or axiom.

The desired result is a small but decisive normalization of the Phase-26
frontier: if the class group is already structurally trivial, the generic
conditional endpoint should say so without making every caller re-supply the
same hypothesis.
