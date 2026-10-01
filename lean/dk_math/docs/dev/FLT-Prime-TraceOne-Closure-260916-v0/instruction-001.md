# Instruction-001 — Finite class-group cardinality criterion

## Working branch

Continue working only on the current branch:

```text
repository: Deskuma/dkmath
branch: research/FLT-Prime-TraceOne-Closure-260916-v0
```

Do not reset or recreate the branch. Preserve all FPTC-000 work already present.

Read first:

```text
README.md
AGENT.md
SUMMARY.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/README.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/ROADMAP.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/instruction-000.md
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-000.md
lean/dk_math/DkMath/Lib/NumberTheory/ClassGroupTorsionBridge.lean
lean/dk_math/DkMath/Lib/NumberTheory/IdealPowerFactor.lean
```

FPTC-000 is complete with Outcome A. Treat its neutral structural bridge and the
p=7 generic regression as established infrastructure.

This checkpoint is deliberately narrow.

**Do not attempt any class-number bound, Minkowski estimate, real-sector
elimination, arbitrary-power TraceOne coordinates, or general FLT theorem.**

The purpose of FPTC-001 is to convert the abstract hypothesis

```lean
classGroupPTorsionFreeAt R p
```

into the concrete finite-group criterion

```text
Nat.Coprime p (Fintype.card (ClassGroup R))
```

whenever the class group is finite.

---

## 0. Repository-first and Mathlib API audit

Before editing production code, inspect the exact current Lean 4.34 / Mathlib
APIs for:

```lean
DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt
DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt_of_subsingleton_classGroup
DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt_of_isPrincipalIdealRing
DkMath.Lib.NumberTheory.ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt
```

and for finite-group element order:

```text
orderOf_dvd_of_pow_eq_one
orderOf_dvd_card
orderOf_eq_one_iff
Fintype.card
Nat.Coprime
Nat.Coprime.gcd_eq_one
```

Also inspect any more direct current Mathlib theorem that may already express
one of the following ideas:

```text
x^p = 1 and Coprime p |G| -> x = 1

I^p principal and Coprime p |ClassGroup R| -> I principal
```

In particular audit the current signatures and assumptions of:

```text
FractionalIdeal.isPrincipal.of_isPrincipal_pow_of_coprime
Ideal.IsPrincipal.of_isPrincipal_pow_of_coprime
```

Do not assume theorem names or argument order from `report-000.md`; verify them
against the current checkout after the Lean 4.34 migration.

Record all exact declarations, assumptions, failed probes, and import choices in:

```text
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-001.md
```

---

## 1. Focused API audit test

Create a focused audit file, suggested:

```text
DkMathTest/Lib/NumberTheory/ClassGroupTorsionCardinalityApiAudit.lean
```

or the nearest repository-consistent location.

Use `#check`, `#synth`, and small local examples to determine:

1. which assumptions make `Fintype (ClassGroup R)` available;
2. whether `orderOf_dvd_card` works directly for `ClassGroup R` under those
   assumptions;
3. whether `orderOf_dvd_of_pow_eq_one` accepts exponent `p : ℕ` in the desired
   form;
4. the cleanest way to conclude `a = 1` from `orderOf a = 1`;
5. whether the direct ideal-principalization theorem is thinner than routing
   through `classGroupPTorsionFreeAt`.

The production theorem should not carry number-field assumptions if a more
neutral finite-group/class-group statement suffices.

Do not leave exploratory code in production modules unless it becomes a
purposeful regression theorem.

---

## 2. Main neutral finite-cardinality bridge

Extend the existing neutral module:

```text
DkMath/Lib/NumberTheory/ClassGroupTorsionBridge.lean
```

unless the import structure clearly justifies a separate small module.

Target a theorem with conceptual content:

```lean
Nat.Coprime p (Fintype.card (ClassGroup R))
  -> classGroupPTorsionFreeAt R p
```

Suggested name:

```lean
classGroupPTorsionFreeAt_of_coprime_card
```

The exact binder/typeclass assumptions must be chosen from the actual API audit.
Prefer the weakest natural assumptions.

A likely proof route is:

```text
a^p = 1
  -> orderOf a | p
  -> orderOf a | Fintype.card (ClassGroup R)
  -> Coprime p card
  -> orderOf a = 1
  -> a = 1.
```

But do not force this route if Mathlib exposes a cleaner theorem.

The theorem must be:

- independent of FLT;
- independent of primality of `p`;
- independent of a specific quadratic field;
- free of any hidden class-number estimate;
- a theorem-level bridge, not a new axiom or opaque structure field.

Suggested status if successful:

```text
FPTC-CLASSGROUP-COPRIME-CARD-BRIDGE-GREEN
```

---

## 3. Convenience corollaries — only if genuinely thin

If the main bridge is green, consider adding one or both of the following
corollaries only when they are one-step compositions of existing APIs.

### 3.1 Principalization from coprime class-group cardinality

Conceptually:

```text
I^p is principal
Nat.Coprime p (Fintype.card (ClassGroup R))
  -> I is principal.
```

Prefer composing:

```lean
classGroupPTorsionFreeAt_of_coprime_card
```

with the existing DkMath theorem

```lean
ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt
```

rather than duplicating its proof.

If Mathlib already has exactly the desired theorem with a better abstraction,
record that fact and avoid a redundant wrapper unless it materially improves the
DkMath API.

### 3.2 Trivial-class-group compatibility

Show that the FPTC-000 structural case is compatible with the new cardinality
criterion. A minimal regression such as

```text
Subsingleton (ClassGroup R)
  -> Fintype.card (ClassGroup R) = 1
  -> Nat.Coprime p 1
```

is enough if it is useful for testing. Do not add unnecessary production
lemmas merely to restate elementary finite-cardinality facts.

---

## 4. p=7 regression through the cardinality route

FPTC-000 already proves structurally:

```lean
classGroupPTorsionFreeAt (TraceOneInt (-2)) 7
```

from the Euclidean/PID structure.

For FPTC-001, add only a focused regression showing that the new
finite-cardinality bridge is consistent with that result.

Preferred conceptual route:

```text
TraceOneInt (-2) is a principal ideal ring
  -> ClassGroup is subsingleton
  -> card ClassGroup = 1
  -> Coprime 7 1
  -> classGroupPTorsionFreeAt (TraceOneInt (-2)) 7.
```

This may live in the API audit/test layer rather than production if it adds no
new reusable theorem.

Do **not** replace the existing FPTC-000 p=7 structural theorem with the longer
cardinality proof. The structural theorem remains the preferred p=7 production
path.

Suggested regression status:

```text
FPTC-P7-CARDINALITY-ROUTE-CONSISTENT-GREEN
```

---

## 5. Optional generic Phase-26 composition

Only if it is truly a one-line corollary after Part 2, add or test a theorem of
conceptual form:

```text
PrimeTraceOneStrippedIdealPacket p ...
Nat.Coprime p (Fintype.card (ClassGroup R))
  -> generic residual endpoint supplied with
     classGroupPTorsionFreeAt_of_coprime_card.
```

Do not duplicate the Phase-26 ideal/unit proofs.

This part is optional because the central product of FPTC-001 is the neutral
class-group criterion, not another FLT wrapper.

If adding such a wrapper would create awkward imports or duplicate existing
composition, document the intended call pattern in `report-001.md` and stop.

---

## 6. Explicit non-goals

Do not in FPTC-001:

- prove `Nat.Coprime p (Fintype.card (ClassGroup R))` for the generic
  prime-discriminant TraceOne family;
- compute any new class number;
- use Minkowski bounds to prove a class number estimate;
- claim that `p` never divides the class number of the relevant quadratic field;
- introduce regular-prime/Bernoulli assumptions;
- eliminate the real `Fin p` unit sectors;
- generalize `TraceOnePowerLanding` beyond squares;
- work on p=3 or p=5 carrier/sector adapters;
- reopen q-adic `2m-global` descent;
- alter completed FLT3/FLT5/FLT7 final contradiction theorems;
- claim a general FLT result.

The checkpoint ends once the abstract class-group torsion condition has been
cleanly reduced to a finite-cardinality coprimality condition.

---

## 7. Dependency and facade rules

Keep the dependency direction neutral:

```text
DkMath.Lib.NumberTheory.IdealPowerFactor
        ↓
DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
        ↓
FLT consumers
```

No neutral `DkMath.Lib.NumberTheory` module may import FLT3/5/7.

If `ClassGroupTorsionBridge.lean` is already exported through `DkMath.Lib`, no
facade change is needed unless a new module is introduced.

Avoid adding broad imports merely to obtain a finite-group theorem. Prefer the
smallest current Mathlib import that is stable under Lean 4.34.

---

## 8. Validation

Run the narrowest focused builds first. At minimum, adjusted to the final file
names:

```text
lake build DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
lake build DkMathTest.Lib.NumberTheory.ClassGroupTorsionCardinalityApiAudit
lake build DkMath.Lib
```

If an FLT-side regression/wrapper is added, build it explicitly as well.

Run:

```text
git diff --check
```

and the repository-standard forbidden-source scan.

New production and test files must contain no new:

```text
sorry
sorryAx
admit
explicit axiom
unsafe
```

Add an axiom audit for the load-bearing theorem

```lean
classGroupPTorsionFreeAt_of_coprime_card
```

and for any new principalization corollary or FLT wrapper.

Standard Lean/Mathlib foundations such as `propext`, `Classical.choice`, and
`Quot.sound` are not themselves failures; report the actual `#print axioms`
output.

---

## 9. Report requirements

`report-001.md` must contain at least:

1. exact Lean 4.34 / Mathlib declarations used;
2. final theorem signatures and module paths;
3. proof strategy for the coprime-cardinality bridge;
4. whether the proof used `orderOf` or a more direct Mathlib theorem;
5. exact typeclass assumptions required for `Fintype (ClassGroup R)`;
6. whether a principalization convenience corollary was added and why;
7. p=7 cardinality-route regression result;
8. all focused build results;
9. forbidden-source and axiom-audit results;
10. the precise remaining frontier after this checkpoint.

The final frontier statement should explicitly distinguish:

```text
formal bridge now available:
  Coprime(p, |ClassGroup R|)
    -> classGroupPTorsionFreeAt R p

still unproved for the generic FLT family:
  Coprime(p, |ClassGroup (TraceOne prime-discriminant order)|).
```

Do not conflate these two statements.

---

## 10. Outcome classification

Use exactly one primary outcome:

```text
Outcome A — FINITE CLASS-GROUP COPRIMALITY BRIDGE GREEN
Outcome B — GROUP-THEORETIC BRIDGE GREEN, CLASSGROUP FINITENESS/API BOUNDARY REMAINS
Outcome C — CURRENT MATHLIB API DOES NOT SUPPORT A CLEAN NEUTRAL CARDINALITY BRIDGE
```

Outcome A requires all of:

```text
- a neutral theorem reducing classGroupPTorsionFreeAt to coprimality with
  Fintype.card (ClassGroup R);
- focused build success under Lean 4.34;
- no new DkMath axiom or hidden arithmetic assumption;
- a p=7 compatibility regression;
- report-001.md with exact API evidence;
- axiom audit of the load-bearing theorem.
```

Outcome B is appropriate only if the finite-group theorem itself is proved but
making it apply to the intended class-group type requires a genuinely missing
or unsuitable finiteness/typeclass bridge.

Outcome C must record the exact API obstruction and failed probes rather than
papering over the gap with a stronger number-field hypothesis.

---

## 11. Stop rule and handoff to FPTC-002

Once Outcome A/B/C is honestly classified, stop this checkpoint.

Do not start arbitrary-power coordinates in the same implementation pass.

If Outcome A is obtained, the next checkpoint is FPTC-002:

```text
TraceOneInt arbitrary-power coordinate kernel
```

At that point the FLT imaginary branch will have two separate reusable layers:

```text
class-group layer:
  Coprime(p, class number) -> exact p-th-power element

coordinate layer:
  exact p-th-power element -> explicit integer coordinate recurrence.
```

Keeping those layers separate is the main architectural requirement of this
checkpoint.
