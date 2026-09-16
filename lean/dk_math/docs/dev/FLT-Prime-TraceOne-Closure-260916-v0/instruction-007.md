# FPTC-007 instruction — prime-discriminant class-number frontier

Branch: `research/FLT-Prime-TraceOne-Closure-260916-v0`

This checkpoint begins after FPTC-006 Outcome A.  Treat this file as a bounded
research/implementation contract.  The goal is to identify and, only where the
current checked APIs genuinely support it, discharge the remaining class-group
obstruction for the generic imaginary prime-discriminant TraceOne family.

Do **not** turn this checkpoint into a proof of general FLT, a general PID
claim, or a new analytic-number-theory development hidden behind assumptions.

## 0. Current checked frontier

The generic imaginary route now has the checked shape

```text
PrimeAdicFactorPacket
  -> PrimeTraceOneStrippedIdealPacket
  -> classGroupPTorsionFreeAt R_p p
  -> residual = delta^p
  -> exact TraceOne integer recurrence coordinates
```

where

```text
R_p := TraceOneInt (signedPrimeParameter p).
```

FPTC-001 already provides the neutral finite-group bridge

```lean
Nat.Coprime p (Fintype.card (ClassGroup R))
  -> classGroupPTorsionFreeAt R p.
```

FPTC-000, FPTC-005, and FPTC-006 discharge the class-group condition
structurally at `p = 7`, `p = 3`, and `p = 5` by existing Euclidean/PID
structure.  This checkpoint is about the **generic imaginary family**, not
about re-proving those fixed exponents.

For `p % 4 = 3`, the prime-discriminant definitions give conceptually

```text
signedPrimeDiscriminant p = -p
R_p = O_(K_p)
K_p := TraceOneRat (signedPrimeParameter p)
```

with `R_p` already proved to be the full ring of integers of `K_p` by the
Phase-17 TraceOne maximal-order work.

The remaining arithmetic target should therefore be made as concrete as the
current NumberField/ClassGroup APIs permit:

```text
Nat.Coprime p (class number of K_p)
```

or, if transport to `NumberField.classNumber` is API-blocked,

```text
Nat.Coprime p (Fintype.card (ClassGroup R_p)).
```

Do not silently identify these two cardinalities without a checked transport.

## 1. Required reading before edits

Read at least:

```text
README.md
ROADMAP.md
report-000.md
report-001.md
report-004.md
report-006.md

DkMath/Lib/NumberTheory/ClassGroupTorsionBridge.lean
DkMath/NumberTheory/PrimeQuadraticDiscriminant.lean
DkMath/NumberTheory/TraceOneQuadraticField.lean
DkMath/NumberTheory/TraceOnePrimeUnitSectors.lean
DkMath/FLT/Prime/PrimeTraceOneConditionalDescent.lean
DkMath/FLT/Prime/PrimeTraceOneCoordinateReceiver.lean
DkMath/FLT/Prime/PrimeTraceOneClassGroupClosure.lean
```

Audit, but do not depend on final FLT7 contradiction modules, the reusable
Minkowski/class-number examples in:

```text
DkMath/FLT/Seven/SevenRealCubicNumberField.lean
DkMath/FLT/Seven/SevenRamifiedFusionCyclotomicSevenPID.lean
```

Also inspect the pinned Mathlib API, especially:

```text
Mathlib/NumberTheory/NumberField/ClassNumber.lean
Mathlib/RingTheory/ClassGroup/Basic.lean
Mathlib/RingTheory/ClassGroup/ExtendedHom.lean
Mathlib/NumberTheory/ClassNumber/Finite.lean
```

Do repository/API search before introducing a new class-group transport.

## 2. Exact API audit — mandatory

Create a focused audit, suggested path:

```text
DkMathTest/FLT/Prime/PrimeTraceOneClassNumberFrontierApiAudit.lean
```

Record exact Lean 4.34 signatures for the declarations actually used.
At minimum audit:

```text
DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt
DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt_of_coprime_card

DkMath.NumberTheory.TraceOneQuadraticField.TraceOneRat
traceOneRat_ringOfIntegers_equiv
traceOneRat_isDedekindDomain
traceOneRat_numberField          -- exact current name/signature if present

signedPrimeDiscriminant
signedPrimeParameter
discr_signedPrimeParameter

NumberField.classNumber
NumberField.classNumber_pos
NumberField.classNumber_ne_zero
NumberField.classNumber_eq_one_iff
NumberField.exists_ideal_in_class_of_norm_le
```

Also search for and record the exact current API for transporting class groups
or their cardinalities across a ring equivalence.  Candidate families include,
but are not limited to:

```text
ClassGroup.extendedHom
ClassGroup equivalences induced by RingEquiv / AlgEquiv
Picard-group equivalences if they are the canonical available route
Fintype.card_congr
```

Do **not** invent a bespoke quotient-level class-group equivalence until the
existing API has been exhausted.

## 3. First production target — class-number/cardinality transport

The first mathematical objective is not a class-number estimate.  It is to
make the arithmetic obstruction exact.

Let

```text
K_p := TraceOneRat (signedPrimeParameter p)
R_p := TraceOneInt (signedPrimeParameter p).
```

For odd prime `p`, the existing theorem

```text
traceOneRat_ringOfIntegers_equiv
```

provides

```text
NumberField.RingOfIntegers K_p ≃+* R_p.
```

If the current ClassGroup API supports a clean transport, prove a theorem of
one of the following conceptual shapes:

```lean
Fintype.card (ClassGroup R_p) = NumberField.classNumber K_p
```

or an equivalently useful cardinality equality/congruence.

Preferred location if the theorem is FLT-independent:

```text
DkMath/NumberTheory/PrimeTraceOneClassNumber.lean
```

Keep this module free of `DkMath.FLT.*` imports if possible.

If no clean ClassGroup/RingEquiv transport exists in the pinned API, stop and
record the precise missing API rather than implementing a large new quotient
transport layer in this checkpoint.

### Required follow-up bridge if transport succeeds

Use FPTC-001 to expose the concrete implication

```text
Nat.Coprime p (NumberField.classNumber K_p)
  -> classGroupPTorsionFreeAt R_p p.
```

The exact theorem name is up to repository style.  A conceptual candidate is:

```lean
classGroupPTorsionFreeAt_primeTraceOne_of_coprime_classNumber
```

Do not require `p.Prime` merely for the finite-group argument itself; require
prime/odd hypotheses only where they are genuinely needed to identify `R_p`
with the ring of integers of `K_p`.

## 4. Discriminant/signature audit — required, production only if clean

To use Minkowski uniformly, audit whether the repository currently proves the
**number-field discriminant** identity

```text
NumberField.discr K_p = signedPrimeDiscriminant p
```

or at least the absolute-value form needed for the Minkowski bound.

Important distinction:

```text
TraceOneQuadratic.discr (signedPrimeParameter p)
  = signedPrimeDiscriminant p
```

is already proved, but this is not automatically the same declaration as
`NumberField.discr K_p`.

The ring-of-integers equivalence makes such a bridge mathematically natural,
but it must be kernel-checked through the actual integral-basis/discriminant
API.

For the imaginary branch audit the signature needed for the quadratic
Minkowski formula:

```text
p % 4 = 3
  -> nrRealPlaces K_p = 0
  -> nrComplexPlaces K_p = 1
  -> finrank_Q K_p = 2.
```

Reuse existing TraceOne signature work if already present.  Do not rebuild
Dirichlet/signature machinery unnecessarily.

If the discriminant or signature bridge is a small reusable theorem, it may be
added in a neutral NumberTheory module.  If it expands into a new large
number-field development, report the boundary and stop there.

## 5. Minkowski/class-number frontier audit — mandatory

Mathlib currently provides the number-field class number as the cardinality of
the ring-of-integers class group and provides

```text
NumberField.exists_ideal_in_class_of_norm_le
```

which gives an ideal representative in every class with norm at most the
Minkowski bound.

For a quadratic imaginary prime-discriminant field the expected numerical
Minkowski scale is conceptually

```text
(2 / pi) * sqrt(p).
```

Audit whether the current API can turn this into a **class-number cardinality
upper bound** strong enough to prove

```text
NumberField.classNumber K_p < p
```

or directly

```text
Nat.Coprime p (NumberField.classNumber K_p).
```

Do not assume that existence of a small ideal representative by itself bounds
the number of classes.  A cardinality bound needs a checked finite target and
an injection/surjection/counting argument.

Search before implementing for existing Mathlib results about:

```text
finite ideals of bounded absolute norm
cardinality of ideals with absNorm <= B
number-field ideal-counting functions
class-number upper bounds
```

The file

```text
Mathlib/NumberTheory/NumberField/Ideal/Asymptotics.lean
```

may contain relevant finiteness/counting infrastructure, but do not import a
large asymptotic theory unless it materially shortens a checked finite bound.

### No uniform PID target

Do **not** target

```text
IsPrincipalIdealRing R_p
```

for all imaginary primes.  The generic route needs only p-torsion-freeness /
class-number coprimality, which is strictly weaker than class number one.

Likewise, do not generalize the FLT7 Euclidean proof to arbitrary p unless the
proof is independently justified.

## 6. Bounded regressions

### p = 7 — mandatory consistency regression

Verify that the new class-number formulation is compatible with the existing
structural result

```lean
classGroupPTorsionFreeAt_traceOneNegTwo_seven
```

and the existing `TraceOneInt (-2)` Euclidean/PID structure.

If a class-number/cardinality transport theorem was implemented, verify the
p=7 class number/cardinality equals `1` through existing PID facts.  This is a
regression only; do not replace the shorter FPTC-000 production theorem.

### p = 11 — audit, implementation optional

The current generic receiver already reaches `p = 11` conditionally at
`TraceOneInt (-3)`.

Audit the pinned Minkowski/class-number API for this concrete field.  If the
existing API makes a proof of class number one or merely `11`-coprimality very
small and local, it may be implemented as a bounded regression.

Do not create a large specialized `p=11` Euclidean-domain development merely
to obtain Outcome B.

If p=11 remains conditional, record the exact first missing checked theorem.

## 7. Optional consumer theorem

If the class-number-to-torsion bridge is green, a thin FLT-side theorem may be
added that restates the generic imaginary exact-power or coordinate receiver
under the concrete hypothesis

```text
Nat.Coprime p (NumberField.classNumber K_p)
```

instead of the abstract

```text
classGroupPTorsionFreeAt R_p p.
```

This is optional.  Do not duplicate the existing receiver body; compose it.

## 8. Hard non-goals

Do not implement or claim in FPTC-007:

```text
- general FLT;
- a generic FLT counterexample -> PrimeAdicFactorPacket router;
- uniform class number = 1 for prime-discriminant quadratic fields;
- unproved class-number formulae;
- analytic Dirichlet L-function bounds from scratch;
- a new large ideal-counting/asymptotic library merely to force Outcome A;
- real Fin p sector elimination;
- p=5 nonzero-sector elimination;
- p=3 sector elimination;
- q-adic 2m-global descent;
- any use of a completed FLT3/FLT5/FLT7 final contradiction as a hidden provider.
```

Do not insert `classGroupPTorsionFreeAt` as an unexplained hypothesis into a
new theorem and call that progress.  The point of this checkpoint is to expose
what arithmetic statement actually supplies it.

## 9. Validation

At minimum run focused builds for every edited production/test module and:

```text
lake build DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
lake build DkMath.NumberTheory.TraceOneQuadraticField
lake build DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
lake build DkMath.FLT.Prime.PrimeTraceOneCoordinateReceiver
```

plus any new `PrimeTraceOneClassNumber` module and the focused audit files.

Run:

```text
git diff --check
```

and the repository-standard forbidden-source scan for new/edited Lean files.
No new `sorry`, `sorryAx`, `admit`, explicit project axiom, or `unsafe`
declaration is permitted.

Create an axiom audit for every load-bearing new theorem.  Standard inherited
Lean/Mathlib foundations such as

```text
[propext, Classical.choice, Quot.sound]
```

are acceptable if that is the actual checked surface.

## 10. Required report

Write:

```text
lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-007.md
```

The report must state separately:

```text
1. exact class-number / ClassGroup cardinality APIs found;
2. whether RingOfIntegers -> TraceOne class-group cardinality transport is green;
3. exact discriminant and signature bridges currently available;
4. the exact Minkowski theorem(s) available;
5. whether those theorems actually imply a class-number cardinality bound;
6. p=7 regression result;
7. p=11 result or first missing theorem;
8. the strongest generic theorem actually proved;
9. the first remaining mathematical obstruction.
```

If the general coprimality statement remains open, write it explicitly in Lean
or mathematical form.  Do not hide it behind prose such as "class-number work
remains".

## 11. Outcome classification

Use one of these outcomes.

### Outcome A — GENERIC IMAGINARY CLASS-NUMBER COPRIMALITY GREEN

Requires a kernel-checked theorem covering the intended generic imaginary
prime family and yielding

```text
Nat.Coprime p (class number of K_p)
```

or directly

```text
classGroupPTorsionFreeAt R_p p
```

from hypotheses already present in the generic prime-discriminant setup, with
no new unproved number-theoretic assumption.

### Outcome B — CLASS-NUMBER BRIDGE GREEN, BOUNDED CLOSURE ONLY

Use when the class-number/cardinality transport and concrete torsion bridge are
green, and one or more new bounded exponents can be discharged, but no uniform
imaginary-prime theorem is proved.

### Outcome C — CLASS-NUMBER FRONTIER ISOLATED

Use when the exact class-number/cardinality target is successfully connected to
the TraceOne generic route, but the current checked Minkowski/counting API does
not prove the required uniform coprimality.  This is a valid research outcome,
not a failure.  State the first missing theorem exactly.

### Outcome D — CLASSGROUP / RING-EQUIV TRANSPORT API BLOCKED

Use only if even the clean identification of the TraceOne class-group
cardinality with the number-field class number cannot be kernel-checked without
building substantial new transport infrastructure.  Record the exact API gap
and do not fake the identification.

## 12. Stop rule

If the next step would require proving a genuinely new general class-number
upper bound or analytic estimate not already supported by the repository or
Mathlib, stop at Outcome C with a precise theorem-shaped frontier.

The desired result of FPTC-007 is **clarity about the exact arithmetic wall**.
A smaller checked bridge plus an explicit frontier is preferable to an
unsupported uniform theorem.
