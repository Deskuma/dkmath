# FLT prime-generalization Phase 17 — TraceOne maximal order / Dedekind realization

## Goal

Phase 13 completed the arbitrary odd-prime quadratic-cyclotomic front-end

```text
GTail / prime cyclotomic shell
  -> integral Gaussian coordinates
  -> TraceOneInt (signedPrimeParameter p)
```

and Phases 14–16 completed the neutral arithmetic kernels

```text
element coprime-power extraction
ideal p-th-power extraction
class-group p-torsion principalization
principal ideal -> unit * p-th power
conditional unit absorption
```

The first concrete obstruction remaining on the Phase-13 carrier is that
`TraceOneInt (signedPrimeParameter p)` is not yet known, for arbitrary odd prime `p`, to be a Dedekind domain / maximal order.

This phase is a bounded test-first probe for exactly that bridge.

Do **not** prove general FLT, class-group p-torsion-freeness, regular-prime theorems, or unit p-th-power surjectivity here.

---

## Mathematical target

For

```text
D_p := signedPrimeDiscriminant p = ±p
s_p := signedPrimeParameter p = (D_p - 1) / 4
```

we already have

```text
discr s_p = D_p
D_p % 4 = 1
|D_p| = p
```

and `TraceOneInt s_p` is the quadratic order with basis `1, τ` and relation

```text
τ^2 = τ + s_p.
```

The natural rational companion is therefore

```lean
QuadraticAlgebra ℚ (s_p : ℚ) 1
```

whose canonical root satisfies the same relation.

For odd prime `p`, `D_p = ±p` is squarefree and fundamental.  The intended arithmetic statement is that `TraceOneInt s_p` is the full ring of integers of this quadratic field, hence Dedekind.

The key point of this phase is to determine how much of that can be proved cleanly in the pinned Mathlib checkout.

---

## Part A — rational TraceOne companion

Prefer a neutral module, e.g.

```text
DkMath/NumberTheory/TraceOneQuadraticField.lean
```

or a similarly narrow name.

Define/audit a rational companion such as

```lean
abbrev TraceOneRat (s : ℤ) := QuadraticAlgebra ℚ (s : ℚ) 1
```

and construct an explicit ring/algebra embedding

```lean
TraceOneInt s ->+* TraceOneRat s
```

sending

```text
<a,b> |-> a + b*ω.
```

Prove compatibility of at least:

```text
fst/re coordinate map
τ -> ω
conjugation
trace
norm
```

where practical.

Do not introduce a duplicate quadratic ring model if an existing Mathlib representation can serve directly.

---

## Part B — field / number-field realization for signed prime discriminant

For odd prime `p`, prove or isolate the exact missing theorem needed for

```text
TraceOneRat (signedPrimeParameter p)
```

to be a field.

The pinned `QuadraticAlgebra` field instance asks for absence of a rational root of

```text
r^2 = s_p + r.
```

Equivalently the discriminant

```text
D_p = 1 + 4*s_p = ±p
```

must not be a rational square.

Use the existing signed-prime API and primality/squarefree facts.  Avoid numerical specialization to 3/5/7/11/13 in the production proof.

If the field instance is clean, also establish `NumberField` / finite-dimensional structure using pinned Mathlib APIs rather than rebuilding rank-two linear algebra manually.

Suggested classification checkpoint:

```text
PGEN-TRACEONE-QUADRATIC-FIELD-GREEN
```

---

## Part C — integral closure characterization (main target)

Attempt the direct maximal-order proof rather than assuming a ready-made quadratic-field theorem.

Let

```text
x = a + b*ω,   a b : ℚ
```

in `TraceOneRat s_p`, and assume

```text
IsIntegral ℤ x.
```

The preferred route is:

1. Show `star/conj x` is integral.
2. Therefore the rational trace and norm are integral over `ℤ`.
3. Since they lie in `ℚ`, use the already-proved rational-integral bridge from Phase 11 (or the pinned equivalent) to obtain

```text
T := trace x in ℤ
N := norm x  in ℤ.
```

4. Use the quadratic identity

```text
T^2 - D_p * b^2 = 4*N.
```

5. Hence `D_p * b^2` is an integer.  Reuse the Phase-12 squarefree-prime rational denominator lemma where possible:

```text
rat_eq_int_of_signedPrime_mul_sq
```

to conclude

```text
b in ℤ.
```

6. Since `D_p ≡ 1 (mod 4)` and

```text
T^2 - D_p*b^2 ≡ 0 (mod 4),
```

deduce `T` and `b` have the same parity.

7. Therefore

```text
a = (T - b)/2
```

is an integer.

8. Conclude that every integral element of the rational quadratic field lies in the image of `TraceOneInt s_p`.

The forward inclusion is easy: every integer-coordinate element is integral because `ω` satisfies a monic quadratic polynomial.

Package the result, if the typeclass/API shape permits, as an honest

```lean
IsIntegralClosure (TraceOneInt (signedPrimeParameter p)) ℤ
  (TraceOneRat (signedPrimeParameter p))
```

or an equivalent ring-of-integers characterization.

Suggested classification checkpoint:

```text
PGEN-TRACEONE-MAXIMAL-ORDER-GREEN
```

If this cannot be packaged because of algebra/scalar-tower friction, prove the two inclusions / image characterization explicitly and record the exact API obstruction.

---

## Part D — ring of integers equivalence and Dedekind transport

If Part C is green, use Mathlib's number-field ring-of-integers API rather than reproving Dedekind-domain theory.

Audit/use:

```text
NumberField.RingOfIntegers.equiv
NumberField.RingOfIntegers.algEquiv
NumberField.RingOfIntegers.instIsDedekindDomain
```

and any pinned transport theorem needed to obtain a usable

```lean
IsDedekindDomain (TraceOneInt (signedPrimeParameter p))
```

for arbitrary odd prime `p`.

Do not install a dangerously broad global instance if typeclass loops or ambiguous `p`/`s` inference would result.  A theorem returning the instance data, a local instance constructor, or a packet API is acceptable if safer.

Suggested classification checkpoint:

```text
PGEN-TRACEONE-DEDEKIND-GREEN
```

This is the preferred Phase-17 endpoint.

---

## Part E — finite compatibility

Probe at

```text
p = 3, 5, 7, 11, 13
```

with strict carrier discipline.

Required observations:

```text
p=3  -> s=-1
p=5  -> s= 1
p=7  -> s=-2
p=11 -> s=-3
p=13 -> s= 3
```

For p=3 and p=7, compare the new Dedekind route with the existing specialized Euclidean/PID/Dedekind carriers.

For p=5, do **not** silently identify the new `TraceOneInt 1` result with `GoldenInt`; if both are available, record them as separate carriers unless an explicit equivalence is proved.

For p=11 and p=13, a successful arbitrary-prime Dedekind realization would be genuinely new carrier arithmetic compared with Phase 14/15.  Make this explicit in the report.

---

## Part F — relation to Phase 15/16 arithmetic kernel

If `PGEN-TRACEONE-DEDEKIND-GREEN` is reached, add a test-only composition showing that the generic Phase-15/16 theorems can now instantiate on

```text
TraceOneInt (signedPrimeParameter p)
```

for an arbitrary odd prime `p`, **conditional only on** the two still-open arithmetic hypotheses:

```text
classGroupPTorsionFreeAt R p
unit p-th-power surjectivity
```

Do not prove either hypothesis in this phase.

The intended final dependency picture is

```text
Phase 13 TraceOne coordinates
  + Phase 17 maximal-order/Dedekind realization
  + classGroupPTorsionFreeAt R p        [OPEN]
  + unit p-power surjectivity            [OPEN]
  -> Phase 15/16 ideal-to-exact-power kernel
```

This should make the remaining general-prime obstruction mathematically explicit.

---

## Part G — outcome classification

Report the highest honest outcome reached:

```text
PGEN-TRACEONE-QUADRATIC-FIELD-GREEN
PGEN-TRACEONE-MAXIMAL-ORDER-GREEN
PGEN-TRACEONE-DEDEKIND-GREEN
```

If maximal-order/Dedekind realization does not close, classify the exact first obstruction, e.g.

```text
PGEN-TRACEONE-INTEGRAL-CLOSURE-API-BLOCKED
PGEN-TRACEONE-FIELD-REALIZATION-BLOCKED
PGEN-TRACEONE-DEDEKIND-TRANSPORT-BLOCKED
```

Do not overstate a partial result.

---

## Verification

Add test-first probe(s) and an axiom audit.  Suggested names:

```text
DkMathTest/FLT/Prime/TraceOneQuadraticFieldProbe.lean
DkMathTest/FLT/Prime/TraceOneDedekindAudit.lean
DkMathTest/FLT/Prime/TraceOneDedekindAxiomAudit.lean
```

Build at minimum:

```text
lake build DkMath.NumberTheory.TraceOneQuadraticField
lake build DkMath.NumberTheory.CyclotomicQRTraceOneBridge
lake build DkMath.Lib.NumberTheory.IdealPowerFactor
lake build DkMath.Lib.NumberTheory.PrincipalIdealPower
lake build DkMathTest.FLT.Prime.TraceOneQuadraticFieldProbe
lake build DkMathTest.FLT.Prime.TraceOneDedekindAudit
lake build DkMathTest.FLT.Prime.TraceOneDedekindAxiomAudit
lake build DkMath.FLT.Seven
```

Also run:

```text
git diff --check
```

and fresh scans for

```text
sorry
sorryAx
explicit axiom
new warnings
```

Existing unrelated warnings are to be reported separately, not attributed to Phase 17.

Write the implementation report to

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-017.md
```

## Non-goals

This phase does **not** prove:

```text
classGroupPTorsionFreeAt (TraceOneInt s_p) p
unit p-th-power surjectivity
regular-prime criteria
class number formulas
Kummer descent
general FLT
```

The purpose is solely to determine whether the arbitrary-prime Phase-13 TraceOne carrier is the correct maximal quadratic order and can therefore enter the already-green ideal/class-group arithmetic kernel honestly.
