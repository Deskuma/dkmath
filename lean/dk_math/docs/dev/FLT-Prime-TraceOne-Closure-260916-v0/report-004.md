# FPTC-004 report — generic imaginary residual coordinate receiver

## Outcome

```text
Outcome A — GENERIC IMAGINARY RESIDUAL COORDINATE RECEIVER GREEN
```

The generic imaginary exact-power endpoint is now consumed by a thin
FLT-side coordinate receiver.  It uses FPTC-003 with `beta = 1` and
`r = p`, exposing exact integer equations for the residual coordinates.  The
p=7 class-group-closed route and a p=11 conditional route are both audited.

No final contradiction, class-number theorem, real-sector elimination,
p=3/p=5 adapter, generic counterexample routing, or general FLT theorem was
implemented.

## Repository and scope audit

Work was performed on
`research/FLT-Prime-TraceOne-Closure-260916-v0`.  The attached instruction was
treated as the bounded implementation contract, separate from the user's
request.  The FPTC-000 through FPTC-003 reports and the specified packet,
TraceOne, discriminant, and conditional-endpoint modules were inspected before
editing.

The neutral-to-FLT dependency direction is:

```text
DkMath.Lib.NumberTheory.TraceOnePowerLanding
        ↓
DkMath.FLT.Prime.PrimeTraceOneCoordinateReceiver
```

The new production module imports no `DkMath.ABC.*` module and does not import
an FLT7 final contradiction theorem.  Its p=7 regression reuses the existing
structural class-group closure endpoint.

## Exact API audit

The focused audit file is
`DkMathTest/FLT/Prime/PrimeTraceOneImaginaryCoordinateReceiverApiAudit.lean`.
The current declarations confirmed by `#check` are:

```text
DkMath.Lib.NumberTheory.traceOnePowCoords (s m n : ℤ) : ℕ → ℤ × ℤ

DkMath.Lib.NumberTheory.traceOne_pow_coordinates (s m n : ℤ) (r : ℕ) :
  (⟨m, n⟩ : TraceOneInt s) ^ r =
    ⟨(traceOnePowCoords s m n r).1,
     (traceOnePowCoords s m n r).2⟩

DkMath.Lib.NumberTheory.traceOne_pow_core_landing_iff
  {s : ℤ} {alpha beta : TraceOneInt s} {r : ℕ}
  (hNorm : norm beta ≠ 0) :
  (∃ gamma, alpha = beta * gamma ^ r) ↔
    ∃ m n,
      (alpha * conj beta).fst = norm beta * (traceOnePowCoords s m n r).1 ∧
      (alpha * conj beta).snd = norm beta * (traceOnePowCoords s m n r).2
```

The existing generic and p=7 exact-power endpoints are:

```text
DkMath.FLT.Prime.exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket
  (... P0 P Q) (hp7 : 7 ≤ p) (hmod : p % 4 = 3) :
  classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p →
    ∃ delta, Q.residual = delta ^ p

DkMath.FLT.Prime.exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket_seven
  (... P0 P Q) :
  ∃ delta, Q.residual = delta ^ 7

DkMath.FLT.Prime.classGroupPTorsionFreeAt_traceOneNegTwo_seven :
  classGroupPTorsionFreeAt (TraceOneInt (-2)) 7
```

The exact endpoint signatures contain the existing local `Fact`, `Field`,
`IsDomain`, and `IsDedekindDomain` `let` bindings for the prime TraceOne
carrier.  The new receiver preserves those bindings in its generic theorem
statement instead of manufacturing a new typeclass façade.

The packet fields audited in
`DkMath/FLT/Prime/PrimeTraceOneStrippedIdeal.lean` include:

```text
Q.parent : TraceOneInt (signedPrimeParameter p)
Q.residual : TraceOneInt (signedPrimeParameter p)
Q.axis_eq : Q.parent = discrAxis (signedPrimeParameter p) * Q.residual
Q.parent_coordinate_coprime
Q.residual_coordinate_coprime
Q.residual_norm_ne_zero
Q.residual_axis_terminal
Q.residual_norm_pow : ∃ k : ℤ, norm Q.residual = k ^ p
Q.residual_conj_ideal_coprime
Q.idealRoot
Q.idealRoot_nonzero
Q.residual_span_eq : Ideal.span ({Q.residual} : Set _) = Q.idealRoot ^ p
```

The coordinate provenance packet supplies `P.coord`, `P.coord_norm_eq`, and
the retained integral polynomial coordinates.  These are available for later
arithmetic consumers but are not used to assert an obstruction in this
checkpoint.

## Implemented production API

The new module is
`DkMath/FLT/Prime/PrimeTraceOneCoordinateReceiver.lean`.  Its generic
receiver is:

```lean
theorem exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket
    {L : Type*} [Field L] [Algebra ℚ L]
    {p g u x : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P0 : PrimeAdicFactorPacket p g u x)
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P)
    (hp7 : 7 ≤ p) (hmod : p % 4 = 3) :
    let ... := existing TraceOne field/domain instances
    classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p →
      ∃ m n : ℤ,
        Q.residual.fst =
          (traceOnePowCoords (signedPrimeParameter p) m n p).1 ∧
        Q.residual.snd =
          (traceOnePowCoords (signedPrimeParameter p) m n p).2
```

The full source statement retains the exact four existing `let` bindings;
they are abbreviated above only for readability.

The proof first calls
`exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket`, obtaining
`Q.residual = delta ^ p`.  It then calls
`traceOne_pow_core_landing_iff` with

```text
alpha = Q.residual
beta  = 1
r     = p.
```

The nonzero-norm obligation is discharged by simplification of
`norm (1 : TraceOneInt s)`.  The resulting equations initially contain
`Q.residual * conj 1` and `norm 1`; `simpa` with the existing `conj` and `norm`
definitions reduces them to the raw equations:

```text
Q.residual.fst = (traceOnePowCoords s m n p).1
Q.residual.snd = (traceOnePowCoords s m n p).2
```

Thus FPTC-003 is a genuine dependency, and no ad hoc power-coordinate proof,
division, or fraction field is introduced.

## p=7 and p=11 regressions

The production p=7 specialization is:

```lean
theorem exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket_seven
    (... P0 P Q) :
    ∃ m n : ℤ,
      Q.residual.fst =
          (traceOnePowCoords (signedPrimeParameter 7) m n 7).1 ∧
        Q.residual.snd =
          (traceOnePowCoords (signedPrimeParameter 7) m n 7).2
```

It calls the generic receiver at `p = 7` and supplies
`classGroupPTorsionFreeAt_traceOneNegTwo_seven`.  The audit explicitly proves:

```text
signedPrimeParameter 7 = -2
```

No caller-supplied class-group hypothesis and no specialized FLT7 final
contradiction theorem are used.  Status:

```text
FPTC-P7-IMAGINARY-COORDINATE-RECEIVER-GREEN
```

The p=11 audit proves:

```text
11 % 4 = 3
signedPrimeParameter 11 = -3
```

It applies the same generic receiver with `p = 11` and retains the explicit
conditional assumption
`classGroupPTorsionFreeAt (TraceOneInt (-3)) 11`.  No class-number fact is
proved or assumed.  Status:

```text
FPTC-P11-CONDITIONAL-COORDINATE-RECEIVER-GREEN
```

## Consumer-shape audit

For every generic imaginary residual endpoint, the new receiver makes the
following exact arithmetic surface available:

```text
Q.residual.fst = A_p(s, m, n)
Q.residual.snd = B_p(s, m, n)
```

where
`(A_p, B_p) = traceOnePowCoords (signedPrimeParameter p) m n p`.

The packet already constrains these coordinates through:

```text
residual_coordinate_coprime : IsCoprime Q.residual.fst Q.residual.snd
residual_norm_ne_zero       : norm Q.residual ≠ 0
residual_axis_terminal      : ¬ discrAxis s ∣ Q.residual
residual_norm_pow           : ∃ k, norm Q.residual = k ^ p
axis_eq                     : parent = discrAxis s * residual
residual_conj_ideal_coprime : conjugate residual ideals are coprime
residual_span_eq            : residual ideal = idealRoot ^ p
```

The coordinate receiver does not combine these facts into a contradiction.
In particular, no claim is made that the recurrence image is empty, that a
coordinate is divisible by the discriminant axis, or that the norm condition
alone forces a root.  The likely next arithmetic consumer is the pair of exact
coordinate equations together with `residual_coordinate_coprime`,
`residual_axis_terminal`, and the norm-power equation.

## Failed probes and import decisions

The first production probe failed because the definitions of
`PrimeTraceOneCoordinatePacket` and the TraceOne rational/domain helpers are
in namespaces opened by `PrimeTraceOneConditionalDescent`, not re-exported as
open names by the imported module.  Adding explicit opens for
`CyclotomicQRTraceOneBridge` and `TraceOneQuadraticField` fixed the import
boundary without changing theorem content.

The first API audit probe had the same missing-open issue for packet and field
names.  The test layer now opens the relevant namespaces explicitly.  No
failed mathematical proof or cancellation/API obstruction remained.

The p=7-specific source is imported only through
`PrimeTraceOneClassGroupClosure` for the existing structural discharge; no
specialized final contradiction is imported or called.  The neutral
`TraceOnePowerLanding` module is unchanged by this checkpoint.

## Axiom audit

The focused axiom audit is
`DkMathTest/FLT/Prime/PrimeTraceOneCoordinateReceiverAxiomAudit.lean`.  The
exact output for both the generic receiver and p=7 specialization is:

```text
depends on axioms:
[propext, Classical.choice, Quot.sound]
```

These are inherited standard Lean/Mathlib foundations.  No DkMath-defined
axiom, `sorry`, `sorryAx`, `admit`, or `unsafe` was introduced.

## Validation

Successful focused builds under Lean 4.34:

```text
lake build DkMath.Lib.NumberTheory.TraceOnePowerLanding
lake build DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
lake build DkMath.FLT.Prime.PrimeTraceOneClassGroupClosure
lake build DkMath.FLT.Prime.PrimeTraceOneCoordinateReceiver
lake build DkMathTest.FLT.Prime.PrimeTraceOneImaginaryCoordinateReceiverApiAudit
lake build DkMathTest.FLT.Prime.PrimeTraceOneCoordinateReceiverAxiomAudit
lake build DkMath.Lib
```

All listed builds completed successfully.  Existing style-linter warnings in
the dependency graph remain non-fatal.  `git diff --check` and no-index checks
for the new untracked files produced no whitespace diagnostics.  The
repository-standard forbidden-source scan over edited production and test
Lean files found no forbidden declaration.

## Boundary and next frontier

The new checked boundary is:

```text
generic imaginary residual exact p-th power
        -> exact TraceOne integer recurrence coordinates
```

The next checkpoint may inspect these equations for an arithmetic obstruction.
This report does not promote that future inspection into a contradiction or a
general FLT result.
