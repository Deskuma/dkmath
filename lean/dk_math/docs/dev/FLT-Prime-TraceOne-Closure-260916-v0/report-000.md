# FPTC-000 report — class-group discharge audit and p=7 regression

## Outcome

```text
Outcome A — P7 CLASS-GROUP HYPOTHESIS DISCHARGED STRUCTURALLY
```

The structural p=7 class-group result and the generic Phase-26 residual
exact-power composition are green.  No specialized `FLT_d7` contradiction
theorem is used.

## Repository and scope audit

The current checkout is on
`research/FLT-Prime-TraceOne-Closure-260916-v0`, at the branch and base commit
specified by `instruction-000.md`.  The instruction was treated as the bounded
implementation contract.  In particular, this checkpoint does not attempt
class-number estimates for arbitrary primes, real-sector elimination, a
general FLT theorem, arbitrary-power TraceOne coordinates, or q-adic global
descent.

The required source documents were read before editing:

- repository `README.md` and `AGENT.md`;
- `lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/README.md`;
- `lean/dk_math/docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/ROADMAP.md`;
- `docs/refact/FLT-Prime-Generalization-260911-v0/summary-026.md`;
- `docs/refact/FLT-Prime-Generalization-260911-v0/report-026.md`.

## Exact API evidence

### Existing DkMath declarations

The class-group definition and principalization layer are in
`DkMath/Lib/NumberTheory/IdealPowerFactor.lean`:

```text
DkMath.Lib.NumberTheory.classGroupPTorsionFreeAt
DkMath.Lib.NumberTheory.classGroup_eq_one_of_pow_eq_one_of_classGroupPTorsionFreeAt
DkMath.Lib.NumberTheory.ideal_isPrincipal_of_classGroup_eq_one
DkMath.Lib.NumberTheory.ideal_isPrincipal_of_classGroupPTorsionFreeAt
DkMath.Lib.NumberTheory.ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt
```

The element and sector compositions are in
`DkMath/Lib/NumberTheory/PrincipalIdealPower.lean` and
`DkMath/Lib/NumberTheory/UnitPowerSector.lean`:

```text
DkMath.Lib.NumberTheory.exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
DkMath.Lib.NumberTheory.exists_sector_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
```

The generic Phase-26 endpoint is in
`DkMath/FLT/Prime/PrimeTraceOneConditionalDescent.lean`:

```text
DkMath.FLT.Prime.exists_unit_mul_pow_of_primeTraceOneStrippedIdealPacket
DkMath.FLT.Prime.exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket
DkMath.FLT.Prime.exists_sector_mul_pow_of_primeTraceOneRealStrippedIdealPacket
```

The p=7 Euclidean infrastructure is
`DkMath/FLT/Seven/QuadraticEuclidean.lean`:

```text
DkMath.FLT.Seven.traceOneNegTwoEuclideanDomain
```

### Mathlib API and import direction

The current Mathlib 4.34 API is:

```text
Mathlib.RingTheory.ClassGroup.Basic
  card_classGroup_eq_one
  card_classGroup_eq_one_iff
  ClassGroup.mk0_eq_one_iff
  FractionalIdeal.isPrincipal.of_isPrincipal_pow_of_coprime
  Ideal.IsPrincipal.of_isPrincipal_pow_of_coprime

Mathlib.RingTheory.PrincipalIdealDomain
  EuclideanDomain.instIsPrincipalIdealRing

Mathlib core/group APIs
  Fintype.card_eq_one_iff
  orderOf_dvd_of_pow_eq_one
  orderOf_dvd_card
  orderOf_eq_one_iff
```

The resulting dependency direction is:

```text
DkMath.Lib.NumberTheory.IdealPowerFactor
  -> DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
  -> DkMath.FLT.Prime.PrimeTraceOneClassGroupClosure
```

The neutral module does not import FLT3, FLT5, or FLT7.  Only the FLT-side
regression imports the p=7 Euclidean instance.

## Implemented changes

### Neutral bridge

Added
`DkMath/Lib/NumberTheory/ClassGroupTorsionBridge.lean` with:

```lean
classGroupPTorsionFreeAt_of_subsingleton_classGroup
subsingleton_classGroup_of_isPrincipalIdealRing
classGroupPTorsionFreeAt_of_isPrincipalIdealRing
```

The first theorem is independent of `p` mathematically.  The second uses
Mathlib's `card_classGroup_eq_one` and `Fintype.card_eq_one_iff`; it does not
introduce a global `Subsingleton (ClassGroup R)` instance.  The third composes
the two theorem-level bridges.

### p=7 regression

Added
`DkMath/FLT/Prime/PrimeTraceOneClassGroupClosure.lean` with

```lean
classGroupPTorsionFreeAt_traceOneNegTwo_seven
```

Its proof uses the existing `TraceOneInt (-2)` Euclidean domain and the
neutral principal-ideal bridge.  The audit file also proves
`signedPrimeParameter 7 = -2` by computation, so the carrier normalization is
explicitly checked without importing the FLT7 final theorem.

### Focused audit

Added
`DkMathTest/FLT/Prime/PrimeTraceOneClassGroupClosureApiAudit.lean`.
It contains the requested `#check` declarations, `#synth` checks for the
Euclidean and principal-ideal instances, and local examples for both the
subsingleton and p=7 structural implications.

## Compatibility repairs

The first attempt to build the generic endpoint exposed pre-existing Lean 4.34
API drift in its dependency chain.  The following local, meaning-preserving
repairs were applied:

1. `DkMath/NumberTheory/CyclotomicQRCoefficientDescent.lean` used the removed
   qualified projection `MvPolynomial.coeff`; the current projection is
   `P.coeff`.
2. `DkMath/NumberTheory/CyclotomicQRIntegralDescent.lean` had the same
   projection issue and passed an obsolete injectivity argument to
   `isIntegral_algebraMap_iff`.
3. `CyclotomicQRTraceOneBridge.lean` had further old qualified coefficient
   projections and deprecated coefficient rewrite lemmas.
4. `TraceOneQuadraticField.lean` needed explicit `Field`, `CommRing`,
   `Algebra`, and `IsIntegralClosure` arguments at
   `NumberField.RingOfIntegers.equiv`; otherwise Lean 4.34 selected a
   definitionally different class-instance diamond.
5. Several generic endpoint proofs required `dsimp` before introducing
   hypotheses because the result type contains nested local `let` bindings.

These repairs preserve the mathematical statements and allow the complete
generic target to build under Lean 4.34.  The remaining messages are warnings
only (style-linter notices and one deprecated complex import).

## p=7 generic exact-power composition

Added
`DkMath.FLT.Prime.exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket_seven`.
It calls the generic Phase-26 theorem, supplies the p=7 structural class-group
bridge, and explicitly normalizes
`signedPrimeParameter 7 = -2`.  It introduces no caller-supplied class-group
hypothesis and does not call a specialized FLT7 contradiction theorem.

## p=3 and p=5 scope audit only

For p=3, production has

```lean
abbrev EisensteinInt := TraceOneInt (-1)
```

in `DkMath/FLT/Three/EisensteinSubstrate.lean`.  The existing
`DkMath/FLT/Three/EisensteinLibBridge.lean` already records the signed
parameter alignment and exposes
`eisensteinCubeUnitPowerSectorSystem`.  No new adapter was implemented in
FPTC-000.

For p=5, `DkMath/FLT/Five/GoldenOrder.lean` defines a distinct `GoldenInt`
structure.  `DkMath/FLT/Five/TraceOneBridge.lean` supplies coordinate and norm
comparisons with `TraceOneInt 1`, but not a ring equivalence.  The likely future
bridge surface is therefore an explicitly audited ring equivalence followed by
transport of only the required unit-sector facts.  No p=5 adapter was added.

## Optional finite-cardinality criterion audit

The clean Mathlib route for the future criterion is the existing proof pattern
in `Mathlib/RingTheory/ClassGroup/Basic.lean`:

```text
orderOf_dvd_of_pow_eq_one
orderOf_dvd_card
orderOf_eq_one_iff
Nat.Coprime
```

The direct candidate is `FractionalIdeal.isPrincipal.of_isPrincipal_pow_of_coprime`
or its integral-ideal counterpart
`Ideal.IsPrincipal.of_isPrincipal_pow_of_coprime`.  The criterion itself was
not implemented; it remains FPTC-001.

## Validation

Successful focused builds:

```text
lake build DkMath.Lib.NumberTheory.ClassGroupTorsionBridge
lake build DkMath.NumberTheory.CyclotomicQRTraceOneBridge
lake build DkMath.NumberTheory.TraceOnePrimeUnitSectors
lake build DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
lake build DkMath.FLT.Prime.PrimeTraceOneClassGroupClosure
lake build DkMathTest.FLT.Prime.PrimeTraceOneClassGroupClosureApiAudit
lake build DkMathTest.FLT.Prime.PrimeTraceOneClassGroupClosureAxiomAudit
lake build DkMath.Lib
```

The successful
new bridge/regression sources contain no `sorry`, `sorryAx`, `admit`, explicit
axiom, or `unsafe`.  The successful structural route uses only the standard
Lean/Mathlib proof foundations; no DkMath-defined axiom was introduced.
