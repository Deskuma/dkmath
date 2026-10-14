# GCNB-008 / instruction-005 — p=3/5/7 dedicated-carrier calibration

Branch: **research/GTail-Cyclotomic-Norm-Bridge-260922-v0**

Read first:

- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/README.md
- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/ROADMAP.md
- docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/report-004.md
- DkMath/FLT/Prime/PrimeCyclotomicTraceOne.lean
- DkMath/FLT/ThreeTraceOneBridge.lean
- DkMath/FLT/Three/EisensteinLibBridge.lean
- DkMath/FLT/Five/TraceOneBridge.lean
- DkMath/NumberTheory/StructuralArithmetic/GNBridge.lean
- DkMath/FLT/Seven/QuadraticBridge.lean

## 1. Mission

GCNB-006 established the generic scalar diagram

~~~text
cyclotomic linear factor
        ↓
principal ideal I
        ↓
Ideal.absNorm I
        ||
TraceOne.norm (generic coordinate packet)
        ↑
arbitrary-prime QR/QNR TraceOne shadow
~~~

with both scalar values equal to the same generic GN/GTail value.

GCNB-008 is a calibration checkpoint.

It must compare this generic scalar with the already-existing dedicated
p = 3, 5, 7 carriers:

~~~text
p = 3  : Eisenstein / TraceOneInt (-1)
p = 5  : Golden / TraceOneInt 1
p = 7  : explicit cubic coordinate / TraceOneInt (-2)
~~~

The purpose is to prove that the new general bridge recovers the established
fixed-prime norm values.

Do **not** refactor the completed FLT3 or FLT5 endpoint proofs onto the new
generic API in this checkpoint.

Do **not** claim coordinate-element equality unless it is already a checked
definitional fact.

## 2. Recommended module placement

Prefer a dedicated compatibility module:

~~~text
DkMath/FLT/Prime/PrimeCyclotomicCalibration.lean
~~~

It may import:

~~~text
DkMath.FLT.Prime.PrimeCyclotomicTraceOne
DkMath.FLT.ThreeTraceOneBridge
DkMath.FLT.Three.EisensteinLibBridge
DkMath.FLT.Five.TraceOneBridge
DkMath.NumberTheory.StructuralArithmetic.GNBridge
DkMath.FLT.Seven.QuadraticBridge
~~~

Keep the calibration dependency in the FLT layer.

Do not make CFBRC or the neutral NumberTheory cyclotomic carrier depend on the
fixed-prime FLT modules.

## 3. p = 3 calibration

For a cyclotomic extension K/Q with a primitive cube root zeta and natural
gap/base coordinates g,u, prove that the generic cyclotomic ideal norm equals
the established p=3 TraceOne/Eisenstein scalar.

Target shape:

~~~lean
theorem cyclotomicIdeal_absNorm_eq_traceOneNorm_three
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    [IsCyclotomicExtension {3} Rat K]
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 3)
    (g u : Nat) :
    (Ideal.absNorm
      (cyclotomicLinearFactorIdeal hzeta g u) : Int)
      =
    TraceOneQuadratic.norm
      (⟨((g + u : Nat) : Int), (u : Int)⟩ : TraceOneInt (-1))
~~~

Use the existing theorem:

~~~text
DkMath.FLT.GN_three_sub_eq_traceOneNorm_negOne
~~~

with endpoint a = g+u and base b = u.

The arithmetic side should reduce by:

~~~text
(g + u) - u = g.
~~~

Also audit the FLT3 carrier alignment:

~~~text
TraceOneInt (signedPrimeParameter 3) = TraceOneInt (-1)
~~~

via the existing Eisenstein bridge.

If a direct theorem to the production FLT3 Eisenstein coordinate is
essentially free, add it. Otherwise the established TraceOneInt(-1) norm is
sufficient for the calibration.

Do not require g != 0 or u != 0.

## 4. p = 5 calibration

Use the existing exact bridge:

~~~text
DkMath.NumberTheory.StructuralArithmetic.GN5_eq_generic_GN
~~~

and:

~~~text
DkMath.FLT.Five.GN5_eq_traceOneNorm_squareLink.
~~~

Prove that the generic cyclotomic ideal norm at p=5 equals the dedicated
square-link Golden/TraceOne scalar.

Conceptual target:

~~~text
(Ideal.absNorm I_5 : Int)
 =
norm
  ( < (g+u)^2 + u^2,
      (g+u)*u > : TraceOneInt 1 ).
~~~

Use the exact casts already present in
GN5_eq_traceOneNorm_squareLink rather than duplicating the polynomial.

If cheap, also expose the same value through the Golden API:

~~~text
GoldenNorm / goldenNorm
~~~

using the existing TraceOne bridge.

Do not rebuild the FLT5 descent or its Euclidean/unit infrastructure.

## 5. p = 7 calibration

Use:

~~~text
DkMath.FLT.Seven.GN_seven_sub_eq_traceOneNorm_negTwo
~~~

with endpoint g+u and base u.

Prove:

~~~text
(Ideal.absNorm I_7 : Int)
 =
norm
  (cyclotomicSevenToTraceOne
    ((g+u : Nat) : Int)
    (u : Int)).
~~~

This is the dedicated p=7 explicit cubic-coordinate calibration.

Again, do not require positive g or u.

The theorem must be a scalar equality only.

## 6. Generic TraceOne packet ↔ dedicated coordinate norm

For each p = 3, 5, 7, connect an arbitrary:

~~~text
P : PrimeTraceOneCoordinatePacket K p zeta hzeta
~~~

to the corresponding dedicated fixed-prime scalar.

The intended theorem family is conceptually:

~~~text
norm (P.coord (g+u) u)
  =
dedicatedNorm_p(g,u).
~~~

Derive this by transitivity through:

~~~text
norm generic coord
  = cast (Ideal.absNorm I)
  = dedicated fixed-prime norm.
~~~

Do not prove equality of the coordinates themselves.

This is the most important calibration of GCNB-008: it shows that the
arbitrary-prime QR/QNR shadow recovers the same scalar as the older dedicated
p=3/5/7 constructions.

## 7. Parameter calibration

Record or test the signed parameters:

~~~text
signedPrimeParameter 3 = -1
signedPrimeParameter 5 = 1
signedPrimeParameter 7 = -2
~~~

Use existing named theorems where available; otherwise a small norm_num test is
enough.

Do not introduce duplicate production theorems solely for numerals unless they
improve API readability.

## 8. Optional ideal-norm normal-form calibration

If cheap, specialize the existing ramified PrimeAdicPowerSplit theorem at
p=3/5/7 and show that the dedicated fixed-prime norm receives exactly the same
normal form:

~~~text
p * b^p.
~~~

This is optional.

Do not construct fake FLT counterexamples just to exercise it.

## 9. What this checkpoint must NOT do

Do not:

- alter the completed FLT3 or FLT5 proof endpoint;
- claim the generic p=3 coordinate packet equals the production Eisenstein
  coordinate element;
- claim the generic p=5 packet equals the Golden element;
- claim the generic p=7 packet equals cyclotomicSevenToTraceOne as an element;
- identify cyclotomic ideals with TraceOne ideals;
- infer local prime-ideal multiplicities;
- infer principalization or class-group facts;
- reopen the FLT7 contradiction tower;
- claim arbitrary-prime FLT.

This is a calibration checkpoint only.

## 10. Tests

Add a focused test module, suggested:

~~~text
DkMathTest/FLT/Prime/PrimeCyclotomicCalibration.lean
~~~

Required checks:

1. p=3 ideal absNorm equals the dedicated TraceOneInt(-1) norm;
2. p=5 ideal absNorm equals the dedicated square-link TraceOneInt(1) norm;
3. p=7 ideal absNorm equals the explicit cyclotomicSevenToTraceOne norm;
4. for each p=3/5/7, generic PrimeTraceOneCoordinatePacket norm equals the
   dedicated fixed-prime norm;
5. include zero-boundary calibration where natural and cheap;
6. #print axioms for every new public theorem.

## 11. Validation

Run at least:

~~~text
lake build DkMath.FLT.Prime.PrimeCyclotomicCalibration
lake build DkMathTest.FLT.Prime.PrimeCyclotomicCalibration
lake build DkMath.FLT.Prime
lake build DkMath.FLT.Three
lake build DkMath.FLT.Five
lake build DkMath.FLT.Seven.QuadraticBridge
lake build DkMath
git diff --check
~~~

No:

~~~text
sorry
admit
sorryAx
new axiom
unsafe proof shortcut
~~~

Pre-existing warnings outside the changed dependency surface remain outside
this checkpoint.

## 12. Report

Create:

~~~text
docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/report-005.md
~~~

Classify:

### Outcome A — p=3/5/7 scalar calibration complete

All three dedicated fixed-prime norm carriers are proved equal to the generic
cyclotomic ideal absNorm, and the arbitrary-prime TraceOne packet norm is
proved equal to each corresponding dedicated scalar.

### Outcome B — scalar calibration complete, one dedicated wrapper omitted

The common GN scalar is checked at all three primes, but one historical
carrier wrapper would require disproportionate legacy dependency work. Record
the exact boundary without fabricating element equality.

### Outcome C — a fixed-prime API is not definitionally aligned

Record the exact coordinate/convention mismatch and the minimal existing
scalar theorem. Do not assert coordinate equality.

## 13. Completion gate

GCNB-008 is complete when the following is kernel checked for p=3,5,7:

~~~text
dedicated fixed-prime norm
          =
generic GN scalar
          =
cyclotomic ideal absNorm
          =
generic TraceOne packet norm.
~~~

After GCNB-008, do not immediately reopen FLT7.

First review the completed generalization stack and decide whether:

1. GCNB-004L local prime-ideal multiplicity aggregation is now the missing
   theorem that could advance the deferred degree-six FLT7 carrier cutoff; or
2. the branch should close and FLT7 re-entry remain blocked.

GCNB-007 complex conjugate-pair decomposition remains optional and independent.
