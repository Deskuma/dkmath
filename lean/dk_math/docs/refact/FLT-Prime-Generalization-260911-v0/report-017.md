# FLT prime-generalization Phase 17 — TraceOne rational field and maximal-order transport

## Scope and outcome

This report records the bounded implementation requested by
`instruction-017.md`.  The implementation remains neutral: it does not prove
FLT, class-group torsion-freeness, unit p-th-power surjectivity, Kummer
descent, or any global prime-exponent theorem.

The requested layers are green:

~~~
PGEN-TRACEONE-QUADRATIC-FIELD-GREEN
PGEN-TRACEONE-MAXIMAL-ORDER-GREEN
PGEN-TRACEONE-DEDEKIND-GREEN
~~~

## A. Rational companion API

The production module is:

~~~
DkMath/NumberTheory/TraceOneQuadraticField.lean
~~~

It defines the neutral companion

~~~
TraceOneRat s := QuadraticAlgebra ℚ (s : ℚ) 1
~~~

and the coordinate-preserving ring homomorphism

~~~
traceOneRatHom s : TraceOneInt s →+* TraceOneRat s
~~~

The implementation proves injectivity, scalar-map compatibility, the `tau`
to `omega` map, conjugation compatibility, and trace/norm compatibility.
The rational quadratic trace is exposed as `quadraticTrace`.

`TraceOneInt` is also given an explicit finite-module witness over `ℤ` using
its two coordinate projections.  This is used only for the integral-image
direction and does not install a PID or Euclidean-domain instance.

## B. Arbitrary odd-prime field realization

For a prime `p` with `p ≠ 2`, the module proves the rational-root obstruction
for the companion polynomial:

~~~
traceOneRat_no_rational_root
~~~

The proof reduces a hypothetical rational square root of the signed prime
discriminant through the Phase-12 rational denominator lemma and separates
the positive and negative signed-prime cases.

The resulting field structure is exposed as:

~~~
traceOneRatField
traceOneRat_numberField
~~~

`traceOneRat_numberField` returns an explicit field instance together with a
`NumberField` structure.  No global field instance is installed for all
`TraceOneRat s`; this keeps the conditional field realization from creating
instance-search loops.

## C. Integral closure / maximal order

The main theorem is:

~~~
traceOneRat_isIntegralClosure
~~~

It proves

~~~
IsIntegralClosure (TraceOneInt (signedPrimeParameter p)) ℤ
  (TraceOneRat (signedPrimeParameter p))
~~~

The forward direction maps an integral element through quadratic conjugation,
extracts integer trace and norm using the existing rational-integral bridge,
and applies the identity

~~~
T^2 - D_p * b^2 = 4*N.
~~~

The Phase-12 signed-prime square lemma makes the second rational coordinate
an integer.  The parity of the displayed identity then makes `(T - b) / 2`
an integer, recovering the first coordinate.  The reverse direction uses the
explicit finite `ℤ`-module structure of `TraceOneInt` and maps integrality
through `traceOneRatHom`.

## D. Ring-of-integers and Dedekind transport

The module provides:

~~~
traceOneRat_ringOfIntegers_equiv
traceOneRat_isDedekindDomain
~~~

The first packages the `NumberField.RingOfIntegers.equiv` transport to
`TraceOneInt`.  The second supplies the corresponding
`IsDedekindDomain (TraceOneInt (signedPrimeParameter p))` under the explicit
field, number-field, and integral-closure witnesses.  The domain instance is
pulled back through the injective coordinate map; no broad global instance is
added.

## E. Finite strict cases

`TraceOneQuadraticFieldProbe.lean` checks the parameter values:

| prime | signed parameter |
|---|---:|
| `3` | `-1` |
| `5` | `1` |
| `7` | `-2` |
| `11` | `-3` |
| `13` | `3` |

The arbitrary-prime integral-closure and field APIs are instantiated in the
probe, while the Dedekind audit also checks a concrete `p = 3` instance.  The
`p = 5` `TraceOneInt 1` carrier remains distinct from `GoldenInt`.

## F. Conditional Phase-15/16 composition

`TraceOneDedekindAudit.lean` checks the arbitrary-prime composition on the
TraceOne carrier.  The exact element-power endpoint remains conditional on
both:

~~~
classGroupPTorsionFreeAt R p
∀ u : Rˣ, ∃ e : Rˣ, u = e ^ p
~~~

No class-group or unit-sector statement is inferred from the maximal-order
transport.

## G. Axiom and forbidden-construct audit

The audit file is:

~~~
DkMathTest/FLT/Prime/TraceOneDedekindAxiomAudit.lean
~~~

The new declarations use the standard inherited
`propext`, `Classical.choice`, and `Quot.sound` axioms.  The fresh source scan
found no `sorry`, `sorryAx`, `admit`, `axiom`, or `unsafe` occurrence in the
new production or test files.

## Verification

The exact focused build requested by `instruction-017.md` passed:

~~~
lake build DkMath.NumberTheory.TraceOneQuadraticField \
  DkMath.NumberTheory.CyclotomicQRTraceOneBridge \
  DkMath.Lib.NumberTheory.IdealPowerFactor \
  DkMath.Lib.NumberTheory.PrincipalIdealPower \
  DkMathTest.FLT.Prime.TraceOneQuadraticFieldProbe \
  DkMathTest.FLT.Prime.TraceOneDedekindAudit \
  DkMathTest.FLT.Prime.TraceOneDedekindAxiomAudit \
  DkMath.FLT.Seven
~~~

`git diff --check` passed, and the fresh warning/error scan of that build log
was empty.
