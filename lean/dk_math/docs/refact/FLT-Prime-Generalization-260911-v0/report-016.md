# FLT prime-generalization Phase 16 — principal ideal to element-power bridge

## Scope and outcome

This report records the bounded implementation requested by
instruction-016.md.  The production module is neutral: it does not import
`DkMath.FLT.*`, Kummer receivers, a fixed prime, or `TraceOneInt`.

The requested bridge layers are green:

~~~
PGEN-PRINCIPAL-IDEAL-ELEMENT-BRIDGE-GREEN
PGEN-IDEAL-TO-EXACT-POWER-CONDITIONAL-GREEN
~~~

The exact-power result is explicitly conditional on p-th-power surjectivity
of the unit sector.  No arbitrary unit is silently absorbed into a p-th
power.

## A. Pinned API audit

The audit was performed against the pinned Mathlib checkout and the current
Phase-14/15 production modules.

The principal-ideal declarations used by the implementation are:

~~~
Ideal.span_singleton_eq_span_singleton
Ideal.span_singleton_pow
Submodule.IsPrincipal.generator
Ideal.span_singleton_generator
~~~

The first declaration identifies equality of principal ideals with
`Associated` elements.  The generator and power declarations give
`span {gamma} = I` and `I^p = span {gamma^p}`.

The existing specialized p=7 declarations were also compared:

~~~
DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.unitMulPowOfSpanEqPow
DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.exists_mul_pow_of_span_eq_mul_pow
~~~

They express the same unit-times-power and unit-absorbed element routes on a
specialized degree-six carrier.  They are audit comparators only; the new
neutral module does not import them.

## B. Production module and local principal bridge

The new production module is:

~~~
DkMath/Lib/NumberTheory/PrincipalIdealPower.lean
~~~

Its imports are limited to the neutral Phase-14 and Phase-15 modules:

~~~
import DkMath.Lib.NumberTheory.IdealPowerFactor
import DkMath.Lib.NumberTheory.PowerFactor
~~~

The module provides:

~~~
associated_of_span_singleton_eq_span_singleton
exists_unit_mul_pow_of_span_eq_pow_of_isPrincipal
exists_associated_pow_of_span_eq_pow_of_isPrincipal
~~~

For `span {a} = I^p` and `I.IsPrincipal`, the proof selects the principal
generator `gamma`, obtains `span {gamma} = I`, compares
`span {a}` with `span {gamma^p}`, and retains the resulting unit explicitly:

~~~
∃ u gamma, IsUnit u ∧ span {gamma} = I ∧ a = u * gamma^p
~~~

The `Associated` wrapper is exposed separately so clients can choose whether
to retain association or the explicit unit witness.

No global PID instance is installed and no FLT-specific factor or axis is
introduced.

## C. Class-group principalization composition

The Phase-15 theorem
`ideal_isPrincipal_of_pow_isPrincipal_of_classGroupPTorsionFreeAt` is
composed with the local bridge in:

~~~
exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
~~~

Under a Dedekind-domain carrier, a nonzero `I`,
`classGroupPTorsionFreeAt R p`, and `span {a} = I^p`, the implementation
first observes that `I^p` is principal because it is equal to `span {a}`.
Phase 15 then principalizes `I`; Phase 16 performs the generator comparison.

The resulting statement is still only a unit-times-p-th-power statement.

## D. Exact power under an explicit unit hypothesis

The exact endpoint is:

~~~
exists_eq_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
~~~

It additionally assumes:

~~~
hunit : ∀ u : Rˣ, ∃ e : Rˣ, u = e ^ p
~~~

The proof passes the associated relation between `a` and `gamma^p` to the
existing Phase-14 theorem
`eq_pow_of_associated_pow_of_unit_pow_surjective`.  Thus the exact equality
`a = delta^p` is conditional on the stated unit-sector hypothesis; it is not
claimed from ideal principalization alone.

## E. Route comparison

| route | endpoint implemented here | remaining condition |
|---|---|---|
| principal ideal | `a = u * gamma^p` with `IsUnit u` | none beyond `I.IsPrincipal` |
| class group | same unit-times-power endpoint | nonzero ideal, Dedekind carrier, and class-group p-torsion-freeness |
| exact element power | `a = delta^p` | explicit p-th-power surjectivity of `Rˣ` |
| specialized p=7 PID | existing carrier-local theorem | specialized carrier and its own generator/unit API |
| specialized element route | existing unit absorption into the distinguished factor | product-shaped ideal identity and specialized carrier |

The routes are related mathematically but are not merged by a broad rename or
an FLT-specific import.

## F. Finite compatibility audit

The test-first probe is:

~~~
DkMathTest/FLT/Prime/PrincipalIdealPowerAuditProbe.lean
~~~

It checks the neutral theorem on the following currently available carriers:

| exponent/carrier | checked compatibility |
|---|---|
| `p = 3`, `TraceOneInt (-1)` | `IsDomain`, `EuclideanDomain`, GCD/PID/Dedekind owners and the neutral theorem application |
| `p = 5`, `GoldenInt` | `IsDomain`, `EuclideanDomain`, PID/Dedekind owners and the neutral theorem application |
| `p = 7`, `TraceOneInt (-2)` | `IsDomain`, `EuclideanDomain`, GCD/PID/Dedekind owners and the neutral theorem application |

The probe does not infer `TraceOneInt 1`, `TraceOneInt (-3)`, or
`TraceOneInt 3` instances from norm or coordinate declarations.  The
GoldenInt check is kept on the GoldenInt carrier and is not presented as a
TraceOne transfer.

## G. Boundary and non-goals

This phase does not prove FLT for any exponent, Kummer descent, a class-number
formula, regularity of a prime, a general TraceOne Dedekind-domain instance,
or unit p-th-power surjectivity on an arbitrary carrier.  It also does not
turn a norm equality into an element factorization or claim that the finite
compatibility audit closes the specialized FLT routes.

The axiom audit is:

~~~
DkMathTest/FLT/Prime/PrincipalIdealPowerAuditAxiomAudit.lean
~~~

It prints the axioms of every new production declaration.  The result is the
standard inherited `propext`, `Classical.choice`, and `Quot.sound` set; no
new explicit axiom, `sorry`, or `sorryAx` is used by the Phase-16 production
module.

## Verification

The focused verification targets are:

~~~
lake build DkMath.Lib.NumberTheory.PowerFactor
lake build DkMath.Lib.NumberTheory.IdealPowerFactor
lake build DkMath.Lib.NumberTheory.PrincipalIdealPower
lake build DkMathTest.FLT.Prime.PrincipalIdealPowerAuditProbe
lake build DkMathTest.FLT.Prime.PrincipalIdealPowerAuditAxiomAudit
lake build DkMath.FLT.Seven
git diff --check
~~~

The source audit also checks the new Phase-16 production and test files for
`sorry`, `sorryAx`, and explicit `axiom` declarations, and checks that the
production module has no `DkMath.FLT` import.

The focused builds replay the pre-existing warning at
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147`; no corresponding
warning or forbidden construct occurs in the new Phase-16 sources.
