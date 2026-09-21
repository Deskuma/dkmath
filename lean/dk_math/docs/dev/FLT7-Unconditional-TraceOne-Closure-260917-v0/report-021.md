# FLT7TC-005R16 — Exact root norm and canonical μ₇ first-order phase normalization

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-021.md` was used as the bounded implementation
contract, separately from the user's request. The implementation remains on
the direct cyclotomic root path and does not assume a global residue provider
or a contradiction receiver.

## Implementation

The new production module is
`DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicRootPhaseNormalization.lean`.
It is exported by the `DkMath.FLT.Seven` facade. The API and axiom checks are
in:

```text
DkMathTest/FLT/SevenPrimeTraceOneDirectCyclotomicRootPhaseNormalizationApi.lean
DkMathTest/FLT/SevenPrimeTraceOneDirectCyclotomicRootPhaseNormalizationAxiom.lean
```

The exact-root packet reuses the R15 chosen-quotient witness and records

```text
Q₁ = gamma^7,
directLinearFactor = ramifiedUniformizer * gamma^7,
gamma ∉ ramifiedPrime,
cyclotomicNormHom gamma = residualRoot.
```

The norm equality is proved as an integer equality, including the sign, by
injectivity of the odd seventh-power map on `ℤ`; it is not obtained by
discarding the norm sign.

For a generic non-ramified cyclotomic scalar, `scalarLift` is the integer
representative of its first ramified residue. The module proves the
first-order μ₇ phase system over `Fin 7`, together with existence and
uniqueness of its phase. Multiplication by the selected seventh root of unity
produces a normalized root packet that preserves the exact seventh power and
the residual norm.

The explicit binomial calculation uses
`7 = ramifiedUniformizer^6 * ramifiedSevenUnit`. A first-order scalar lift
therefore gives

```text
gammaNorm^7 - scalarLift(gamma)^7 ∈ ramifiedPrime^8.
```

The degree-six rational norm then proves

```text
49 ∣ endpointRight - scalarLift(gamma)^7,
```

and the corresponding equality in `ZMod 49`.

## Bounded audit and outcome

The production source, API source, and axiom source contain no `sorry`,
`sorryAx`, `admit`, `unsafe`, or project `axiom`. The decisive theorem audit
reports only `propext`, `Classical.choice`, and `Quot.sound`.

No six-residue classifier was added because the exact mod-49 congruence gate
is already exposed and the remaining nonvanishing/unit condition is not a
receiver-free contradiction. The historical `CubicGapSeventhShapeReceiver`
route was not used. The checkpoint is therefore:

**Outcome B — NORMALIZED ROOT PACKET GREEN; EXACT NORM AND MOD-49 SEVENTH-
POWER GATE GREEN; RESIDUE/PROVIDER AND GLOBAL FLT7 BRANCHES REMAIN OPEN.**

## Validation

The focused builds were run successfully:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicRootPhaseNormalization
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicRootPhaseNormalizationApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicRootPhaseNormalizationAxiom
```
