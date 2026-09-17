# FLT7TC-005R13 — Relative-norm-one unit reduction and residual μ₇ phase

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This checkpoint starts from the completed R12 module
`PrimeTraceOneDirectCyclotomicUnitCongruence.lean`.
Do not return to the historical receiver route, and do not use any theorem
whose decisive dependency contains `sorryAx`.

## Goal

R12 already provides, for the current counterexample-origin chosen quotient,

```text
Q₁ = unit * beta^7
unit ≡ m (mod 7),  7 ∤ m
quadraticNorm(unit) = realUnit^7
```

with the real-cubic unit class explicitly seventh-power.

Do **not** attack the full degree-six Kummer-unit lemma first.
Reduce it to the smallest relative-norm-one statement.

Let `v` be a real-cubic unit with

```text
quadraticNorm(unit) = v^7.
```

Using the unit map induced by `ofReal`, define conceptually

```text
delta := unit^2 * ofReal(v)^(-7).
```

Because `quadraticNorm(ofReal(v)) = v^2`, prove

```text
quadraticNorm(delta) = 1.
```

Also transport the existing mod-seven scalar congruence and seventh-power
scalarization to prove that `delta` is congruent modulo `(7)` to a
nonzero rational integer.

## Required checked interfaces

1. A concrete unit-level quadratic norm map for the degree-six carrier, or the
   thinnest local wrapper needed for this checkpoint.
2. Construction of the real-unit lift through `ofReal`.
3. A packet, conceptually:

```lean
structure DirectRelativeNormOnePhasePacket ... where
  sourceUnit : SevenCyclotomicDegreeSixInt.Ringˣ
  realNormRoot : SevenRealCubicIntˣ
  phase : SevenCyclotomicDegreeSixInt.Ringˣ
  sourceNorm_eq : ...
  phase_def : ...
  phase_norm_one : ...
  phase_congruentToRationalModSeven :
    DegreeSixUnitCongruentToRationalModSeven phase
```

Keep the actual theorem names/API minimal and repository-consistent.

## Narrow Kummer target

Introduce only as a specification if not immediately provable:

```lean
def RelativeNormOneKummerUnitLemmaAtSeven : Prop :=
  ∀ delta : SevenCyclotomicDegreeSixInt.Ringˣ,
    quadraticNormUnit delta = 1 ->
    DegreeSixUnitCongruentToRationalModSeven delta ->
    ∃ w : SevenCyclotomicDegreeSixInt.Ringˣ, delta = w ^ 7
```

Prove that this **narrow** target implies the existing
`DegreeSixKummerUnitLemmaAtSeven` for the R12 packet:

- if `delta = w^7`, then `unit^2` is a seventh power;
- use Bézout for exponents 2 and 7 (for example `1 = 4*2 - 1*7`) in the
  abelian unit group to conclude that `unit` itself is a seventh power.

Do not hand-wave this last group step; kernel-check it.

## Relative-norm-one classification audit

Attempt the narrow target by the cheapest honest route.

### Preferred route A — cyclotomic ring of integers

Audit whether the existing surjective map

```text
ringOfIntegersToRing :
  O_(Q(zeta_7)) -> SevenCyclotomicDegreeSixInt.Ring
```

can be upgraded to an equivalence cheaply.

Before building new basis machinery, search Mathlib and existing DkMath for a
theorem that a surjective integral map between these rank-six orders is
injective/equivalent, or for an existing integral power-basis equivalence.

If needed, an explicit `1,zeta,...,zeta^5` determinant/basis proof is
allowed, but do not make it the first choice.

Once an honest equivalence exists, use standard number-field unit theory to
show that the kernel of the CM relative norm on units is finite/torsion
(root-of-unity). Do not assert this for the concrete carrier without a checked
transport.

### Preferred route B — direct concrete classification

If substantially shorter, classify only those concrete units satisfying
`quadraticNormUnit delta = 1`.
A full classification of all degree-six units is not required.

The expected mathematical shape is that relative-norm-one units are roots of
unity in the seventh cyclotomic field.

## Scalar-congruence phase kill

If relative-norm-one units are reduced to roots of unity, do not stop there.
Use the already proved congruence modulo `(7)` to eliminate nontrivial zeta
phase.

The target shape is:

```text
relative norm one
  -> delta is a root of unity (conceptually ± zeta^j)
delta ≡ rational scalar (mod 7)
  -> zeta phase j = 0
  -> delta = ±1
  -> delta is a seventh power
```

Remember that `(-1)^7 = -1`, so both signs are harmless.

Do not infer `j = 0` merely from reduction modulo `ramifiedPrime`; all
zeta phases reduce to 1 there.  The argument must use the stronger congruence
modulo the full principal ideal `(7) = (1-zeta)^6 * unit`, or an equivalent
checked coordinate statement.

## Consequences if the narrow lemma closes

From the actual R12 packet prove, in order:

```text
unit = unitRoot^7
Q₁ = gamma^7
directLinearFactor = ramifiedUniformizer * gamma^7
```

where any reassociation of seventh-power factors is explicit.

Then perform a bounded audit: determine whether this exact direct linear-factor
equation already feeds an existing no-sorry descent/contradiction theorem
without passing through the old TraceOne receiver. Do not import a theorem whose
conclusion is already FLT7 by a circular specialized dependency.

## Required report questions

Create `report-018.md` and answer:

1. Was the norm-one phase packet constructed from the actual R12 unit?
2. Was its relative norm proved exactly one?
3. Was rational-scalar congruence modulo `(7)` preserved?
4. Was the concrete ring-of-integers map upgraded to an equivalence? If not,
   what exact theorem blocks it?
5. Was the relative norm-one unit group classified as torsion/roots of unity?
6. Was the nontrivial zeta phase killed by the full mod-seven congruence?
7. Was `RelativeNormOneKummerUnitLemmaAtSeven` proved?
8. Was the original R12 unit proved a seventh power?
9. Were `Q₁ = gamma^7` and
   `directLinearFactor = ramifiedUniformizer * gamma^7` proved?
10. Does an existing clean downstream theorem now give a contradiction, or
    what exact frontier remains?

## Outcome labels

- **Outcome A — RELATIVE NORM-ONE PHASE KILLED; DIRECT CHOSEN QUOTIENT IS AN EXACT SEVENTH POWER.**
- **Outcome B — NORM-ONE REDUCTION GREEN; ROOT-OF-UNITY CLASSIFICATION GREEN; FULL MOD-SEVEN PHASE KILL REMAINS.**
- **Outcome C — NORM-ONE REDUCTION GREEN; CONCRETE/ABSTRACT UNIT-THEORY TRANSPORT IS THE PRECISE FRONTIER.**
- **Outcome D — AN EARLIER UNIT-NORM OR CONGRUENCE BRIDGE IS MISSING.**

## Validation

At minimum:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicRelativeNormPhase
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicRelativeNormPhaseApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectCyclotomicRelativeNormPhaseAxiom
git diff --check
```

Run forbidden-source scans for new production/audit files and print axioms for
all decisive new theorems. No `sorry`, `sorryAx`, `admit`, `unsafe`, or
project `axiom` is allowed.

Keep the public `DkMath.FLT.Seven` facade unchanged unless the full unit lemma
and its exact-power consequences become stable, non-speculative API.
