# FLT7TC-005R12 — Direct chosen-quotient unit congruence and p=7 Kummer-unit frontier

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This checkpoint starts from the **current counterexample provenance** and the
R11 direct ideal theorem.  It must not route through
`RamifiedSignedRootRoutingPacket`, must not assume
`CubicGapSeventhShapeReceiver`, and must not use any theorem whose axiom audit
contains `sorryAx`.

The purpose is to move one layer beyond

```text
∃ I, span {directLinearFactor r} = ramifiedPrime * I^7
```

and determine exactly how much of the associated-unit obstruction can now be
removed.

The key chosen quotient is

```text
Q₁ := directCyclotomicPhaseQuotient r 1
```

with the already checked properties

```text
span {Q₁} = I^7                  for some I
Q₁ = endpointRight + directRamifiedGapTail
Q₁ ∉ ramifiedPrime
```

and

```text
directLinearFactor r = ramifiedUniformizer * Q₁.
```

## 1. Construct an honest element-level chosen-quotient packet

Use only the R11 theorem

```text
directCyclotomicChosenQuotient_ideal_is_seventh_power
```

and the clean concrete PID theorem

```text
SevenCyclotomicDegreeSixInt.unitMulPowOfSpanEqPow
```

to construct the smallest useful packet, conceptually:

```lean
structure DirectCyclotomicChosenQuotientPowerPacket
    {x y z : ℕ} (source : CounterexamplePack x y z)
    (r : PrimitiveCounterexampleRamifiedProvenance source) where
  idealRoot : Ideal SevenCyclotomicDegreeSixInt.Ring
  beta : SevenCyclotomicDegreeSixInt.Ring
  unit : SevenCyclotomicDegreeSixInt.Ring
  unit_isUnit : IsUnit unit
  span_beta : Ideal.span {beta} = idealRoot
  quotient_eq :
    directCyclotomicPhaseQuotient r 1 = unit * beta ^ 7
```

The exact fields may be smaller if some are redundant, but the packet must
retain the **same** `r` and the exact element equation.  Do not silently treat
`unit` as a seventh power.

Also expose the resulting direct factor equation

```text
directLinearFactor r
  = ramifiedUniformizer * unit * beta^7
```

up to the harmless reassociation/commutation appropriate for the commutative
carrier.

## 2. Prove the chosen quotient is a rational scalar modulo seven

Let

```text
sevenIdeal := Ideal.span {(7 : SevenCyclotomicDegreeSixInt.Ring)}.
```

Prove, from the explicit R10/R11 formula and total ramification, the honest
congruence

```text
Q₁ - ofReal(endpointRight) ∈ sevenIdeal.
```

The existing tail contains `ramifiedUniformizer^35`; use

```text
ofReal_seven_eq_uniformizer_pow_six_mul_unit
```

and the fact that `ramifiedSevenUnit` is a unit.  Do not replace congruence
modulo `(7)` by congruence modulo `ramifiedPrime`.

Prefer a reusable theorem saying that the R11 tail is in `(7)`.

## 3. Degree-six Frobenius/scalarization modulo seven

Prove the concrete p=7 statement that for every

```text
a : SevenCyclotomicDegreeSixInt.Ring
```

its seventh power is congruent modulo `(7)` to a rational scalar.
A suitable theorem shape is, conceptually,

```lean
∃ n : ℤ,
  a ^ 7 - (n : SevenCyclotomicDegreeSixInt.Ring) ∈ sevenIdeal
```

with a stronger canonical choice allowed, for example the representative of
`ramifiedEval a : ZMod 7`.

Preferred proof routes:

1. quotient by `(7)` and use characteristic-seven Frobenius together with the
   already checked `adjoin_zeta_eq_top` and `zeta^7 = 1`; or
2. an explicit coordinate proof in the concrete six-coordinate carrier.

Do **not** assume that the quotient modulo `(7)` is reduced.  The nilpotent
ramified direction is real; the theorem is about the seventh power killing the
non-scalar nilpotent coordinates.

For the `beta` in the packet, also prove that the resulting scalar is nonzero
modulo seven.  Use `Q₁ ∉ ramifiedPrime` and `unit_isUnit`; do not infer this
from the integer norm alone.

## 4. Isolate the associated unit as a rational scalar modulo seven

Combine §§2–3 with

```text
Q₁ = unit * beta^7
```

to prove that the concrete associated unit is congruent modulo `(7)` to a
rational integer not divisible by seven.

A suitable public/internal boundary predicate is, conceptually,

```lean
def DegreeSixUnitCongruentToRationalModSeven
    (u : SevenCyclotomicDegreeSixInt.Ring) : Prop :=
  ∃ m : ℤ,
    ¬ (7 : ℤ) ∣ m ∧
    u - (m : SevenCyclotomicDegreeSixInt.Ring) ∈ sevenIdeal
```

and the packet's `unit` should satisfy it.

This is the exact p=7 Kummer-unit input.  Do not replace it by mere equality
under `ramifiedEval`.

## 5. Real-cubic norm audit: kill the free real unit class if possible

Independently of whether the full Kummer unit lemma is available, take the
quadratic norm of the chosen-quotient equation.

First define/check the current-provenance real source obtained after removing
the one forced ramified axis.  Algebraically, with

```text
L := r.summit.endpointLeft
R := r.summit.endpointRight
A := r.summit.gapRoot
```

and using

```text
L - R = 7^6 * A^7
7 = eisensteinAxis^3 * thetaSevenUnit
```

the direct relative norm satisfies

```text
directRelativeNorm L R
  = eisensteinAxis *
      (eisensteinAxis^35 * thetaSevenUnit^12 * A^14 - L*R).
```

Since

```text
QuadraticAlgebra.norm ramifiedUniformizer = -eisensteinAxis,
```

the quadratic norm of `Q₁` should therefore be the sign-adjusted core

```text
L*R - eisensteinAxis^35 * thetaSevenUnit^12 * A^14.
```

Kernel-check the exact sign/orientation rather than relying on this comment.

From

```text
Q₁ = unit * beta^7
```

obtain

```text
realSource = realUnit * realRoot^7
```

where `realUnit` is the quadratic norm of the degree-six `unit` and is packaged
honestly as a `SevenRealCubicIntˣ`.

The explicit `realSource` is a nonzero rational scalar modulo seven because
both stored endpoints are seven-units and the high Eisenstein-axis term
vanishes modulo seven.  Generalize/reuse the local-coordinate argument in

```text
SevenRealCubicInt.projectiveLog_eq_zero_of_linearSource_eq_unit_mul_pow_seven
```

rather than forcing the source into the old `linearSource a b` API when its
coefficient hypotheses do not match.

Target:

```text
projectiveLog realUnit = 0
```

and therefore, using

```text
unit_isSeventhPower_iff_projectiveLog_eq_zero,
```

prove that the **relative quadratic norm of the associated degree-six unit is
a seventh power in the real-cubic unit group**.

This does not yet prove that the degree-six unit itself is a seventh power.
It should be recorded explicitly as removal of the free real unit class,
leaving only the kernel of relative norm modulo seventh powers.

## 6. Bounded p=7 Kummer-unit lemma audit

Now audit the stronger concrete statement

```lean
/-- Conceptual target only. -/
def DegreeSixKummerUnitLemmaAtSeven : Prop :=
  ∀ u : SevenCyclotomicDegreeSixInt.Ringˣ,
    DegreeSixUnitCongruentToRationalModSeven (u : _)
      → ∃ v : SevenCyclotomicDegreeSixInt.Ringˣ, u = v ^ 7
```

The classical motivation is the regular-prime Kummer unit lemma, but this
checkpoint must derive any result from checked DkMath/Mathlib infrastructure,
not from historical authority.

Useful existing assets to inspect include:

```text
SevenCyclotomicDegreeSixInt.ringOfIntegersToRing
SevenCyclotomicDegreeSixInt.ringOfIntegersToRing_surjective
SevenCyclotomicDegreeSixInt.rankOverIntegers_eq_six
SevenRealCubicInt.projectiveLog
SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero
```

A potentially honest route is to upgrade `ringOfIntegersToRing` to an
isomorphism by proving that `1,zeta,...,zeta^5` form a `ℤ`-basis of the
concrete rank-six carrier, and then transport the required unit theory.  Do
not assume injectivity merely from surjectivity.

Another acceptable route is a direct concrete proof that the residual
relative-norm-kernel class is exactly the `mu_7` phase and that congruence
modulo `(7)` kills that phase.

Hard stops:

- do not assert that every degree-six unit is a seventh power;
- do not infer the Kummer unit lemma from PID/class number one alone;
- do not replace congruence modulo `(7)` by congruence modulo
  `ramifiedPrime`;
- do not identify relative norm-one units with roots of unity without a
  checked theorem;
- do not use legacy/default Kummer theorems carrying `sorryAx`;
- do not import a theorem already equivalent to unconditional FLT7.

## 7. If the full unit lemma closes, absorb the unit

Only if §6 is actually kernel-checked, apply it to the packet's unit and expose

```text
∃ gamma : SevenCyclotomicDegreeSixInt.Ring,
  directCyclotomicPhaseQuotient r 1 = gamma ^ 7
```

and hence

```text
directLinearFactor r = ramifiedUniformizer * gamma ^ 7.
```

Do not claim a contradiction unless an already checked noncircular theorem
consumes exactly this current-provenance equation.

## 8. Files / reports

Preferred new module name:

```text
DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicUnitCongruence.lean
```

Add focused API and axiom audits.  Update `report-017.md` and `ROADMAP.md`.
Keep speculative APIs out of the public `DkMath.FLT.Seven` facade unless a
stable theorem surface is genuinely established.

The report must answer separately:

1. Is `Q₁ = unit * beta^7` checked from the current R11 ideal packet?
2. Is `Q₁ ≡ endpointRight (mod 7)` checked?
3. Is seventh-power scalarization modulo `(7)` checked for arbitrary elements?
4. Is the actual associated unit congruent to a nonzero rational integer
   modulo `(7)`?
5. Is the relative real-cubic unit class proved to be a seventh power?
6. Is the remaining degree-six class reduced to a pure `mu_7` / relative
   norm-kernel phase?
7. Is the full p=7 Kummer unit lemma actually proved?
8. If yes, is `Q₁` an exact seventh power and is
   `directLinearFactor = ramifiedUniformizer * gamma^7` checked?
9. What exact first theorem remains if any step fails?
10. What do the decisive `#print axioms` outputs contain?

## 9. Required validation

At minimum:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicUnitCongruence
lake build DkMath.FLT.Seven
```

plus focused API/axiom audits, `git diff --check`, and scans of new production
sources for `sorry`, `admit`, `unsafe`, project `axiom`, and accidental use of
quarantined `sorryAx` surfaces.

## 10. Outcome labels

Use the strongest honest outcome only.

### Outcome A

**DIRECT UNIT CONGRUENCE AND CONCRETE p=7 KUMMER UNIT LEMMA GREEN; CHOSEN
QUOTIENT IS AN EXACT SEVENTH POWER.**

Required:

```text
Q₁ = gamma^7
directLinearFactor = ramifiedUniformizer * gamma^7
```

from current provenance, with clean axiom audit.

### Outcome B

**ELEMENT PACKET / MOD-SEVEN RATIONAL CONGRUENCE GREEN; REAL FREE UNIT CLASS
KILLED; PURE MU_7 / RELATIVE-NORM-KERNEL PHASE REMAINS.**

This is a strong successful result.  State the exact remaining phase theorem.

### Outcome C

**ELEMENT PACKET AND MOD-SEVEN RATIONAL CONGRUENCE GREEN; FULL KUMMER UNIT
LEMMA BLOCKED ON A CONCRETE UNIT-THEORY BRIDGE.**

Name the first missing bridge, e.g. concrete-ring/ring-of-integers equivalence
or a checked relative norm-one unit classification.

### Outcome D

**ELEMENT PACKET GREEN, BUT MOD-SEVEN SCALARIZATION / RATIONAL UNIT CONGRUENCE
HAS A PRECISE EARLIER INFRASTRUCTURE GAP.**

Do not hide the gap behind a broad `unit normalization` label.

No outcome in this checkpoint by itself licenses a claim of unconditional
FLT7 unless an actual kernel-checked contradiction theorem is additionally
constructed from the current provenance.
