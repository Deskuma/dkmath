# Structural Arithmetic / Red Ribbon integration

Date: 2026-08-20
Status: Phases A-E implemented and build-checked locally
Branch: `wip/structural-arithmetic-red-ribbon-260818-v0`
Base: `develop`

## 1. Purpose

This document records the integration point between ideas that have previously
been developed separately in DkMath:

- KUS structural preservation `(K, U, S_U)`;
- the red-ribbon interpretation of a chosen unit/base label;
- prime-factor / valuation coordinates;
- DHNT-style dynamic exponent scaling;
- congruence and quotient observations;
- the generic Cosmic Formula `GN` family;
- the exponent-five / golden-unit modulo-fifth-power reduction;
- finite-prime escape and primitive-scale directions.

The immediate goal is not to rename or refactor those mature modules.  The goal
is to introduce a small mathematically standard kernel that distinguishes
three operations which have often been discussed together:

1. **scale** — change magnitude while preserving structural direction;
2. **rebase / transport** — change the unit/support used to encode a structure;
3. **project / quotient** — intentionally forget periodic information.

KUS is the existing DkMath layer whose job is to preserve support and blueprint
information while values are changed or transported.  The new structural
arithmetic layer should therefore sit beside / above KUS rather than replace it.

## 2. Terminology fixed here

### 2.1 Multiplicative identity

`1` remains the ordinary algebraic multiplicative identity.  It is the
**basepoint label** of a multiplicative structure:

```text
x * 1 = 1 * x = x
```

Do not call a congruence period such as `5` the ring/monoid identity.

### 2.2 Gauge period

For exponent data, a natural `d` is a **gauge period** when exponents differing
by a multiple of `d` are observed as the same sector:

```text
n ~_d n + d*k
```

The observable coordinate is

```text
projectExponent d n = n % d
```

This is the precise congruence form of the red-ribbon idea that one full period
returns to the same visible position.

### 2.3 Raw structure and projected structure

A raw multiplicative coordinate structure is represented abstractly as

```text
v : ι -> Nat
```

For prime coordinates, the implemented specialization is

```text
v p = v_p(n)
```

where `v_p` is the prime valuation of `n`.

The projected structure is

```text
p |-> v p % d
```

and the raw structure must remain available when information-preserving
transport is required.

### 2.4 The two boundary periods

There is an important asymmetry which must be fixed before using names such as
`GN1` for a structural world.

In Lean's natural remainder arithmetic:

```text
n % 0 = n
n % 1 = 0
```

Therefore:

- period `0` gives the identity / unprojected view;
- period `1` collapses every exponent coordinate to one visible sector.

Consequently, the ordinary natural prime world must **not** be modeled as the
quotient `mod 1`.  The ordinary world is the raw structure (or equivalently the
period-zero identity view in this minimal coordinate API).

This also prevents a naming collision with the already existing
`DkMath.CosmicFormula.GN`, where the argument `d` is the degree of the Cosmic
Formula polynomial rather than the index of a quotient world.

For now the new layer uses the neutral term **PowerGauge** / **Structural
Projection** rather than introducing a second incompatible `GNn` notation.

## 3. Red Ribbon theorem

The first formal contract is deliberately elementary:

```text
projectExponent d (n + d*k) = projectExponent d n
```

and coordinatewise:

```text
projectCoordinates d (fun i => v i + d * k i)
  = projectCoordinates d v
```

Interpretation:

- `v` is the retained structure;
- `d*k` is motion in the invisible period direction;
- the quotient observer sees no change.

This is the first formal red-ribbon law.

### 3.1 Canonical inter-period forgetting

`DkMath.NumberTheory.StructuralArithmetic.InterPeriod` formalizes the direct
map from a period-`d` observation to a period-`m` observation when `m ∣ d`:

```text
projectExponent m (projectExponent d n) = projectExponent m n
projectCoordinates m (projectCoordinates d v) = projectCoordinates m v
```

The public theorems are `projectExponent_project_of_dvd`,
`projectCoordinates_project_of_dvd`, `SamePowerSector.of_dvd`, and
`SamePowerStructure.of_dvd`. The prime-coordinate specializations are
`projectPrimeCoordinates_coarsen_of_dvd` and
`projectPrimeCoordinates_eq_of_dvd`.

This map is deliberately one-way: it forgets additional periodic information
but does not reconstruct the raw exponent source. The theorem includes both
boundary periods. If `m = 0`, the hypothesis `m ∣ d` forces `d = 0`; if `m = 1`,
the target observation is the already established total collapse.

### 3.2 Explicit KUS observation

`DkMath.NumberTheory.StructuralArithmetic.KUSObservation` retains a typed KUS
source through `extract_g`, interprets it with an explicit `ObservationSpec`,
and applies the existing `projectCoordinates` kernel through `observePeriod`.
The public laws are `observePeriod_period_zero`,
`observePeriod_period_one`, `observePeriod_eq_project`, and
`observePeriod_project_of_dvd`.

Transport is not assumed to preserve meaning. `ObservationCompatible` is an
explicit support-level proposition; only under it do
`rawObservation_scaleGKUS_of_compatible` and
`observePeriod_scaleGKUS_of_compatible` prove transport compatibility.
The concrete `cosmicUnitObservation` reads the retained dimension of the
existing `DkMath.KUS.CosmicBridge.cosmicTerm`, and
`observePeriod_cosmicTerm` shows the resulting nontrivial `d % p` projection.

## 4. Connection to fifth-power unit classification

The exponent-five golden-unit classification used in FLT5 has the same shape:

```text
epsilon = phi^r * delta^5
```

with the fifth-power factor absorbed into the invisible/gauge part and only the
sector `r mod 5` remaining visible.

The present implementation does **not** yet refactor the FLT5 golden-unit files.
A later bridge should state explicitly that the existing modulo-fifth-power
classification is an instance of the same period-five projection principle.

## 5. Connection to prime coordinates

For a positive natural

```text
n = product p^(v_p(n))
```

the prime-exponent map is the canonical raw multiplicative structure.
`DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates` defines the
period-`d` observation

```text
p |-> v_p(n) % d
```

and proves the expected power-gauge invariance

```text
project_d (n * a^d) = project_d n
```

as `projectPrimeCoordinates_mul_pow`, under nonzero hypotheses on `n` and `a`.
Its relation form is `samePowerStructure_primeCoordinates_mul_pow`.

The prime directions themselves belong to the **raw** world: a prime `p`
introduces one basis direction in the valuation coordinate system.  The
projection layer may hide repeated multiples of that direction but does not
create the primitive direction.

## 6. Connection to DHNT dynamic scaling

For a fixed positive real scale exponent `k`, the familiar identity

```text
(product p^(a_p))^k = product p^(k*a_p)
```

is a radial scaling of the exponent vector.  In the numerical example

```text
30 = 2 * 3 * 5
x = sqrt(31) - 1
k = log(x) / log(30)
x = 2^k * 3^k * 5^k
```

the support / exponent direction `(1,1,1)` is retained and scaled to
`(k,k,k)`.

Changing the base from `30` to `6` and solving a new exponent is a different
operation because the support changes from `{2,3,5}` to `{2,3}`.  That is a
**rebase**, not the same structure-preserving scale operation.

A later DHNT bridge should make this distinction explicit in types/theorem
names.

## 7. Connection to KUS

KUS already provides the preservation layer:

```text
GKUS C U Blueprint
  coeff
  unit
  blueprint
```

and `ScaleSpec` transports unit/blueprint data while preserving the visible
coefficient.  KUS therefore remains the canonical DkMath machinery for
remembering support/blueprint information across value-changing operations.

The structural-arithmetic projection layer must not discard the KUS source when
an inverse comparison or a projection into another period is required.

The intended architecture is:

```text
raw structural source / KUS support
            |
            +---- scale / transport ----> raw structural source
            |
            `---- project d ------------> observable period-d view
```

Different projected worlds should normally be compared through their retained
raw source.  A direct map from period `n` to period `m` is canonical only when
the relevant congruence map is canonical (for example when `m | n`).

## 8. Implementation phases

### Phase A — minimal power-gauge kernel (completed and build-checked)

Target module:

```text
DkMath.NumberTheory.StructuralArithmetic.PowerGauge
```

Contracts:

- `projectExponent`;
- `SamePowerSector`;
- identity behavior at period `0`;
- total collapse at period `1`;
- red-ribbon invariance under `+ d*k`;
- coordinatewise projection;
- coordinatewise power-sector equivalence.

### Phase B — prime valuation bridge (completed and build-checked)

`DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates` implements the raw
valuation coordinates and proves:

```text
v_p(n * a^d) = v_p(n) + d * v_p(a)
```

under the needed nonzero/prime hypotheses, then projects modulo `d` via
`projectPrimeCoordinates_mul_pow`.

### Phase C — inter-period projection (completed and build-checked)

`DkMath.NumberTheory.StructuralArithmetic.InterPeriod` proves canonical
forgetting from period `d` to period `m` under `m ∣ d`, first for one exponent,
then arbitrary coordinates, equivalence relations, and prime coordinates.

### Phase D — KUS observation bridge (completed and build-checked)

`KUSObservation` retains the raw `GKUS` support, derives coordinates through an
explicit observer, reuses `projectCoordinates` and `InterPeriod`, and expresses
`ScaleSpec` compatibility as an explicit hypothesis. The existing cosmic-term
support provides a concrete nonconstant witness.

### Phase E — primitive direction layer (completed and build-checked)

`PrimitiveDirection` defines `KnownPrimeScales`,
`PrimeScaleGeneratedBy`, and `FreshPrimeDirection` without reusing the existing
Erdos `PrimitiveSet` or Zsigmondy `PrimitiveBeam` meanings.
`FinitePrimeEscapeBridge` reuses the existing Hackathon provider and proves
`GN5_escape_not_primeScaleGeneratedBy_two_three_five`.

### Phase F — Cosmic Formula / GN bridge (completed and build-checked)

`GNBridge` transports an existing `PrimitiveBeam` primitive prime factor to a
`FreshPrimeDirection` and non-generation theorem for generic GN, with the
explicit hypothesis that the witness is outside the supplied finite scale set.
It also proves the exact identity
`FLT.Five.GN5 g y = CosmicFormulaBinom.GN 5 g y` and rewrites the existing
`{2, 3, 5}` finite escape to the specialized `GN5 1 1` target.  Degree `5`,
additive congruence modulo `5`, and PowerGauge period `5` remain separate.

### Phase G — golden-unit bridge (completed and build-checked)

`GoldenUnitBridge` introduces the relation-valued `GoldenFifthSector` observer,
reuses the certified golden-unit classification, and proves that multiplying
by a complete fifth power preserves a fixed visible sector.  It also exposes
the existing stripped FLT5 packet theorem through this relation.  No canonical
sector selector or uniqueness theorem is claimed.  Golden fifth-power
classes, natural prime-exponent period five, and additive congruence modulo
five remain separate constructions.

## 9. Non-goals for the first implementation

- no new axiom;
- no replacement of KUS;
- no broad namespace move;
- no claim that nonzero reals have ordinary prime factorization;
- no definition of `2^k`, `3^k`, ... as ring-theoretic real primes;
- no direct identification of `mod 1` with the natural prime world;
- no modification of the completed FLT5 proof tower before the bridge API is
  stable.

## 10. Completed structural checkpoint

The current public modules make the following distinctions theorem-level rather
than prose-level:

```text
period 0 : structure preserved exactly
period 1 : projected structure completely collapsed
period d : adding d-period gauge motion is observationally invisible
period m : a period-d observation forgets canonically to m when m divides d
```

The kernel, prime-coordinate bridge, KUS observation bridge, primitive
finite-escape bridge, generic GN/GN5 bridge, and golden-unit bridge are now
public through `DkMath.NumberTheory.StructuralArithmetic`. The next bounded
gap is determined by the remaining A--G integration state; the raw
prime-direction and golden-unit observers remain distinct from period
projection and from arbitrary KUS observations.
