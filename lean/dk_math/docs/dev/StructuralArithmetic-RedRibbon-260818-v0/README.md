# Structural Arithmetic / Red Ribbon integration

Date: 2026-08-20
Status: **Phases A-I implemented, build-checked locally, and closeout-audited**
Branch: `wip/structural-arithmetic-red-ribbon-260818-v0`
Base: `develop`

## 1. Purpose

This document records the integration point between ideas that had previously
been developed separately in DkMath:

- KUS structural preservation `(K, U, S_U)`;
- the red-ribbon interpretation of a chosen unit/base label;
- prime-factor / valuation coordinates;
- DHNT-style dynamic exponent scaling;
- congruence and quotient observations;
- the generic Cosmic Formula `GN` family;
- the exponent-five / golden-unit modulo-fifth-power reduction;
- finite-prime escape and primitive-scale directions.

The integration does not rename or refactor those mature modules. Its purpose
is to provide a small public StructuralArithmetic layer that keeps several
operations distinct while proving the bridges that are actually justified.

The main operations are:

1. **radial scale** — multiply a fixed real coordinate vector by a scalar;
2. **rebase / transport** — change typed unit/support/blueprint information;
3. **project / quotient** — intentionally forget periodic exponent information;
4. **escape / new direction** — exhibit a prime direction absent from a known
   finite prime-scale world.

KUS remains the preservation/transport layer. StructuralArithmetic sits beside
and above it as an observation, projection, multiplicative-direction, and
scaling vocabulary.

## 2. Terminology fixed here

### 2.1 Multiplicative identity

`1` remains the ordinary algebraic multiplicative identity:

```text
x * 1 = 1 * x = x
```

A congruence period such as `5` is not a ring/monoid identity.

### 2.2 Gauge period

For natural exponent data, `d` is a **gauge period** when exponents differing
by a multiple of `d` have the same projected observation:

```text
n ~_d n + d*k
projectExponent d n = n % d
```

### 2.3 Raw and projected prime structure

A raw multiplicative coordinate structure is abstractly

```text
v : ι -> Nat
```

and for ordinary naturals the prime specialization is

```text
p |-> v_p(n).
```

A period-`d` observation is

```text
p |-> v_p(n) % d.
```

The raw source is retained independently of the lossy projection.

### 2.4 Boundary periods

Lean natural remainder arithmetic gives:

```text
n % 0 = n
n % 1 = 0
```

Therefore:

- period `0` is the identity / unprojected view;
- period `1` is total exponent-coordinate collapse.

The ordinary raw prime world is therefore not modeled as `mod 1`.

The `d` argument of `DkMath.CosmicFormula.GN` remains the polynomial degree,
not a StructuralArithmetic gauge period.

## 3. PowerGauge Red Ribbon kernel

`PowerGauge` proves the elementary Red Ribbon contract:

```text
projectExponent d (n + d*k) = projectExponent d n
```

and coordinatewise:

```text
projectCoordinates d (fun i => v i + d * k i)
  = projectCoordinates d v.
```

Interpretation:

- `v` is retained raw structure;
- `d*k` is whole-period motion;
- the projected observer does not see that motion.

### 3.1 Canonical inter-period forgetting

`InterPeriod` formalizes the canonical map from period `d` to period `m` when
`m ∣ d`:

```text
projectExponent m (projectExponent d n) = projectExponent m n
projectCoordinates m (projectCoordinates d v) = projectCoordinates m v
```

The relation-level and prime-coordinate forms are public as well. This is
one-way information loss; no reconstruction from a coarser observation is
claimed.

### 3.2 Explicit KUS observation

`KUSObservation` keeps a `GKUS` source, interprets its retained support through
an explicit `ObservationSpec`, and then applies the existing projection kernel.

`ObservationCompatible` is a separate semantic hypothesis. Arbitrary
`DkMath.KUS.ScaleSpec` transports are not declared observation-preserving.
Under compatibility, raw and projected observations commute with the KUS
transport.

The concrete `cosmicUnitObservation` reads the retained dimension of the
existing `DkMath.KUS.CosmicBridge.cosmicTerm`, giving a genuine nonconstant
KUS witness.

## 4. Golden fifth-power Red Ribbon bridge

`GoldenUnitBridge` now connects the already-certified FLT5 golden-unit
classification to StructuralArithmetic without changing the FLT5 proof route.

The relation-valued observer is:

```text
GoldenFifthSector i x
  := exists delta, x = phi^i * delta^5.
```

Every golden unit obtains such a sector witness from the existing
`goldenUnitFifthClass_of_unit` theorem. The new load-bearing Red Ribbon law is:

```text
GoldenFifthSector i x
  -> GoldenFifthSector i (x * eta^5).
```

Thus complete fifth-power multiplication changes only the hidden witness and
preserves the visible representative. No canonical sector selector or sector
uniqueness theorem is introduced.

This construction remains distinct from:

- natural prime-exponent reduction modulo `5`;
- ordinary additive congruence modulo `5`;
- Cosmic Formula degree `5`.

The common principle is only that a corresponding complete fifth-power gauge
motion is invisible to its chosen observer.

## 5. Prime directions and finite escape

`PrimeCoordinates` supplies the raw valuation coordinates and proves:

```text
v_p(n * a^d) = v_p(n) + d * v_p(a),
```

hence multiplication by a `d`-th power is invisible after period-`d`
projection.

`PrimitiveDirection` introduces a deliberately separate primitive notion:

```text
KnownPrimeScales S
PrimeScaleGeneratedBy S n
FreshPrimeDirection S n q
```

This does not rename the existing Erdos-style `PrimitiveOn` or the
Zsigmondy-style `PrimitivePrimeFactorOfDiffPow`.

The intended semantic reading of `S` as a prime-scale basis is certified by
`KnownPrimeScales S`. The core generated-world predicate itself is kept small:
a nonzero natural is generated when every prime divisor belongs to `S`.

`FinitePrimeEscapeBridge` reuses the existing Hackathon `FreshPrimeFactor`
provider instead of reproving Euclid-style escape. In particular, the existing
`{2,3,5}` example proves that the generic degree-five GN target lies outside
the old prime-scale world.

## 6. Generic GN and FLT5 GN5

`GNBridge` connects an existing `PrimitiveBeam` primitive-prime witness to a
`FreshPrimeDirection` of the generic GN target, provided the prime is explicitly
absent from the finite scale set.

It also proves the exact specialization identity:

```text
DkMath.FLT.Five.GN5 g y = DkMath.CosmicFormulaBinom.GN 5 g y.
```

The Phase-E `{2,3,5}` escape is then transported by equality to the explicit
FLT5 `GN5 1 1` target. No new computation of the concrete value is used in the
bridge.

## 7. DHNT radial scaling and rebase distinction

`RadialScaling` formalizes fixed-index real coordinate scaling:

```text
radialScaleCoordinates k v i = k * v i.
```

It proves identity, zero, composition, and—most importantly—for `k ≠ 0`:

```text
radialScaleCoordinates k v i = 0 <-> v i = 0
Function.support (radialScaleCoordinates k v) = Function.support v.
```

Therefore a nonzero radial scale changes magnitudes but cannot erase an
existing coordinate direction.

The existing natural valuation vector is reused through:

```text
realPrimeExponentCoordinates n
radialScalePrimeCoordinates k n.
```

These are real-valued images of integer valuation coordinates; they are not a
prime factorization theory for arbitrary real numbers.

This operation is intentionally different from KUS `ScaleSpec`:

```text
Radial scaling:
  fixed index type
  v -> k*v
  nonzero k preserves the zero-pattern

KUS ScaleSpec:
  typed unit / blueprint transport
  may change support interpretation
  needs explicit ObservationCompatible to preserve a chosen observation
```

Changing from the support of `30 = 2*3*5` to the support of `6 = 2*3` is thus a
rebase/support change, not a nonzero radial scale of the same coordinate
vector.

## 8. Cosmic-square analytic dynamic scaling

`CosmicSquareScaling` provides one bounded analytic realization of the radial
scalar idea:

```text
F(y) = sqrt(1 + y) - 1
kappa(y) = log(F(y)) / log(y).
```

For `0 < y` and `y ≠ 1`, it proves the exact local reconstruction:

```text
Real.rpow y (kappa(y)) = F(y).
```

The reusable `rpow_log_ratio` theorem isolates the positive-real analytic
identity from the Cosmic-square specialization.

The dynamic scalar is then fed directly to Phase-H coordinates:

```text
dynamicPrimeCoordinates y n
  = radialScalePrimeCoordinates (kappa(y)) n.
```

When `kappa(y) ≠ 0`, the prime-coordinate zero-pattern and `Function.support`
are preserved.

Two exact boundaries/examples are certified:

```text
y = 3  : F(3) = 1, kappa(3) = 0
          -> radial collapse boundary

y = 30 : 30 ^ kappa(30) = sqrt(31) - 1
          and kappa(30) ≠ 0
          -> prime-coordinate support preserved
```

The second statement is an analytic reconstruction plus a scaled coordinate
image. It does **not** assert that `sqrt(31) - 1` has an ordinary real prime
factorization or that the dynamic map is multiplicative.

## 9. Implementation phases

- **Phase A — PowerGauge:** completed and build-checked.
- **Phase B — PrimeCoordinates:** completed and build-checked.
- **Phase C — InterPeriod:** completed and build-checked.
- **Phase D — KUSObservation:** completed and build-checked.
- **Phase E — PrimitiveDirection / FinitePrimeEscapeBridge:** completed and
  build-checked.
- **Phase F — GNBridge:** completed and build-checked.
- **Phase G — GoldenUnitBridge:** completed and build-checked.
- **Phase H — RadialScaling:** completed and build-checked.
- **Phase I — CosmicSquareScaling:** completed and build-checked.

All of these modules are public through
`DkMath.NumberTheory.StructuralArithmetic`.

## 10. Explicit non-goals and semantic boundaries

This integration does not claim:

- a new axiom or replacement foundation;
- replacement of KUS;
- a broad namespace/refactor of mature FLT5, KUS, or DHNT code;
- ordinary prime factorization for arbitrary nonzero reals;
- ring-theoretic “real primes” `2^k`, `3^k`, ...;
- a global multiplicative homomorphism for the dynamic square map;
- equality of Cosmic Formula degree, additive modulus, and PowerGauge period;
- equality of golden fifth-power classes and natural valuation mod-5 classes;
- canonical golden-sector uniqueness;
- reconstruction of raw exponent coordinates from a coarser period;
- automatic observation preservation for arbitrary KUS `ScaleSpec` values.

## 11. Completed structural checkpoint

The A-I integration establishes the following public picture:

```text
retained raw source / coordinates
        |
        +-- project d ----------------> lossy period-d observation
        |                                 |
        |                                 `-- coarsen to m when m | d
        |
        +-- KUS transport ------------> typed support transport
        |                                 only observation-preserving
        |                                 under explicit compatibility
        |
        +-- fresh prime direction ----> escape from finite prime-scale world
        |                                 |
        |                                 `-- generic GN / FLT5 GN5 bridge
        |
        +-- golden fifth-power class -> visible phi^i sector
        |                                 invariant under * eta^5
        |
        `-- real radial scaling ------> k * valuation coordinates
                                          |
                                          `-- Cosmic-square dynamic kappa(y)
                                              with exact rpow reconstruction
```

The integration is therefore closed at Phase I. Further work should begin from
a new, separately justified mathematical question rather than automatically
opening a Phase J abstraction layer.
