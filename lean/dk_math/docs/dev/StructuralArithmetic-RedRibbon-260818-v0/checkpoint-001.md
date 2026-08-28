# Structural Arithmetic / Red Ribbon — checkpoint 001

Date: 2026-08-18
Branch: `wip/structural-arithmetic-red-ribbon-260818-v0`
Base: `develop`

## Implemented

### A. Power-gauge kernel

Module:

```text
DkMath.NumberTheory.StructuralArithmetic.PowerGauge
```

Implemented declarations include:

```text
projectExponent
SamePowerSector
projectCoordinates
SamePowerStructure
```

Theorem-level boundary behavior is fixed:

```text
period 0 : n % 0 = n       -- raw / unprojected identity view
period 1 : n % 1 = 0       -- total sector collapse
period d : n + d*k ~_d n   -- red-ribbon period invariance
```

The coordinatewise theorem records that adding a whole `d`-period in every
structural direction is invisible after projection.

### B. Prime-coordinate bridge

Module:

```text
DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
```

The prime index type is the subtype of natural primes.  The raw structure is
represented by the full p-adic valuation coordinate function:

```text
primeExponentCoordinates n : PrimeIndex -> Nat
```

Using the existing DkMath ABC valuation API, the bridge proves:

```text
padicValNat p (n * a^d)
  = padicValNat p n + d * padicValNat p a
```

for prime `p` and nonzero `n`, `a`.

The main projected consequence is:

```text
projectPrimeCoordinates d (n * a^d)
  = projectPrimeCoordinates d n
```

This is the first concrete formal Red Ribbon theorem for the ordinary natural
prime world: multiplication by a `d`-th power moves every prime exponent by a
multiple of `d`, and the period-`d` observer sees no change.

## Architectural decision

Do not model the ordinary prime world as `mod 1`.

The raw prime world is the retained valuation structure.  In the current
minimal remainder API, period `0` is the identity/unprojected view and period
`1` is the fully collapsed quotient view.

Also keep separate:

```text
Cosmic Formula degree d
Power-gauge projection period d
```

Even when a later theorem specializes both to `5`, they are distinct roles.

## Reuse decision

KUS remains the canonical support/blueprint preservation layer.  Structural
Arithmetic adds an observation/projection layer and should bridge to KUS rather
than replace it.

The prime-coordinate bridge reuses `DkMath.ABC.padicValNat_pow`; it does not
introduce a competing valuation API.

## Not yet implemented

1. KUS source-retaining observation wrapper / bridge.
2. DHNT dynamic real exponent scaling bridge.
3. Inter-period maps, especially canonical `n -> m` projection when `m | n`.
4. Primitive multiplicative direction / generated-closure API.
5. Promotion of finite-prime escape out of the Hackathon namespace.
6. Bridge between generic `DkMath.CosmicFormula.GN` and the structural
   projection vocabulary.
7. Bridge between specialized FLT5 `GN5` and generic `GN`.
8. Golden-unit modulo-fifth-power classification as a period-five gauge
   instance.
9. Import through wider public DkMath surfaces after build verification.

## Verification status

Repository edits are isolated on the work branch.  The ChatGPT execution
environment used for this checkpoint does not contain `lean` / `lake`, so a
local Lean build has not been run here.  The implementation deliberately reuses
APIs already present in the current `develop` source and keeps the first kernel
small.  Before merge, run at minimum:

```bash
lake build DkMath.NumberTheory.StructuralArithmetic.PowerGauge
lake build DkMath.NumberTheory.StructuralArithmetic.PrimeCoordinates
lake build DkMath.NumberTheory.StructuralArithmetic
```

Then run the appropriate wider DkMath build and `git diff --check`.
