# DkMath.Pow Implementation Plan

- Authors: D. and Wise Wolf
- Created: 2026-08-05
- Status: pre-implementation plan
- Conversation reachability key (`cid`): `6a721382-8e50-83ee-a3f3-b75e77a93476`

## 1. Purpose

The purpose of `DkMath.Pow` is not to duplicate Mathlib's elementary exponent laws.

Mathlib already proves the algebraic identities and provides root-related APIs. This package will organize those ingredients into a structural theory of:

- power fibers;
- power-root witnesses;
- fusion of powered states;
- rebasing to divisor exponents;
- presentations of the same value by different base-exponent pairs;
- later normalization and maximal-power-depth APIs.

The first mathematical reading is:

```text
A = a^d
B = b^d
        ↓ fusion
A * B = (a * b)^d
```

The corresponding structural reading is:

```text
PowFiber d A × PowFiber d B
  → PowFiber d (A * B)
```

## 2. Architectural position

The initial implementation lives in `DkMath.Pow`, but it must be written at the quality boundary expected of a future standalone `DkMathlib.Pow` package.

```text
Mathlib
  ↓
DkMath.Pow
  ↓
DkMath.PowerSwap
DkMath.CosmicFormula.PowBridge
  ↓
ABC / FLT / RH / Collatz / other research modules
```

The lower `Pow` layer must remain independent of all research targets.

## 3. Dependency rules

### Allowed dependencies

- Mathlib modules required for monoids, powers, `PNat`, gcd, roots, and homomorphisms;
- earlier files inside `DkMath.Pow`.

### Forbidden dependencies

The generic layer must not import:

```text
DkMath.ABC
DkMath.FLT
DkMath.RH
DkMath.Collatz
DkMath.CosmicFormula
DkMath.PowerSwap
DkMath.KUS
```

Connections to those modules belong in explicit bridge files outside the generic core.

### Typeclass policy

Every declaration should use the weakest practical assumptions.

Examples:

- `PowFiber`: `Monoid`;
- `PowFiber.map`: monoid homomorphisms;
- same-exponent multiplication: `CommMonoid`, or a later noncommutative version parameterized by `Commute`;
- order and injectivity results: added only in specialized files.

## 4. Planned module tree

```text
DkMath/Pow/
├── README.md
├── Basic.lean
├── Fiber.lean
├── Fusion.lean
├── Rebase.lean
├── Presentation.lean
├── NormalForm.lean          -- later checkpoint
├── NatDepth.lean            -- later checkpoint
├── RootsOfUnity.lean        -- later checkpoint
└── docs/
    ├── IMPLEMENTATION_PLAN.md
    ├── INITIAL_IMPLEMENTATION_BLUEPRINT.md
    └── DESIGN.md

DkMath/Pow.lean              -- public aggregator after the first API stabilizes
```

## 5. Checkpoint plan

## POW-000 — Documentation scaffold

Create the directory, landing README, implementation plan, blueprint, and design specification.

Deliverables:

```text
DkMath/Pow/README.md
DkMath/Pow/docs/IMPLEMENTATION_PLAN.md
DkMath/Pow/docs/INITIAL_IMPLEMENTATION_BLUEPRINT.md
DkMath/Pow/docs/DESIGN.md
```

No Lean theorem is introduced at this checkpoint.

## POW-001 — Basic fiber definitions

Create:

```text
DkMath/Pow/Basic.lean
DkMath/Pow/Fiber.lean
```

Initial public surface:

```lean
PowFiber
HasPowRoot
PowFiber.base
PowFiber.power_eq
PowFiber.one
PowFiber.map
```

Goals:

1. Establish the namespace and minimal import boundary.
2. Keep `PowFiber` as a proof-carrying root type.
3. Verify that the construction works for arbitrary monoids.
4. Add small examples over `ℕ` without importing research modules.

## POW-002 — Same-exponent fusion

Create `DkMath/Pow/Fusion.lean`.

Initial public surface:

```lean
PowFiber.mul
sameExponentFusion
sameExponentFusion_apply
```

Central law:

```text
a ∈ PowFiber d A
b ∈ PowFiber d B
--------------------------------
a * b ∈ PowFiber d (A * B)
```

The proof should be a thin structural lift of Mathlib's `mul_pow`.

This checkpoint must not introduce alternate copies of `mul_pow`, `pow_add`, or `pow_mul` under DkMath names unless a stable directional wrapper is genuinely needed by callers.

## POW-003 — Exponent rebasing

Create `DkMath/Pow/Rebase.lean`.

Initial public surface:

```lean
PowFiber.rebaseOfMul
PowFiber.rebase
PowFiber.toSquare_of_even
PowFiber.toExponent_of_dvd
```

Mathematical law:

```text
N = x^d
k ∣ d
------------------------
N = (x^(d / k))^k
```

The implementation should prefer an equality witness `d = k * m` internally, then provide a divisibility wrapper. This avoids making natural-number division the primitive proof mechanism.

Specialized square normalization is a wrapper, not the foundation.

## POW-004 — Mixed-exponent gcd fusion

Extend `Fusion.lean` with:

```lean
gcdExponentFusion
gcdExponentFusionFiber
```

Central identity:

```text
a^d * b^e
  = (a^(d / gcd d e) * b^(e / gcd d e))^(gcd d e)
```

This checkpoint records that equal exponents preserve the full exponent, while unequal exponents always preserve at least their gcd exponent.

Edge cases `d = 0`, `e = 0`, and `d = e = 0` must be tested explicitly rather than silently excluded.

## POW-005 — Power presentations

Create `DkMath/Pow/Presentation.lean`.

Initial public surface:

```lean
PowerPresentation
PowerPresentation.exponent
PowerPresentation.base
PowerPresentation.power_eq
PowerPresentation.rebase
```

Target representation:

```lean
def PowerPresentation (N : M) : Type _ :=
  Σ d : PNat, PowFiber (d : ℕ) N
```

This captures multiple presentations of one value, for example:

```text
64 = 8^2 = 4^3 = 2^6
```

The positive-exponent type prevents the degenerate universal presentation `x^0 = 1` from contaminating the main presentation space.

## POW-006 — Public aggregator and examples

Create:

```text
DkMath/Pow.lean
DkMath/Pow/Examples.lean     -- only if examples justify a separate file
```

The aggregator should re-export only stable modules.

Expected caller form:

```lean
import DkMath.Pow

open DkMath.Pow
```

No global notation should be introduced yet.

## POW-007 — Normal forms and natural-number depth

This is a later checkpoint and must not block the initial package.

Candidate surface:

```lean
PowNormalForm
HasPowNormalForm
Nat.powerDepth
Nat.maxPowerPresentation
```

The design must account for the exceptional values `0` and `1`, which possess positive power presentations of arbitrarily large exponent.

Possible codomains for depth:

```text
WithTop ℕ
```

or a domain-restricted finite definition for `2 ≤ n`.

No definition should be selected until existing `DkMath.PowerSwap.NormalForm` is audited for reuse and duplication.

## POW-008 — Root-of-unity action

For suitable commutative groups or fields, connect a nonempty fiber with `rootsOfUnity`.

Conceptual target:

```text
one selected d-th root of N
  + action of μ_d
  = the full d-th-root fiber of N
```

This is not part of the first implementation milestone.

## POW-009 — Research bridges

Only after the generic API is stable, create thin bridges such as:

```text
DkMath/PowerSwap/PowBridge.lean
DkMath/CosmicFormula/PowBridge.lean
```

Possible DkMath interpretations:

```text
PowFiber             → true-core fiber
PowFiber.mul         → true-core fusion
PowFiber.rebase      → standard-core normalization
PowerPresentation    → same-value power world
```

These names and interpretations must not leak back into the generic `DkMath.Pow` definitions.

## 6. Initial milestone

The first implementation milestone ends when the following API is build-verified:

```text
PowFiber
HasPowRoot
PowFiber.one
PowFiber.map
PowFiber.mul
PowFiber.rebaseOfMul
PowFiber.rebase
sameExponentFusion
gcdExponentFusion
PowerPresentation
```

At that point the package should be usable independently of PowerSwap and CosmicFormula.

## 7. Verification gates

Each checkpoint should satisfy:

1. The target module builds under the repository's current Lean and Mathlib versions.
2. No `sorry` or new axiom is introduced.
3. Public declarations have docstrings.
4. Imports are audited for accidental research dependencies.
5. Existing Mathlib declarations are not duplicated without a structural reason.
6. Small executable examples or `example` proofs cover edge cases.
7. Public names are stable enough for later extraction.

## 8. Future extraction gate

Moving the generic core to `DkMathlib.Pow` becomes reasonable when:

- no generic file imports a DkMath research module;
- at least two independent DkMath domains consume the API;
- theorem names and namespace boundaries have stabilized;
- the public aggregator is small and documented;
- examples demonstrate value beyond a single research project.

The migration should then follow:

```text
DkMath.Pow.*
  ↓ move generic implementation
DkMathlib.Pow.*

DkMath.Pow.*
  ↓ retain compatibility imports and DkMath-specific bridges
```

## 9. Provenance

This implementation plan derives from the DkMath discussion on power fibers, true-core fusion, PowerSwap, and the future Mathlib-compatible `DkMathlib` layer.

Reachability key:

```text
cid: 6a721382-8e50-83ee-a3f3-b75e77a93476
```

The key must remain available in successor design documents so that the original reasoning path can be recovered.