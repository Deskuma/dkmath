# DkMath.Pow

- Authors: D. and Wise Wolf
- Created: 2026-08-05
- Status: design checkpoint; Lean implementation has not started
- Conversation reachability key (`cid`): `6a721382-8e50-83ee-a3f3-b75e77a93476`

`DkMath.Pow` is the planned general-purpose layer for power presentations, power fibers, exponent fusion, and exponent rebasing.

The module is intentionally designed as a Mathlib-compatible extension rather than as a replacement for Mathlib's power API.

Mathlib already supplies the algebraic laws such as `pow_add`, `pow_mul`, `mul_pow`, `map_pow`, roots, and square predicates. `DkMath.Pow` will reuse those results and lift them into reusable structures.

```text
Mathlib
  power laws and root APIs
        ↓
DkMath.Pow
  PowFiber / fusion / rebase / presentation / normalization
        ↓
DkMath.PowerSwap
DkMath.CosmicFormula.PowBridge
DkMath.ABC / DkMath.FLT / other research bridges
```

## Design goal

The first central object is the fiber of bases whose fixed power realizes a value.

```lean
def PowFiber
    {M : Type*} [Monoid M]
    (d : ℕ) (N : M) : Type _ :=
  {x : M // x ^ d = N}
```

For a commutative multiplicative world, equal-exponent fibers admit a natural fusion map.

```text
PowFiber d A × PowFiber d B
  → PowFiber d (A * B)
```

This turns the ordinary identity

```text
a^d * b^d = (a * b)^d
```

into a typed structural operation.

## Scope

The initial implementation is expected to provide:

- `PowFiber`
- `HasPowRoot`
- `PowFiber.one`
- `PowFiber.mul`
- `PowFiber.map`
- exponent rebasing along divisibility
- same-exponent fusion
- gcd-exponent fusion
- `PowerPresentation`
- a thin bridge toward existing `DkMath.PowerSwap`

The generic layer must depend only on Mathlib and lower-level `DkMath.Pow` modules. It must not import `DkMath.ABC`, `DkMath.FLT`, `DkMath.RH`, `DkMath.Collatz`, or other research applications.

## Future extraction

The implementation should be written so that the generic files can later move almost mechanically from

```text
DkMath.Pow.*
```

to

```text
DkMathlib.Pow.*
```

with `DkMath.Pow` retained as a compatibility and bridge layer.

The intended public relation is:

```text
Mathlib + DkMathlib
  = standard mathematics plus reusable structural extensions

DkMath
  = research applications built on that extension layer
```

## Documentation

- [Implementation plan](./docs/IMPLEMENTATION_PLAN.md)
- [Initial implementation blueprint](./docs/INITIAL_IMPLEMENTATION_BLUEPRINT.md)
- [Design specification](./docs/DESIGN.md)

## Provenance

This directory was created from the DkMath power-fiber and true-core fusion discussion.

The conversation can be reached by the project conversation key:

```text
cid: 6a721382-8e50-83ee-a3f3-b75e77a93476
```

This key is part of the design provenance and should remain in the documentation when the module is refactored or extracted.