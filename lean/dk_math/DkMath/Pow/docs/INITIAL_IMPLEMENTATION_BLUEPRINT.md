# DkMath.Pow Initial Implementation Blueprint

- Authors: D. and Wise Wolf
- Created: 2026-08-05
- Status: initial Lean blueprint; declarations are planned, not yet implemented
- Conversation reachability key (`cid`): `6a721382-8e50-83ee-a3f3-b75e77a93476`

## 1. Goal

This blueprint fixes the first implementation surface before proof work begins.

The first release should be small enough to audit, generic enough to extract later, and strong enough to support `DkMath.PowerSwap` and CosmicFormula bridges without redesigning the core.

The blueprint intentionally separates:

```text
Mathlib algebraic facts
  ↓
proof-carrying power structures
  ↓
DkMath research interpretations
```

## 2. Namespace and import policy

All initial declarations live under:

```lean
namespace DkMath.Pow
```

The first files should import the narrowest suitable Mathlib modules. Exact imports must be confirmed against the repository's current Mathlib version, but the implementation should not begin with `import DkMath` or another large umbrella import.

Candidate import families:

```text
Mathlib.Algebra.Group.Defs
Mathlib.Algebra.Group.Hom.Defs
Mathlib.Algebra.Group.PNatPowAssoc
Mathlib.Data.Nat.GCD.Basic
```

Do not copy this list mechanically. Audit the actual declarations used by each file.

## 3. `Basic.lean`

Purpose:

- reserve the namespace;
- provide only genuinely useful directional wrappers;
- avoid renaming the whole Mathlib power API.

Candidate theorem shapes:

```lean
namespace DkMath.Pow

variable {M : Type*}

/-- Multiplication of equal-exponent powers, oriented toward a single powered base. -/
theorem sameExponentFusion
    [CommMonoid M]
    (a b : M) (d : ℕ) :
    a ^ d * b ^ d = (a * b) ^ d := by
  simpa using (mul_pow a b d).symm

/-- A power with a product exponent can be viewed as a power of a power. -/
theorem rebaseExponentOfMul
    [Monoid M]
    (x : M) (k m : ℕ) :
    x ^ (k * m) = (x ^ m) ^ k := by
  -- Proof direction and `pow_mul` orientation must be checked in the active Mathlib.
  simpa [Nat.mul_comm] using (pow_mul x m k).symm

end DkMath.Pow
```

The exact proof term may change after API inspection. The statement shape is the design commitment.

## 4. `Fiber.lean`

### 4.1 Core definition

```lean
namespace DkMath.Pow

variable {M : Type*} [Monoid M]

/-- Bases whose `d`-th power realizes the value `N`. -/
def PowFiber (d : ℕ) (N : M) : Type _ :=
  {x : M // x ^ d = N}

/-- Propositional existence of a `d`-th power root of `N`. -/
def HasPowRoot (d : ℕ) (N : M) : Prop :=
  Nonempty (PowFiber d N)

end DkMath.Pow
```

### 4.2 Basic projections

The subtype already provides `.1`, `.2`, and coercions, but named accessors may improve discoverability.

```lean
namespace PowFiber

variable {M : Type*} [Monoid M]
variable {d : ℕ} {N : M}

/-- The underlying base of a power-fiber witness. -/
def base (x : PowFiber d N) : M := x.1

@[simp]
theorem power_eq (x : PowFiber d N) : x.1 ^ d = N := x.2

end PowFiber
```

Avoid adding aliases that provide no API value.

### 4.3 Canonical unit witness

```lean
namespace PowFiber

variable {M : Type*} [Monoid M]

/-- The unit is a power root of the unit for every exponent. -/
def one (d : ℕ) : PowFiber d (1 : M) :=
  ⟨1, by simp⟩

end PowFiber
```

### 4.4 Mapping along monoid homomorphisms

```lean
namespace PowFiber

variable {M N : Type*} [Monoid M] [Monoid N]

/-- Transport a power-root witness through a monoid homomorphism. -/
def map
    (f : M →* N)
    {d : ℕ} {A : M}
    (x : PowFiber d A) :
    PowFiber d (f A) :=
  ⟨f x.1, by
    simpa using congrArg f x.2⟩

end PowFiber
```

The proof should rely on `map_pow` through simplification.

### 4.5 Expected simp surface

Use `[simp]` conservatively for:

```text
PowFiber.power_eq
PowFiber.map_base, if introduced
```

Do not mark structural fusion or rebasing theorems as global simp rules until rewriting behavior has been tested.

## 5. `Fusion.lean`

### 5.1 Same-exponent fiber multiplication

```lean
namespace DkMath.Pow.PowFiber

variable {M : Type*} [CommMonoid M]
variable {d : ℕ} {A B : M}

/-- Fuse two roots carrying the same exponent. -/
def mul
    (x : PowFiber d A)
    (y : PowFiber d B) :
    PowFiber d (A * B) :=
  ⟨x.1 * y.1, by
    rw [mul_pow, x.2, y.2]⟩

end DkMath.Pow.PowFiber
```

This is the first structural theorem of the package.

### 5.2 Fiber-level theorem form

A theorem exposing the underlying base may be useful:

```lean
@[simp]
theorem PowFiber.mul_base
    {M : Type*} [CommMonoid M]
    {d : ℕ} {A B : M}
    (x : PowFiber d A)
    (y : PowFiber d B) :
    (x.mul y : M) = x.1 * y.1 := rfl
```

Whether the subtype coercion syntax elaborates as written must be confirmed during implementation.

### 5.3 Mixed-exponent gcd fusion

The theorem shape to target is:

```lean
theorem gcdExponentFusion
    {M : Type*} [CommMonoid M]
    (a b : M) (d e : ℕ) :
    a ^ d * b ^ e =
      (a ^ (d / Nat.gcd d e) *
       b ^ (e / Nat.gcd d e)) ^ Nat.gcd d e := by
  -- Expand the power of a product, apply `pow_mul`,
  -- then use `Nat.div_mul_cancel` with gcd divisibility.
  sorry
```

The actual implementation must contain no `sorry`; this placeholder only marks the proof plan in the design document.

Required edge-case examples:

```lean
example {M : Type*} [CommMonoid M] (a b : M) :
    a ^ 0 * b ^ 0 =
      (a ^ (0 / Nat.gcd 0 0) * b ^ (0 / Nat.gcd 0 0)) ^ Nat.gcd 0 0 := by
  simpa using gcdExponentFusion a b 0 0
```

Additional examples should cover equal exponents and coprime exponents.

## 6. `Rebase.lean`

The internal primitive should use a multiplication witness rather than division.

### 6.1 Equality-witness primitive

```lean
namespace DkMath.Pow.PowFiber

variable {M : Type*} [Monoid M]
variable {d k : ℕ} {N : M}

/-- Rebase a `d`-power witness to exponent `k` from an explicit factorization `d = k * m`. -/
def rebaseOfMul
    (x : PowFiber d N)
    (m : ℕ)
    (hd : d = k * m) :
    PowFiber k N := by
  refine ⟨x.1 ^ m, ?_⟩
  -- Rewrite the target with `pow_mul` and `hd`.
  -- Exact orientation must be confirmed against Mathlib.
  simpa [hd, Nat.mul_comm] using x.2

end DkMath.Pow.PowFiber
```

The proof skeleton may need `rw [← pow_mul]` or an explicit `calc`. The mathematical interface is fixed.

### 6.2 Divisibility wrapper

```lean
def PowFiber.rebase
    {M : Type*} [Monoid M]
    {d k : ℕ} {N : M}
    (x : PowFiber d N)
    (hk : k ∣ d) :
    PowFiber k N := by
  obtain ⟨m, rfl⟩ := hk
  exact x.rebaseOfMul m rfl
```

The exact equality orientation produced by `obtain` must be checked.

### 6.3 Square specialization

```lean
def PowFiber.toSquare_of_even
    {M : Type*} [Monoid M]
    {d : ℕ} {N : M}
    (x : PowFiber d N)
    (hd : Even d) :
    PowFiber 2 N := by
  exact x.rebase hd
```

This relies on the representation of `Even d` as `2 ∣ d`; confirm coercion or use `hd.two_dvd` if required by the active API.

The specialized theorem should remain a wrapper around generic rebasing.

## 7. `Presentation.lean`

### 7.1 Positive-exponent presentation

```lean
namespace DkMath.Pow

variable {M : Type*} [Monoid M]

/-- A positive-exponent presentation of the value `N`. -/
def PowerPresentation (N : M) : Type _ :=
  Σ d : PNat, PowFiber (d : ℕ) N

end DkMath.Pow
```

If `PNat` import weight or coercion ergonomics are unsuitable, use the explicit subtype:

```lean
Σ d : {n : ℕ // 0 < n}, PowFiber d.1 N
```

The decision must be made after a minimal compilation experiment.

### 7.2 Accessors

Candidate public surface:

```lean
namespace PowerPresentation

variable {M : Type*} [Monoid M] {N : M}

/-- Positive exponent used by the presentation. -/
def exponent (p : PowerPresentation N) : PNat := p.1

/-- Base used by the presentation. -/
def base (p : PowerPresentation N) : M := p.2.1

@[simp]
theorem power_eq (p : PowerPresentation N) :
    p.base ^ (p.exponent : ℕ) = N :=
  p.2.2

end PowerPresentation
```

### 7.3 Example target

```lean
example : PowerPresentation (64 : ℕ) :=
  ⟨⟨6, by decide⟩, ⟨2, by norm_num⟩⟩
```

Other presentations of `64` should be examples, not hard-coded library declarations.

## 8. Public aggregator

After the first modules stabilize:

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Pow.Basic
import DkMath.Pow.Fiber
import DkMath.Pow.Fusion
import DkMath.Pow.Rebase
import DkMath.Pow.Presentation
```

Expected caller usage:

```lean
import DkMath.Pow

open DkMath.Pow
```

The root namespace should not be opened automatically by imports.

## 9. Initial tests

The first checkpoint should include examples for:

```text
PowFiber 3 8 over ℕ
PowFiber.mul for 8 and 27 at exponent 3
rebase from exponent 6 to exponent 2
rebase from exponent 6 to exponent 3
PowerPresentation 64 with exponents 2, 3, and 6
gcd fusion with exponents 6 and 4
zero-exponent edge behavior
```

Tests should use `example` declarations or a dedicated examples file, not pollute the public theorem namespace.

## 10. Deferred items

Do not add these in the first implementation:

- custom notation for fibers;
- root-of-unity torsor instances;
- canonical root choices over `ℝ`, `ℂ`, `ℕ`, or `ℤ`;
- `Nat.powerDepth` before the `0` and `1` semantics are fixed;
- automatic normal-form tactics;
- CosmicFormula names such as true core or magic core inside the generic namespace;
- compatibility aliases for a future `DkMathlib` before extraction actually occurs.

## 11. First Codex-sized task

A small first implementation request can be limited to:

```text
Create Basic.lean and Fiber.lean.
Implement PowFiber, HasPowRoot, PowFiber.one, and PowFiber.map.
Add docstrings and four small examples.
Do not create the aggregator yet.
Do not import any DkMath research module.
```

The second task can then add same-exponent fusion independently.

## 12. Provenance

This blueprint records the first concrete Lean surface derived from the power-fiber discussion.

Reachability key:

```text
cid: 6a721382-8e50-83ee-a3f3-b75e77a93476
```

The key should be copied into successor implementation reports and handoff documents.