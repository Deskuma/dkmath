# PUU-L025 — Fresh-Prime Lift-Index Affine Normal Form / Constant Phase Radius

## 0. Status / purpose

PUU-L024 established the reflection involution on the fresh-prime raw lift-index circle:

```text
rho(j) = 2*jzero - j
F(rho(j)) = -F(j)
```

with the deleted index as the unique fixed center for an odd fresh prime, the `+a/-a` phase pair exchanged by reflection, and neutral indices arranged in fixed-point-free two-cycles.

This checkpoint should sharpen that geometry to an explicit affine normal form.  The key new invariant is that the displacement of the two phase indices from the deleted center depends only on `a`, the old period `M`, and the fresh prime `q`; it does **not** depend on the old representative `b`.

Remain entirely inside `DkMath.NumberTheory.PrimorialUniverse`.  Do not import Legendre consumers.

Preferred module:

```lean
DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndexNormalForm
```

Preferred import:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndexReflection
```

Export through `DkMath.NumberTheory.PrimorialUniverse` and update the facade docstring.

---

## 1. Phase radius

Let

```text
M = finitePrimeBasisProduct S
```

and let `q` be fresh prime.  Since `M : ZMod q` is nonzero, define the fresh-prime phase radius by dividing the anchor residue by the old-period residue.

Preferred definition shape:

```lean
noncomputable def freshPrimePhaseRadius
    (S : Finset ℕ) (q a : ℕ) : ZMod q :=
  (a : ZMod q) / (finitePrimeBasisProduct S : ZMod q)
```

or an equivalent inverse-multiplication definition if that is smoother in Mathlib:

```text
a * M⁻¹
```

The exact implementation is flexible, but the public semantic API should expose the radius as the unique `d` satisfying

```text
d * M = a    in ZMod q.
```

Prove a theorem of the shape:

```lean
freshPrimePhaseRadius_mul_period
```

under `hS`, `hq`, `hqS`.

If useful, also prove uniqueness:

```lean
freshPrimePhaseRadius_unique
```

for any `d : ZMod q` with `d * M = a`.

---

## 2. Radius nonzero for a coprime anchor

Under the same coprime-anchor hypothesis already used by L020–L024,

```lean
hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S))
```

prove:

```lean
freshPrimePhaseRadius_ne_zero
```

for fresh prime `q`.

This is the normalized version of the existing fact that `a : ZMod q ≠ 0` and `M : ZMod q ≠ 0`.

Do not overstate uniqueness of natural representatives; this theorem is about the `ZMod q` radius.

---

## 3. Explicit plus/minus coordinates around the deleted center

Let `jplus`, `jminus`, `jzero` satisfy the L022 predicates.

Prove the exact coordinate formulas:

```lean
freshPrime_plus_index_eq_center_add_radius
```

with conclusion

```lean
(jplus : ZMod q) =
  (jzero : ZMod q) + freshPrimePhaseRadius S q a
```

and

```lean
freshPrime_minus_index_eq_center_sub_radius
```

with conclusion

```lean
(jminus : ZMod q) =
  (jzero : ZMod q) - freshPrimePhaseRadius S q a
```

Use the affine raw-lift equations and cancellation by nonzero `M` / multiplication by `M⁻¹`; do not recover these merely from cardinality or reflection.

These are the central theorems of L025.

---

## 4. Constant-radius theorem

Make the independence from the old representative explicit.

For any two old representatives `b₁`, `b₂` with their own deleted centers and plus/minus indices, prove that their center-relative phase offsets agree:

```lean
freshPrime_plus_offsets_eq_across_old_representatives
```

conceptually:

```text
jplus₁ - jzero₁ = jplus₂ - jzero₂ = radius
```

and similarly for minus:

```text
jminus₁ - jzero₁ = jminus₂ - jzero₂ = -radius.
```

A single theorem returning both equalities is also acceptable.

The important mathematical statement is:

```text
changing b translates the center,
but does not change the phase radius.
```

Do not require the two old representatives to be equal.  Use only the existing phase-fiber / coprime assumptions required to obtain the distinguished indices.

---

## 5. Phase separation

Derive the center-free separation formula:

```lean
freshPrime_phase_index_separation
```

with conclusion equivalent to

```text
jplus - jminus = 2 * radius      in ZMod q.
```

This separation is independent of `b` and `jzero`.

For odd fresh prime and coprime anchor, it should be nonzero because the plus/minus indices are distinct.  An optional theorem may record:

```lean
2 * freshPrimePhaseRadius S q a ≠ 0
```

under the existing odd/coprime hypotheses.

Do not introduce an order, metric, or smallest positive distance on the circle.

---

## 6. Normalized coordinate about the deleted center

If useful for a clean API, define or prove a normalized center-relative coordinate:

```text
u(j) = (j - jzero) * M
```

or equivalently `j - jzero` itself after multiplication by `M`.

The distinguished indices should satisfy exactly:

```text
u(jplus)  = +a
u(jzero)  = 0
u(jminus) = -a
```

This may be a theorem bundle rather than a new definition.

The goal is to expose the affine normal form

```text
center + radius,
center,
center - radius
```

rather than only the reflection identity.

---

## 7. Visible `6 → 30` regression

Use the existing public regression:

```text
S = {2,3}
M = 6
q = 5
a = b = 1
jplus = 0
jzero = 4
jminus = 3
```

Since `6 ≡ 1 (mod 5)`, the radius is `1` in `ZMod 5`.

Record via the public L025 API:

```text
radius = 1
0 = 4 + 1
3 = 4 - 1
0 - 3 = 2 * 1
```

all in `ZMod 5`.

Avoid a regression proved only by detached `decide`; route it through the public normal-form theorems where practical.

---

## 8. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-fresh-prime-lift-index-affine-normal-form-260828.md
```

The report must state explicitly:

1. L024 gave a reflection involution; L025 gives explicit center/radius coordinates.
2. The radius is `a / M` in `ZMod q` (or the equivalent inverse-product form used in Lean).
3. The deleted center depends on the old representative `b`, but the phase radius does not.
4. The phase separation `2*radius` is therefore also independent of `b`.
5. This remains finite provider-side congruence geometry and is not an escape or prime-existence theorem.

---

## 9. A+ rubric

Outcome A+ if the implementation establishes, without new consumer assumptions:

1. a public phase-radius coordinate,
2. `radius * M = a`,
3. nonzero radius under coprime anchor,
4. `jplus = jzero + radius`,
5. `jminus = jzero - radius`,
6. explicit independence of the relative offsets from `b`,
7. phase separation `jplus - jminus = 2*radius`,
8. the `6 → 30` normal-form regression,
9. facade export + docstrings + report.

---

## STOP

Do **not** add in L025:

- Legendre or `escapingSquareOffsets`,
- escape existence,
- Jacobsthal / wheel-gap bounds,
- neutral primality/compositeness,
- PowerSwap / GN / CosmicFormula,
- PNT / RH,
- prime powers,
- arbitrary-anchor cardinality,
- an ordered/geodesic notion of circle distance,
- a claim that the radius is a globally canonical natural number rather than a `ZMod q` coordinate.

L025 is specifically the affine normal form and constant-radius theorem for the fresh-prime lift-index geometry.
