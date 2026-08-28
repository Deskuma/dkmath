# PUU-L026 — Fresh-Prime Deleted-Center Transport / Old-Representative Translation Law

## 0. Status / purpose

PUU-L025 completed the fresh-prime affine normal form

```text
jplus  = jzero + radius
jminus = jzero - radius
radius = a / M
```

with the crucial invariant that the radius is independent of the old representative `b`.

This checkpoint begins the revised roadmap Phase E1.  The local affine geometry is now strong enough; do **not** continue adding local reflection/cardinality lemmas for their own sake.  Instead, isolate the part that actually moves when the old representative changes: the deleted center.

Remain entirely inside `DkMath.NumberTheory.PrimorialUniverse`.  Do not import Legendre consumers.

Preferred module:

```lean
DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndexCenterTransport
```

Preferred import:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseLiftIndexNormalForm
```

Export through `DkMath.NumberTheory.PrimorialUniverse` and update the facade docstring.

---

## 1. Canonical deleted-center coordinate

Let

```text
M := finitePrimeBasisProduct S.
```

For a fresh prime `q`, define the canonical deleted-center coordinate of an old representative `b` by

```text
C(b) := -b * M⁻¹    in ZMod q.
```

Preferred definition shape:

```lean
noncomputable def freshPrimeDeletedCenterCoord
    (S : Finset ℕ) (q b : ℕ) : ZMod q :=
  -(b : ZMod q) * (finitePrimeBasisProduct S : ZMod q)⁻¹
```

Equivalent division notation is acceptable.

The semantic theorem should be:

```lean
freshPrimeDeletedCenterCoord_zero_residue
```

with conclusion equivalent to

```text
(b : ZMod q) + C(b) * M = 0.
```

Use `hS`, `hq`, `hqS` only as required to invert/cancel `M`.

---

## 2. Center uniqueness

Prove that the zero-residue equation determines the center uniquely:

```lean
freshPrimeDeletedCenterCoord_unique
```

Conceptually:

```text
b + z*M = 0
    →
z = C(b).
```

This theorem should not require a phase anchor `a`, coprime-anchor hypothesis, or Legendre-side structure.

This is an important strengthening: deleted-center transport belongs to the raw fresh-prime lift geometry itself.

---

## 3. Existing deleted index equals the canonical center

For

```lean
hzero : IsFreshPrimeDeletedLiftIndex S q b jzero
```

prove:

```lean
freshPrime_deleted_index_eq_centerCoord
```

with conclusion

```lean
(jzero : ZMod q) = freshPrimeDeletedCenterCoord S q b.
```

Route through the public affine raw-lift formula / zero residue and the uniqueness theorem above.

Do not prove this by finite enumeration or by re-running the unique-deletion existence proof.

---

## 4. Old-representative center transport

For two old representatives `b₁`, `b₂`, prove the exact translation law

```lean
freshPrime_deleted_center_transport
```

with conclusion equivalent to

```text
C(b₂) - C(b₁)
  = (b₁ - b₂) * M⁻¹
```

in `ZMod q`.

An equivalent orientation is acceptable if documented clearly, but keep one canonical public orientation.

Also provide the witness-index version when `jzero₁` and `jzero₂` satisfy the deleted-index predicates:

```text
jzero₂ - jzero₁
  = (b₁ - b₂) * M⁻¹.
```

This is the central theorem of PUU-L026.

The mathematical reading must be explicit:

```text
changing b translates the center affinely;
there is no change in radius.
```

---

## 5. Fully explicit phase coordinates with the center witness eliminated

Combine L025 with the canonical center coordinate.

For a `+a` phase index and the corresponding deleted index, derive a public theorem equivalent to

```text
jplus = C(b) + R(a)
```

and for the minus index:

```text
jminus = C(b) - R(a).
```

where

```text
C(b) = -b/M
R(a) =  a/M.
```

If algebraically convenient, expose the simplified forms

```text
jplus  = (a - b) / M
jminus = -(a + b) / M
```

in `ZMod q`, but keep the `center ± radius` form as the main semantic API.

These theorems should make the dependence split visible:

```text
old representative b  → center
anchor a              → radius
fresh basis period M  → common scale.
```

---

## 6. Translation of the phase pair across old representatives

For fixed `S`, `q`, `a` and two representatives `b₁`, `b₂`, prove that both phase sheets translate by exactly the same center displacement.

Preferred theorem shape:

```lean
freshPrime_phase_pair_translates_with_center
```

Conceptually:

```text
jplus₂  - jplus₁  = C(b₂) - C(b₁)
jminus₂ - jminus₁ = C(b₂) - C(b₁).
```

Hence

```text
phase pair shape is rigid;
only its center translates.
```

This is stronger and more useful for later anchor dynamics than re-stating radius equality alone.

No ordering or metric interpretation is needed.

---

## 7. Visible `6 → 30` two-representative regression

Use

```text
S = {2,3}
M = 6
q = 5
a = 1.
```

Compare the two old representatives already visible in the wheel/phase regressions:

```text
b₁ = 1
b₂ = 5.
```

The canonical centers should be

```text
C(1) = 4
C(5) = 0
```

in `ZMod 5`, since `M = 1` modulo `5`.

Record the transport

```text
C(5) - C(1) = 0 - 4 = 1
(1 - 5) / 6 = 1       in ZMod 5.
```

With radius `R = 1`, the phase pairs are

```text
b = 1 : center 4 → {0,3}
b = 5 : center 0 → {1,4}
```

at the index level, corresponding to the already known enlarged seats

```text
{1,19}  over old representative 1
{11,29} over old representative 5.
```

Where practical, route this regression through the public center/radius/transport API rather than detached `decide`.

---

## 8. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-fresh-prime-deleted-center-transport-260828.md
```

The report must state explicitly:

1. L025 fixed the radius; L026 isolates the moving center.
2. The canonical center is `-b/M` in `ZMod q`.
3. The center is uniquely characterized by the deleted zero-residue equation.
4. Changing the old representative translates the center by `(b₁-b₂)/M`.
5. Both phase sheets translate by the same displacement, while the radius remains fixed.
6. This is the first transport checkpoint of revised roadmap Phase E1.
7. The result remains provider-side and contains no square-shell escape or prime-existence conclusion.

---

## 9. A+ rubric

Outcome A+ if the implementation establishes, without consumer assumptions:

1. canonical deleted-center coordinate `C(b) = -b/M`,
2. its zero-residue semantic theorem,
3. uniqueness of that coordinate,
4. identification of any deleted natural index with `C(b)`,
5. exact center-translation law across `b₁,b₂`,
6. explicit `center ± radius` phase coordinates using the canonical center,
7. rigid translation of both phase sheets across old representatives,
8. the `6 → 30`, `b=1 ↔ 5` transport regression,
9. facade export + docstrings + report.

---

## STOP

Do **not** add in L026:

- Legendre or `escapingSquareOffsets`,
- square-shell escape existence,
- Jacobsthal / wheel-gap bounds,
- neutral-seat primality/compositeness,
- another cardinality or reflection-orbit refinement,
- PowerSwap / GN / CosmicFormula,
- PNT / RH,
- prime powers,
- ordered/geodesic circle distance,
- the square-anchor step `n → n+1` itself.

L026 is specifically the old-representative center-transport theorem.  If it closes, the next phase should return to PUU-L010 and transport these coordinates under the moving square anchor.
