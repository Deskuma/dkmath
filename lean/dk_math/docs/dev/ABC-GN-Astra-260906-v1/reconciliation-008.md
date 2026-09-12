# RECONCILIATION-008 — DkMath.Lib / FLT-prime-generalization alignment

## Status

The ABC-GN v1 branch has been fast-forwarded to the current `develop` head after the FLT prime-generalization refactor.

This note records the delta between the ABC-GN production freeze (`LUNA-002` through `LUNA-007`) and the newer promoted `DkMath.Lib` / odd-prime FLT architecture.

No new ABC theorem is claimed here.

---

## 1. New promoted infrastructure relevant to ABC-GN

The new `DkMath.Lib.NumberTheory` layer now contains reusable generic APIs including:

```text
PadicValNat
PowerFactor
IdealPowerFactor
PrincipalIdealPower
UnitPowerSector
```

The odd-prime FLT architecture uses these in the chain:

```text
prime-adic exact split
-> TraceOne coordinates
-> conjugate-coprime residual ideals
-> residual principal ideal = idealRoot^p
-> class-group p-torsion hypothesis
-> unit * element^p
-> unit-sector normalization.
```

This is compatible in spirit with the ABC-GN v1 Eisenstein work, but it does not prove the ABC-side factorization-existence problem.

---

## 2. Existing ABC-GN v1 Eisenstein layer

LUNA-006/007 currently owns the neutral coordinate implementation at:

```text
DkMath.NumberTheory.EisensteinCoordinates
```

with:

```text
eisensteinCoord
norm_eisensteinCoord
eisensteinCoord_mul
eisensteinCoord_sq
eisensteinCoord_mul_sq
norm_eisensteinCoord_mul_sq
eisenstein_square_coefficient_coprime
```

and the conditional explicit-factor consequences:

```text
beta * gamma^2 = (a+2)+omega
-> exact coordinate equations
-> coefficient-one Bezout relation
-> IsCoprime square coefficients
-> cubic norm factor identity.
```

The mathematics remains valid, but the reusable implementation now belongs conceptually under `DkMath.Lib.NumberTheory`.

---

## 3. Promotion gap

The current state is therefore:

```text
old/current owner:
  DkMath.NumberTheory.EisensteinCoordinates

new preferred stable owner:
  DkMath.Lib.NumberTheory.EisensteinCoordinates
```

The intended migration pattern should match the existing `PadicValNat` promotion:

```text
DkMath.Lib.NumberTheory.EisensteinCoordinates
  = canonical implementation

DkMath.NumberTheory.EisensteinCoordinates
  = compatibility facade for historical consumers.
```

ABC production modules should import the new Lib owner directly after the migration.

---

## 4. p=3 carrier boundary is an API boundary, not a mathematical type gap

The FLT prime-generalization closeout records a p=3 boundary between:

```text
existing FLT3 sector API:
  EisensteinInt

generic odd-prime API:
  TraceOneInt (-1) at p=3.
```

However the existing FLT3 substrate defines:

```text
abbrev EisensteinInt := TraceOneInt (-1).
```

Therefore no nontrivial carrier equivalence is missing.

Also, by definition of the signed-prime parameter,

```text
signedPrimeParameter 3 = -1.
```

Hence the generic p=3 TraceOne carrier and the FLT3 Eisenstein carrier are definitionally the same underlying ring.

The remaining mismatch is:

```text
1. namespace / API ownership;
2. coordinate convention;
3. unit-sector packaging.
```

---

## 5. Coordinate convention

The FLT3 production substrate uses the trace-one basis

```text
r + s*tau,

tau^2 = tau - 1.
```

The ABC-GN neutral module uses standard Eisenstein coordinates

```text
m + n*omega,

omega^2 + omega + 1 = 0,
```

represented inside the same `TraceOneInt (-1)` carrier by

```text
eisensteinCoord m n = <m,-n>,

tau = -omega.
```

Thus the bridge is only the coordinate sign conversion

```text
(m,n)_omega <-> (m,-n)_tau.
```

No new ring is required.

---

## 6. Unit-sector compatibility opportunity

FLT3 already proves that every Eisenstein unit is one of six units and normalizes units modulo cubes to three sectors:

```text
1
tau
tau^2
```

via `exists_sector_mul_cube_of_unit`.

The new generic Lib layer defines:

```text
UnitPowerSectorSystem R p
```

with exactly the abstraction needed to represent units modulo p-th powers.

Therefore the existing FLT3 theorem should be packageable as:

```text
UnitPowerSectorSystem (TraceOneInt (-1)) 3.
```

This would close the p=3 unit-sector API mismatch without changing the FLT3 mathematics.

It does NOT by itself prove a new FLT theorem or an ABC factorization theorem.

---

## 7. Relation to ABC-GN factorization research

The new Lib principal-ideal bridge supplies a generic route:

```text
span(a) = I^p
+ principalization / class-group hypothesis
-> a = unit * gamma^p
-> unit-sector normalization.
```

This is structurally adjacent to the ABC-GN research target

```text
(a+2)+omega = beta * gamma^2.
```

But the ABC target is exponent 2 on a factor inside a specific cubic-norm decomposition, while the FLT generic architecture concerns an ideal p-th-power endpoint under explicit hypotheses.

No implication between these two is asserted at this checkpoint.

The useful new fact is architectural:

```text
if future ABC research produces the required ideal-power statement,
DkMath.Lib now contains the generic element/unit-sector machinery needed downstream.
```

---

## 8. Required reconciliation implementation

The next coding-only task should:

```text
A. promote EisensteinCoordinates into DkMath.Lib.NumberTheory;
B. preserve the historical DkMath.NumberTheory module as a compatibility facade;
C. update ABC-GN Eisenstein modules to import/use the Lib owner directly;
D. add the new Lib module to DkMath.Lib;
E. prove signedPrimeParameter 3 = -1;
F. add a thin FLT3/Lib bridge showing the omega/tau coordinate conversion;
G. package the existing FLT3 cube-unit classification as
   UnitPowerSectorSystem (TraceOneInt (-1)) 3.
```

No ABC asymptotic estimate, factorization existence, class-group theorem, or general FLT endpoint should be added.

---

## 9. Post-reconciliation architecture

Target dependency direction:

```text
DkMath.NumberTheory.TraceOneQuadratic
        |
        v
DkMath.Lib.NumberTheory.EisensteinCoordinates
        |
        +--> DkMath.NumberTheory.EisensteinCoordinates   [compat facade]
        |
        +--> ABC cubic Eisenstein bridges
        |
        +--> FLT3 Eisenstein Lib compatibility

DkMath.Lib.NumberTheory.UnitPowerSector
        |
        v
FLT3 cube-sector packaging at p=3
```

The ABC-GN research frontier remains unchanged:

```text
represented-pair / balanced-box sparsity
and/or
actual Eisenstein factorization existence/counting.
```

ABC remains unproved.
