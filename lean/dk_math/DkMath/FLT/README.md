# DkMath.FLT — current surfaces and research map

This README distinguishes **completed exponent-specific public results** from **active generalization research** and **legacy research routes**.

The old documentation centered on `DkMath.FLT.Main`, `FLT_d3_by_padicValNat`, and `NoSqOnS0`. Those files remain useful historical/alternate routes, but they are no longer the canonical description of the completed FLT3 result.

## 1. Completed public surface: exponent 3

Canonical import:

```lean
import DkMath.FLT.Three
```

Final endpoint:

```lean
DkMath.FLT.Three.fermatThree_no_positive_solution
```

Statement:

$$
\forall a,b,c\in\mathbb N_{>0},
\qquad
a^3+b^3\ne c^3.
$$

Primitive endpoint:

```lean
DkMath.FLT.Three.FLT_d3_unconditional
```

Proof spine:

```text
positive solution
  -> gcd normalization
  -> PrimitiveCubicPack
  -> signed 3-adic routing
  -> Eisenstein ramifier stripping
  -> conjugate-coprime factors
  -> Euclidean cube extraction
  -> unit sectors
  -> strict primitive descent
  -> strong induction
  -> contradiction
```

The public `Three` tower does not use the completed legacy conditional theorem as a proof step and does not depend on `hS0_not_sq` / `NoSqOnS0`.

Source map:

```text
Three.lean
  -> Three/PositiveCubicNormalization.lean
     -> Three/PrimitiveCubicClosure.lean
        -> Three/PrimitiveCubicDescent.lean
           -> Eisenstein / signed-three-adic tower
```

Final report:

- `../../docs/dev/FLT3-Unconditional-260904-v0/report-014.md`

Standalone exhibition project:

- <https://github.com/Deskuma/flt3_dk_math_lean4>

## 2. Completed public surface: exponent 5

Canonical import:

```lean
import DkMath.FLT.Five
```

Public endpoints:

```lean
DkMath.FLT.Five.flt5Target
DkMath.FLT.Five.fermatFive_no_positive_solution
```

Statement:

$$
\forall x,y,z\in\mathbb N_{>0},
\qquad
x^5+y^5\ne z^5.
$$

Proof spine:

```text
positive solution normalization
  -> signed gap orientation
  -> GN5 / 5-adic factor splitting
  -> golden-order arithmetic
  -> unit classes modulo fifth powers
  -> nonzero sector exclusion
  -> zero-sector inversion/factorization
  -> strict descent
  -> contradiction
```

Axiom audit entry point:

- `../../DkMathTest/FLT/Five/CheckAxioms.lean`

Standalone exhibition project:

- <https://github.com/Deskuma/flt5_dk_math_lean4>

## 3. Trust boundary for the completed endpoints

The recorded final endpoint axiom surface for both completed FLT3 and FLT5 developments is:

```text
{propext, Classical.choice, Quot.sound}
```

The corresponding audits report no `sorryAx` and no DkMath-defined axiom in the checked final endpoint.

This is a statement about Lean dependency/trust surfaces. It is not a claim of external peer review, historical priority, or community acceptance.

## 4. Current odd-prime generalization research

The current generalization line is under `DkMath.FLT.Prime.*`, not the old FLT3 `Main` route.

Current bounded closeout:

- `../../docs/refact/FLT-Prime-Generalization-260911-v0/summary-026.md`

Proved architecture:

```text
PrimeAdicFactorPacket
  -> GTail exact p-adic split
  -> arbitrary-prime QR/QNR TraceOne coordinates
  -> primitive coordinates
  -> prime-discriminant maximal order / Dedekind domain
  -> discriminant-axis strip
  -> conjugate-coprime residual ideals
  -> residual principal ideal = idealRoot^p
  -> [classGroupPTorsionFreeAt]
  -> unit * element^p
  -> unit-sector normalization
```

Important current production modules:

- `Prime/AdicPowerSplit.lean`
- `Prime/PrimeTraceOneCoordinateCoprime.lean`
- `Prime/PrimeTraceOneStrippedIdeal.lean`
- `Prime/PrimeTraceOneConditionalDescent.lean`

### Imaginary branch

For prime $p\ge7$ with

$$
p\equiv3\pmod4,
$$

the current sector machinery removes the unit-sector obstruction. Under the explicit

```lean
classGroupPTorsionFreeAt (TraceOneInt (signedPrimeParameter p)) p
```

hypothesis, the stripped residual is returned as an exact $p$-th power.

The class-group hypothesis itself remains open in the generic theorem.

### Real branch

For

$$
p\equiv1\pmod4,
$$

the conditional endpoint returns

```text
residual = rep(i) * delta^p
```

for a finite sector `i : Fin p`. Nonzero-sector elimination is not supplied by the generic theorem.

### Explicit generalization frontier

1. class-group $p$-torsion / principalization;
2. real-branch nonzero unit-sector elimination;
3. optional unification of the `p=3` Eisenstein carrier with the generic `TraceOneInt (-1)` facade.

This architecture is **not** a proof of FLT for arbitrary prime exponent.

## 5. `DkMath.Lib` connection

A major outcome of the FLT3 / FLT5 / generalization work is the migration of reusable mathematics away from owner-specific namespaces.

Examples used by the current FLT research include:

```text
DkMath.Lib.Cosmic.GTail*
DkMath.Lib.NumberTheory.PadicValNat
DkMath.Lib.NumberTheory.PowerFactor
DkMath.Lib.NumberTheory.IdealPowerFactor
DkMath.Lib.NumberTheory.PrincipalIdealPower
DkMath.Lib.NumberTheory.UnitPowerSector
DkMath.Lib.NumberTheory.TraceOneLatticeLanding
DkMath.Lib.NumberTheory.TraceOnePowerLanding
DkMath.Lib.NumberTheory.EisensteinCoordinates
DkMath.Lib.NumberTheory.EisensteinLatticeLanding
```

For generic reusable statements, prefer these promoted APIs over copying a fixed-exponent FLT lemma into another research owner.

## 6. Legacy and alternate FLT routes

The following remain in the repository but are not the canonical completed FLT3 story:

### `DkMath.FLT.Main`

Contains the older valuation / `NoSqOnS0` / `GEisensteinBridge` family, including names such as:

```text
FLT_d3_by_padicValNat
FLT_d3_by_padicValNat_of_NoSqOnS0
...
```

These are historical/alternate research APIs. Existing users may still depend on them, so this documentation refactor does not delete them.

### `DkMath.FLT.PrimeProvider.*` and `DkMath.FLT.Kummer.*`

These directories preserve earlier high-exponent provider and Kummer-style research routes. They still contain reusable ideas and bridge infrastructure, but the latest odd-prime generalization status should be read from `DkMath.FLT.Prime.*` and `summary-026.md`.

### `DkMath.FLT.Seven.*`

This is an extensive exponent-seven research tower. It is not advertised here as a completed unconditional FLT7 endpoint.

## 7. About `DkMath.FLT`

`DkMath.FLT` is a historical broad aggregator that imports several legacy and research surfaces. It is **not** the best discovery import for the completed independent FLT3 proof.

For completed exponent-specific results, prefer explicit imports:

```lean
import DkMath.FLT.Three
import DkMath.FLT.Five
```

For reusable neutral kernels, prefer:

```lean
import DkMath.Lib
```

## 8. Documentation policy

Dated work notes and old lemma-chain diagrams are preserved as historical records. When an old document describes `FLT_d3_by_padicValNat` as “the main theorem”, interpret that claim in the context of its checkpoint date.

Current global status is maintained in:

- repository `docs/PROJECT_STATUS.md`;
- this README for FLT-specific navigation;
- actual public source modules `DkMath.FLT.Three` and `DkMath.FLT.Five`.
