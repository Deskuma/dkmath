# DkMath Index

**Updated:** 2026-09-16  
**Documentation baseline:**  
commit hash: `defafa474285bab64c004b5fd98822e44a646116`

このファイルは DkMath の **現在の入口を辿るための索引** である。
定理を全件列挙する百科事典ではなく、完成成果、再利用ライブラリ、進行中研究、歴史資料を分離して「どこから読むべきか」を示す。

> [!IMPORTANT]
> 完了度・研究境界の正本は [`../../docs/PROJECT_STATUS.md`](../../docs/PROJECT_STATUS.md)。
> `docs/dev`, `docs/feature`, `docs/refact` 以下の dated documents は各 checkpoint の研究記録であり、自動的に現在状態を表すものではない。

## 0. Start here

| 目的 | 入口 |
|---|---|
| プロジェクト全体の公開概要 | [`../../README.md`](../../README.md) |
| 現在の完成成果・研究境界 | [`../../docs/PROJECT_STATUS.md`](../../docs/PROJECT_STATUS.md) |
| Lean 実装全体の入口 | [`README.md`](./README.md) |
| 再利用可能な中立 API | [`DkMath/Lib/README.md`](./DkMath/Lib/README.md) |
| FLT の現行 public surface と歴史路線 | [`DkMath/FLT/README.md`](./DkMath/FLT/README.md) |
| DkMath 全体 aggregator | [`DkMath.lean`](./DkMath.lean) |
| `DkMath.Lib.*` aggregator | [`DkMath/Lib.lean`](./DkMath/Lib.lean) |

現在の読み順は次を推奨する。

```text
completed formal results
  -> DkMath.Lib.* reusable kernels
  -> active research
  -> historical / dated research records
```

---

# I. Completed formal results

## I-1. FLT3 — exponent 3 over positive naturals

**Status:** COMPLETE

Canonical import:

```lean
import DkMath.FLT.Three
```

Public endpoints:

```lean
DkMath.FLT.Three.FLT_d3_unconditional
DkMath.FLT.Three.fermatThree_no_positive_solution
```

Main public surface:

- [`DkMath/FLT/Three.lean`](./DkMath/FLT/Three.lean)

Representative proof tower:

```text
positive solution
  -> gcd normalization
  -> PrimitiveCubicPack
  -> signed 3-adic routing
  -> Eisenstein ramifier stripping
  -> coprime conjugate factors
  -> cube extraction
  -> unit-sector exclusion
  -> exact Eisenstein cube
  -> strict descent
  -> contradiction
```

Representative modules:

- [`PositiveCubicNormalization.lean`](./DkMath/FLT/Three/PositiveCubicNormalization.lean)
- [`PrimitiveCubicLiftPacket.lean`](./DkMath/FLT/Three/PrimitiveCubicLiftPacket.lean)
- [`SignedThreeAdic.lean`](./DkMath/FLT/Three/SignedThreeAdic.lean)
- [`SignedThreeAdicPowerSplit.lean`](./DkMath/FLT/Three/SignedThreeAdicPowerSplit.lean)
- [`EisensteinEuclidean.lean`](./DkMath/FLT/Three/EisensteinEuclidean.lean)
- [`EisensteinCubeExtraction.lean`](./DkMath/FLT/Three/EisensteinCubeExtraction.lean)
- [`EisensteinSectorExclusion.lean`](./DkMath/FLT/Three/EisensteinSectorExclusion.lean)
- [`PrimitiveCubicDescent.lean`](./DkMath/FLT/Three/PrimitiveCubicDescent.lean)
- [`PrimitiveCubicClosure.lean`](./DkMath/FLT/Three/PrimitiveCubicClosure.lean)

Implementation report:

- [`docs/dev/FLT3-Unconditional-260904-v0/report-014.md`](./docs/dev/FLT3-Unconditional-260904-v0/report-014.md)

Standalone exhibition project:

- <https://github.com/Deskuma/flt3_dk_math_lean4>

The completed tower is independent of the legacy conditional `DkMath.FLT.Main` / `FLT_d3_by_padicValNat` / `NoSqOnS0` route.

## I-2. FLT5 — exponent 5 over positive naturals

**Status:** COMPLETE

Canonical import:

```lean
import DkMath.FLT.Five
```

Public endpoints:

```lean
DkMath.FLT.Five.flt5Target
DkMath.FLT.Five.fermatFive_no_positive_solution
```

Main public surface:

- [`DkMath/FLT/Five.lean`](./DkMath/FLT/Five.lean)
- [`DkMath/FLT/Five/Main.lean`](./DkMath/FLT/Five/Main.lean)

Representative proof route:

```text
positive solution normalization
  -> signed gap orientation
  -> GN5 / five-adic factor splitting
  -> golden-order factorization
  -> unit classes modulo fifth powers
  -> nonzero-sector exclusion
  -> zero-sector strict descent
  -> contradiction
```

Axiom audit entry point:

- [`DkMathTest/FLT/Five/CheckAxioms.lean`](./DkMathTest/FLT/Five/CheckAxioms.lean)

Standalone exhibition project:

- <https://github.com/Deskuma/flt5_dk_math_lean4>

The OpenAI Build Week GN5 work is the historical origin of this route. The reusable mathematics extracted from that line now belongs primarily under `DkMath.Lib.*`.

## I-3. Infinitely many primes from the Cosmic Formula boundary

**Status:** COMPLETE proof route

Core boundary identities:

$$
\text{cosmicN}(P)=P(P+2),
$$

$$
\text{cosmicN}(P)+1=(P+1)^2.
$$

Main route:

```lean
DkMath.CosmicFormula.euclid_from_cosmic_boundary
```

Comparator sample endpoint:

```lean
InfinitudeOfPrimes
```

Read:

- [`DkMath/Samples/Prime/A.lean`](./DkMath/Samples/Prime/A.lean)
- [`DkMath/Samples/Prime/README.md`](./DkMath/Samples/Prime/README.md)
- [`DkMath/Samples/Prime/Lean4Web.md`](./DkMath/Samples/Prime/Lean4Web.md)

---

# II. Reusable library — `DkMath.Lib.*`

## II-1. Public development aggregator

Recommended lightweight import for the currently exported reusable subset:

```lean
import DkMath.Lib
```

[`DkMath/Lib.lean`](./DkMath/Lib.lean) currently imports:

```text
DkMath.Lib.Basic
DkMath.Lib.TwoChannel
DkMath.Lib.NumberTheory.PadicValNat
DkMath.Lib.NumberTheory.TraceOneLatticeLanding
DkMath.Lib.NumberTheory.TraceOnePowerLanding
DkMath.Lib.NumberTheory.EisensteinCoordinates
DkMath.Lib.NumberTheory.EisensteinLatticeLanding
DkMath.Lib.NumberTheory.SquarefreePowerFactor
DkMath.Lib.Cosmic.GTail
DkMath.Lib.Cosmic.GTailCyclotomic
DkMath.Lib.Cosmic.GTailPascal
DkMath.Lib.Cosmic.GTailBoundary
DkMath.Lib.Cosmic.GTailNat
DkMath.Lib.Cosmic.GTailCongruence
DkMath.Lib.Cosmic.GTailPadic
```

Full guide:

- [`DkMath/Lib/README.md`](./DkMath/Lib/README.md)

## II-2. Cosmic / GTail family

`GTail` is the neutral binomial-tail kernel behind the standard GN layer.

For general depth $r$:

$$
(x+u)^d
=
\sum_{j<r}\binom dj x^j u^{d-j}
+x^r\text{GTail}(d,r,x,u).
$$

The standard GN layer is the specialization

$$
GN_d(x,u)=\text{GTail}(d,1,x,u).
$$

Modules:

- [`GTail.lean`](./DkMath/Lib/Cosmic/GTail.lean) — core decomposition / recursion
- [`GTailBoundary.lean`](./DkMath/Lib/Cosmic/GTailBoundary.lean) — exact gcd boundary formulas
- [`GTailCongruence.lean`](./DkMath/Lib/Cosmic/GTailCongruence.lean) — congruence transport / head collapse
- [`GTailCyclotomic.lean`](./DkMath/Lib/Cosmic/GTailCyclotomic.lean) — cyclotomic shell bridge
- [`GTailNat.lean`](./DkMath/Lib/Cosmic/GTailNat.lean) — natural-number divisibility
- [`GTailPadic.lean`](./DkMath/Lib/Cosmic/GTailPadic.lean) — exact p-adic consequences
- [`GTailPascal.lean`](./DkMath/Lib/Cosmic/GTailPascal.lean) — finite-depth Pascal filtration

The old degree-specific GN5 story is therefore no longer the right library-level abstraction. New neutral code should prefer the `GTail` family when the statement is not intrinsically degree-specific.

## II-3. Number-theory promoted modules

Aggregator-exposed modules:

- [`PadicValNat.lean`](./DkMath/Lib/NumberTheory/PadicValNat.lean)
- [`TraceOneLatticeLanding.lean`](./DkMath/Lib/NumberTheory/TraceOneLatticeLanding.lean)
- [`TraceOnePowerLanding.lean`](./DkMath/Lib/NumberTheory/TraceOnePowerLanding.lean)
- [`EisensteinCoordinates.lean`](./DkMath/Lib/NumberTheory/EisensteinCoordinates.lean)
- [`EisensteinLatticeLanding.lean`](./DkMath/Lib/NumberTheory/EisensteinLatticeLanding.lean)
- [`SquarefreePowerFactor.lean`](./DkMath/Lib/NumberTheory/SquarefreePowerFactor.lean)

Neutral direct-import modules that exist in `DkMath.Lib.NumberTheory` but are not re-exported by `DkMath.Lib.lean` in this snapshot:

- [`PowerFactor.lean`](./DkMath/Lib/NumberTheory/PowerFactor.lean)
- [`IdealPowerFactor.lean`](./DkMath/Lib/NumberTheory/IdealPowerFactor.lean)
- [`PrincipalIdealPower.lean`](./DkMath/Lib/NumberTheory/PrincipalIdealPower.lean)
- [`UnitPowerSector.lean`](./DkMath/Lib/NumberTheory/UnitPowerSector.lean)

This distinction is only about aggregator coverage; all four are intended as reusable neutral APIs.

---

# III. Full workspace entry point

## III-1. `DkMath.lean`

[`DkMath.lean`](./DkMath.lean) is the broad workspace aggregator.

```lean
import DkMath
```

imports not only stable/reusable layers but also active research facades and hackathon material. Use `import DkMath.Lib`, `import DkMath.FLT.Three`, or `import DkMath.FLT.Five` when a narrower dependency surface is desired.

Major families currently imported by `DkMath.lean` include:

### Foundation / reusable infrastructure

- `DkMath.Basic`
- `DkMath.Lib`
- `DkMath.Algebra.MetallicRatioCore`
- `DkMath.Verification`
- `DkMath.Samples`
- `DkMath.Sequence`
- `DkMath.Kernel`
- `DkMath.Analysis`

### Number theory / combinatorics

- `DkMath.NumberTheory.PowerSums`
- `DkMath.NumberTheory.BinomialPrime`
- `DkMath.NumberTheory.BinomialPrimePower`
- `DkMath.NumberTheory.PascalPrimeDial`
- `DkMath.NumberTheory.PascalPrimeCoordinateDecoder`
- `DkMath.NumberTheory.Primitive`
- `DkMath.NumberTheory.PrimorialUniverse`
- `DkMath.NumberTheory.Legendre`
- `DkMath.NumberTheory.AKSBridge`
- `DkMath.NumberTheory.WeightedBinomial`
- `DkMath.NumberTheory.WeightedGNBridge`
- `DkMath.NumberTheory.GNPrime`
- `DkMath.NumberTheory.Goldbach`
- `DkMath.Pascal`
- `DkMath.Petal`

### Geometry / structural arithmetic

- `DkMath.CosmicFormula`
- `DkMath.EuclideanGeometry`
- `DkMath.PowerSwap`
- `DkMath.Polyomino`
- `DkMath.PolyominoPrototype`
- `DkMath.Tromino`
- `DkMath.SilverRatio`
- `DkMath.UniqueRepSimple`
- `DkMath.UniqueRepresentation`
- `DkMath.UnitCycle`

### Research-owner facades

- `DkMath.ABC`
- `DkMath.Collatz.Collatz2K26`
- `DkMath.DHNT`
- `DkMath.KUS`
- `DkMath.RH`
- `DkMath.FLT`
- `DkMath.CFBRC`
- `DkMath.BookOfMagic`
- `DkMath.Zsigmondy`

### Hackathon entries imported by the broad workspace

- `DkMath.Hackathon.FinitePrimeEscapeGN5`
- `DkMath.Hackathon.JacobianCounterexample3`

---

# IV. FLT map

## IV-1. Completed exponent-specific surfaces

| Exponent | Canonical import | Public endpoint | Status |
|---:|---|---|---|
| $3$ | `DkMath.FLT.Three` | `fermatThree_no_positive_solution` | COMPLETE |
| $5$ | `DkMath.FLT.Five` | `fermatFive_no_positive_solution` | COMPLETE |

These are the two completed public FLT results that should be presented first.

## IV-2. General odd-prime research

**Status:** ACTIVE / INCOMPLETE

Current prime-generalization modules:

- [`AdicPowerSplit.lean`](./DkMath/FLT/Prime/AdicPowerSplit.lean)
- [`PrimeTraceOneCoordinateCoprime.lean`](./DkMath/FLT/Prime/PrimeTraceOneCoordinateCoprime.lean)
- [`PrimeTraceOneStrippedIdeal.lean`](./DkMath/FLT/Prime/PrimeTraceOneStrippedIdeal.lean)
- [`PrimeTraceOneConditionalDescent.lean`](./DkMath/FLT/Prime/PrimeTraceOneConditionalDescent.lean)

Latest bounded architecture:

```text
odd-prime factor packet
  -> exact p-adic split
  -> QR/QNR TraceOne coordinate
  -> primitive coordinates
  -> prime-discriminant / conjugate-coprime strip
  -> residual principal ideal = I^p
  -> class-group p-torsion condition
  -> residual = unit * gamma^p
  -> unit-sector normalization
  -> final FLT contradiction still open in general
```

Current detailed checkpoint:

- [`docs/refact/FLT-Prime-Generalization-260911-v0/summary-026.md`](./docs/refact/FLT-Prime-Generalization-260911-v0/summary-026.md)

Important supporting neutral / number-theory modules include:

- [`CyclotomicQRTraceOneBridge.lean`](./DkMath/NumberTheory/CyclotomicQRTraceOneBridge.lean)
- [`CyclotomicQRUniversalTransport.lean`](./DkMath/NumberTheory/CyclotomicQRUniversalTransport.lean)
- [`TraceOnePrimeDiscriminant.lean`](./DkMath/NumberTheory/TraceOnePrimeDiscriminant.lean)
- [`TraceOneConjugateCoprime.lean`](./DkMath/NumberTheory/TraceOneConjugateCoprime.lean)
- [`TraceOneIdealPower.lean`](./DkMath/NumberTheory/TraceOneIdealPower.lean)
- [`TraceOnePrimeUnitSectors.lean`](./DkMath/NumberTheory/TraceOnePrimeUnitSectors.lean)

## IV-3. FLT7 research tower

[`DkMath.FLT.Seven`](./DkMath/FLT/Seven.lean) and [`DkMath/FLT/Seven/`](./DkMath/FLT/Seven/) contain a large exponent-seven research tower used to explore routing, quadratic/real-cubic/cyclotomic carriers, ramified fusion, prime-power cells, and descent boundaries.

It is **not** indexed here as a completed unconditional FLT7 endpoint. For current generalization status, use the prime-generalization summary above.

## IV-4. Historical / alternate FLT surfaces

These remain valuable research records and bridge layers, but they are not the canonical completed FLT3 story:

- [`DkMath/FLT/Main.lean`](./DkMath/FLT/Main.lean)
- [`DkMath/FLT/PhaseLift.lean`](./DkMath/FLT/PhaseLift.lean)
- [`DkMath/FLT/CounterexamplePattern.lean`](./DkMath/FLT/CounterexamplePattern.lean)
- [`DkMath/FLT/GEisensteinBridge.lean`](./DkMath/FLT/GEisensteinBridge.lean)
- [`DkMath/FLT/PrimeProvider.lean`](./DkMath/FLT/PrimeProvider.lean)
- [`DkMath/FLT/Kummer.lean`](./DkMath/FLT/Kummer.lean)
- [`DkMath/FLT/TriominoMainBridge.lean`](./DkMath/FLT/TriominoMainBridge.lean)
- [`DkMath/FLT/TriominoPrimeProvider.lean`](./DkMath/FLT/TriominoPrimeProvider.lean)

Use [`DkMath/FLT/README.md`](./DkMath/FLT/README.md) for the current classification of these routes.

---

# V. Active research map

This section is a navigation map, not a completion claim.

## V-1. ABC / GN excess / balance calibration

Facade:

- [`DkMath/ABC.lean`](./DkMath/ABC.lean)

Current families include:

- GN exceptional excess and depth pressure
- realizable / realized profile and moment layers
- cubic complement / Pell / incidence machinery
- Eisenstein coordinate and square-factor providers
- balance / calibration / depth-transport layers

Recent calibration entries:

- [`GNBalanceCalibration.lean`](./DkMath/ABC/GNBalanceCalibration.lean)
- [`ABCBalanceCalibrationBridge.lean`](./DkMath/ABC/ABCBalanceCalibrationBridge.lean)
- [`ABCCalibrationSourceDecomposition.lean`](./DkMath/ABC/ABCCalibrationSourceDecomposition.lean)

The facade itself still describes the ABC development as experimental / unproven research. Do not interpret its importability as a completed ABC theorem.

## V-2. Goldbach fixed-center GN fibers

Facade:

- [`DkMath/NumberTheory/Goldbach.lean`](./DkMath/NumberTheory/Goldbach.lean)

The current facade exports exact finite reformulations, obstruction search, capacity/accounting identities, CRT overlap layers, and conditional endpoints. It explicitly does **not** provide an unconditional Strong Goldbach provider.

Representative subareas:

```text
Basic / Obstruction / PrimeWorld
Cardinality / Capacity / Conservation
Overlap / PairOverlap
CrossGapExchange / CrossGapEscape
BalancedCRT* / BalancedSignedCRT*
```

## V-3. Primitive / primorial / Legendre line

Primary entries:

- [`DkMath/NumberTheory/Primitive.lean`](./DkMath/NumberTheory/Primitive.lean)
- [`DkMath/NumberTheory/PrimorialUniverse.lean`](./DkMath/NumberTheory/PrimorialUniverse.lean)
- [`DkMath/NumberTheory/Legendre.lean`](./DkMath/NumberTheory/Legendre.lean)

Related primitive-conservation work is used as infrastructure for prime-scale and finite-support research.

## V-4. Pascal / prime rows / AKS-facing bridges

Entries:

- [`DkMath/Pascal.lean`](./DkMath/Pascal.lean)
- [`BinomialPrime.lean`](./DkMath/NumberTheory/BinomialPrime.lean)
- [`BinomialPrimePower.lean`](./DkMath/NumberTheory/BinomialPrimePower.lean)
- [`PascalPrimeDial.lean`](./DkMath/NumberTheory/PascalPrimeDial.lean)
- [`PascalPrimeCoordinateDecoder.lean`](./DkMath/NumberTheory/PascalPrimeCoordinateDecoder.lean)
- [`AKSBridge.lean`](./DkMath/NumberTheory/AKSBridge.lean)
- [`WeightedBinomial.lean`](./DkMath/NumberTheory/WeightedBinomial.lean)
- [`WeightedGNBridge.lean`](./DkMath/NumberTheory/WeightedGNBridge.lean)

## V-5. GN prime arithmetic / Hensel depth

Facade:

- [`DkMath/NumberTheory/GNPrime.lean`](./DkMath/NumberTheory/GNPrime.lean)

Related modules include prime closure, representations, target residues, cubic orientation, paired depth, finite Hensel lifting/depth, and Wieferich structure.

## V-6. CF2D / Euclidean geometry

Public aggregate:

- [`DkMath/EuclideanGeometry.lean`](./DkMath/EuclideanGeometry.lean)

It aggregates stable v0 layers for:

- unit-kernel powers
- normalized cycle division
- exact finite CF2D regular orbits
- oriented Euclidean interpretation
- Fermat-form predicates
- quadratic-expression constructibility bridges

The module explicitly does **not** claim a complete Gauss-Wantzel theorem.

## V-7. Other research-owner facades

- [`DkMath/RH.lean`](./DkMath/RH.lean) — RH-related observer / bridge research
- [`DkMath/CFBRC.lean`](./DkMath/CFBRC.lean) — Cosmic Formula Binomial Real Complex bridge layer
- [`DkMath/Collatz/Collatz2K26.lean`](./DkMath/Collatz/Collatz2K26.lean) — accelerated Collatz cartography
- [`DkMath/DHNT.lean`](./DkMath/DHNT.lean) — Dynamic Harmonic Number Theory
- [`DkMath/KUS.lean`](./DkMath/KUS.lean) — coefficient / unit / blueprint kernel
- [`DkMath/BookOfMagic.lean`](./DkMath/BookOfMagic.lean) — dependent Core-Gap API
- [`DkMath/PowerSwap.lean`](./DkMath/PowerSwap.lean) — power-swapping relations
- [`DkMath/UnitCycle.lean`](./DkMath/UnitCycle.lean) — unit-cycle structures

---

# VI. Hackathon and verification projects

## VI-1. GN5 / Cosmic Formula inversion

- [`DkMath/Hackathon/FinitePrimeEscapeGN5.lean`](./DkMath/Hackathon/FinitePrimeEscapeGN5.lean)
- [`docs/hackathon/cosmic-formula-inversion-260715/README.md`](./docs/hackathon/cosmic-formula-inversion-260715/README.md)

This line is historically important as the GN5 experiment that developed into the completed FLT5 formalization and helped expose reusable kernels later promoted to `DkMath.Lib.*`.

## VI-2. Breaking Math Verification / Jacobian certificate

- [`DkMath/Hackathon/JacobianCounterexample3.lean`](./DkMath/Hackathon/JacobianCounterexample3.lean)
- [`DkMath/Verification.lean`](./DkMath/Verification.lean)
- [`docs/hackathon/jacobian-counterexample-verification-260721/README.md`](./docs/hackathon/jacobian-counterexample-verification-260721/README.md)

The verification layer is reusable independently of the case study.

---

# VII. Documentation and research records

## VII-1. Current documents

These documents are intended to describe the current public structure:

- [`../../README.md`](../../README.md)
- [`../../docs/PROJECT_STATUS.md`](../../docs/PROJECT_STATUS.md)
- [`README.md`](./README.md)
- [`INDEX.md`](./INDEX.md)
- [`DkMath/Lib/README.md`](./DkMath/Lib/README.md)
- [`DkMath/FLT/README.md`](./DkMath/FLT/README.md)

## VII-2. Dated research records

The following trees preserve checkpoint history:

```text
docs/dev/
docs/feature/
docs/refact/
docs/hackathon/
```

Do not rewrite old checkpoint documents merely because the current architecture changed. When an old route can be mistaken for the current public route, add a historical-status note or link back to the current documents instead.

Current documentation-refactor record:

- [`docs/refact/documentation-current-state-260916-v0/README.md`](./docs/refact/documentation-current-state-260916-v0/README.md)

---

# VIII. Build / audit quick paths

Focused public builds:

```sh
lake build DkMath.Lib
lake build DkMath.FLT.Three
lake build DkMath.FLT.Five
```

Broad workspace build:

```sh
lake build DkMath
```

FLT5 axiom audit source:

```text
DkMathTest/FLT/Five/CheckAxioms.lean
```

FLT3 completion report and endpoint axiom audit:

```text
docs/dev/FLT3-Unconditional-260904-v0/report-014.md
```

---

# IX. Maintenance policy for this index

`INDEX.md` should remain a **navigation map**, not a manually maintained list of every theorem.

When the repository changes:

1. add a new section here only when a new public facade, completed result, or durable research family appears;
2. keep exact theorem inventories in module docs / generated API docs rather than duplicating them here;
3. use [`../../docs/PROJECT_STATUS.md`](../../docs/PROJECT_STATUS.md) for dated status claims;
4. keep `DkMath.Lib.lean` aggregator coverage distinct from all physical modules under `DkMath.Lib.*`;
5. never promote a conditional or research endpoint to `COMPLETE` merely because the module builds;
6. preserve historical documents as checkpoint records instead of silently rewriting their mathematics.

The intended long-term shape is:

```text
DkMath
  ├─ completed formal results
  │    ├─ FLT3
  │    ├─ FLT5
  │    └─ prime infinitude via Cosmic Formula boundary
  ├─ DkMath.Lib.*
  │    ├─ GTail / GN neutral kernels
  │    ├─ p-adic / divisibility
  │    ├─ TraceOne / Eisenstein lattice landing
  │    └─ power / ideal / unit-sector factorization
  ├─ active research
  │    ├─ general odd-prime FLT
  │    ├─ ABC
  │    ├─ Goldbach
  │    ├─ primitive / Legendre / prime geometry
  │    └─ CF2D / RH / Collatz / other owners
  └─ dated historical research records
```
