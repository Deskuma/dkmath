# dk_math — Lean 4 mathematics library

presented by D. and Wise Wolf

## 1. このディレクトリの役割

`lean/dk_math` は DkMath の Lean 4 実装本体である。

現在の説明順序は次の通り。

1. kernel-checked まで閉じた公開成果を明確にする。
2. そこから抽出した reusable kernel を `DkMath.Lib.*` に整理する。
3. 未完の一般化・未解決問題研究は completed result と分離する。
4. 古い checkpoint 文書は研究史として保持する。

プロジェクト全体の公開概要は [root README](../../README.md)、日付つきの技術的な正本は [docs/PROJECT_STATUS.md](../../docs/PROJECT_STATUS.md) を参照。

## 2. Current stable result surfaces

### FLT3

```lean
import DkMath.FLT.Three
```

Final endpoint:

```lean
DkMath.FLT.Three.fermatThree_no_positive_solution
```

$$
\forall x,y,z\in\mathbb N_{>0},
\qquad
x^3+y^3\ne z^3.
$$

`DkMath.FLT.Three` は旧 `DkMath.FLT.Main` の conditional route から独立した public surface である。

- source: [DkMath/FLT/Three.lean](./DkMath/FLT/Three.lean)
- final report: [docs/dev/FLT3-Unconditional-260904-v0/report-014.md](./docs/dev/FLT3-Unconditional-260904-v0/report-014.md)
- standalone exhibition: <https://github.com/Deskuma/flt3_dk_math_lean4>

### FLT5

```lean
import DkMath.FLT.Five
```

Final endpoints:

```lean
DkMath.FLT.Five.flt5Target
DkMath.FLT.Five.fermatFive_no_positive_solution
```

$$
\forall x,y,z\in\mathbb N_{>0},
\qquad
x^5+y^5\ne z^5.
$$

- source: [DkMath/FLT/Five.lean](./DkMath/FLT/Five.lean)
- axiom audit: [DkMathTest/FLT/Five/CheckAxioms.lean](./DkMathTest/FLT/Five/CheckAxioms.lean)
- standalone exhibition: <https://github.com/Deskuma/flt5_dk_math_lean4>

### Infinitely many primes via Cosmic Formula boundary

The Cosmic Formula boundary route yields:

```lean
DkMath.CosmicFormula.euclid_from_cosmic_boundary
```

and the sample challenge theorem `InfinitudeOfPrimes`.

- guide: [DkMath/Samples/Prime/README.md](./DkMath/Samples/Prime/README.md)
- source: [DkMath/Samples/Prime/A.lean](./DkMath/Samples/Prime/A.lean)

## 3. `DkMath.Lib` — recommended reusable layer

For reusable neutral mathematics, prefer the promoted `DkMath.Lib.*` module that owns the theorem. For the subset already exposed by the aggregator, use:

```lean
import DkMath.Lib
```

rather than importing a large research owner module when the needed theorem has already been promoted. Some neutral `DkMath.Lib.NumberTheory.*` modules are still direct-import modules and are not yet re-exported by `DkMath.Lib.lean`.

Current aggregator:

- [DkMath/Lib.lean](./DkMath/Lib.lean)
- [DkMath/Lib/README.md](./DkMath/Lib/README.md)

Major families:

```text
DkMath.Lib.Cosmic.*
  GTail
  GTailBoundary
  GTailCongruence
  GTailCyclotomic
  GTailNat
  GTailPadic
  GTailPascal

DkMath.Lib.NumberTheory.*
  PadicValNat
  PowerFactor
  IdealPowerFactor
  PrincipalIdealPower
  UnitPowerSector
  TraceOneLatticeLanding
  TraceOnePowerLanding
  EisensteinCoordinates
  EisensteinLatticeLanding
  SquarefreePowerFactor
```

The standard GN kernel is now treated as the `r = 1` specialization of the promoted `GTail` family. New neutral code should prefer the `DkMath.Lib` APIs where they cover the required statement.

## 4. FLT directory map

See [DkMath/FLT/README.md](./DkMath/FLT/README.md) for full details.

The most important distinction is:

```text
completed exponent-specific public surfaces
  DkMath.FLT.Three
  DkMath.FLT.Five

active generalization research
  DkMath.FLT.Prime.*

legacy / alternate research surfaces
  DkMath.FLT.Main
  DkMath.FLT.PrimeProvider.*
  DkMath.FLT.Kummer.*
```

`DkMath.FLT.Seven.*` is an extensive research tower but is not listed here as a completed FLT7 endpoint.

## 5. General odd-prime FLT research

The current bounded architecture is summarized in:

[docs/refact/FLT-Prime-Generalization-260911-v0/summary-026.md](./docs/refact/FLT-Prime-Generalization-260911-v0/summary-026.md)

It reaches a residual ideal $p$-th power and conditional element-level unit-sector normalization. It does **not** complete general FLT.

Current explicit frontier:

- class-group $p$-torsion / principalization;
- nonzero real unit-sector elimination;
- optional `p=3` carrier/API unification.

## 6. Other research areas

The tree also contains active work for ABC, Goldbach, RH/CFBRC, Collatz, CF2D, Primitive Conservation, MultiGauge, gnomon structures, Legendre, and related themes.

These are research workspaces. Do not infer a completed global theorem merely from the presence of production modules or a successful checkpoint report.

## 7. Build

From `lean/dk_math`:

```bash
lake build
```

or use:

```bash
./lean-build.sh
```

Focused builds are preferred while developing a subsystem, for example:

```bash
lake build DkMath.FLT.Three
lake build DkMath.FLT.Five
lake build DkMath.Lib
```

Research modules that are intentionally outside the normal production build should be handled according to their local documentation.

## 8. Documentation policy

- [../../README.md](../../README.md): public overview.
- [../../docs/PROJECT_STATUS.md](../../docs/PROJECT_STATUS.md): authoritative dated project status.
- this file: Lean implementation and navigation.
- [DkMath/FLT/README.md](./DkMath/FLT/README.md): FLT subsystem current/legacy map.
- [DkMath/Lib/README.md](./DkMath/Lib/README.md): reusable library map.
- `docs/dev`, `docs/feature`, `docs/refact`: dated checkpoint records.

Old checkpoint documents are normally preserved as historical records rather than rewritten to match later architecture.

## 9. Snapshot used for the 2026-09-16 documentation reset

```text
1f0b8ee3dd0a9a5f829447eba7656060c1d2e19f085153a19e5040fa63f0dde7  __snapshot-dk_math-lean-code-260916-1826.tar.gz
```
