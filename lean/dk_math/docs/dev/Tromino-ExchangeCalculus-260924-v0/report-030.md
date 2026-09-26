# TRM-031 — V4 Tension / Proper Four-State Coloring Equivalence

## 実装内容

`DkMath.Tromino.PortTensionColoring` を追加し、強連結な Port combinatorial map に対する V4 の zero-holonomy tension と proper TrominoState coloring の対応を実装した。

- Port region graph の crossing witness による隣接関係、SimpleGraph 化、looplessness、Flow graph との calibration を追加した。
- 既存の `V4FlowAssignment` を用いて、Port graph の assignment と Flow lifted assignment の graph を一致させる定理を追加した。
- `PortFourStateColorable` と `Colorable 4` の接続を追加した。
- proper coloring から `K(source) + K(target)` による nowhere-zero V4 assignment と RegionPotential を構成した。
- zero-holonomy assignment から RegionPotential、さらに base region を 0 とする Port coloring を再構成した。
- assignment のラベルから coloring への exact round-trip と、強連結 map 上の主同値
  `HasZeroHolonomyV4Tension C ↔ PortFourStateColorable C`
  を追加した。
- genus-zero wrapper は一般の同値を再利用する specialization として追加した。genus witness は主証明の前提に使用していない。

## Fixtures と audit

`DkMathTest.Tromino.PortTensionColoringAxiomAudit` に次を固定した。

- 2×2 fixture の明示的な 0 / `deltaA` coloring、deltaA assignment、zero holonomy、label round-trip、主同値。
- 2×3 genus-1 fixture の明示 coloring と map ごとの主同値。
- Port/Flow graph calibration、PortFourStateColorable、`Colorable 4`、crossing preservation。
- genus-zero specialization と universal target proposition の iff。
- production declarations の `#print axioms` audit。

## 境界

ここで扱った zero-holonomy は、assignment が coboundary（exact 1-cochain）であるという tension 条件であり、歴史的な `V4FlowAssignment` という名前から Kirchhoff 型の流量保存を意味するものではない。今回の実装は、genus-zero の存在、planarity、sphere realization、Four Color theorem、dual-flow theory、または全ての map に対する universal existence を証明しない。universal target proposition についても target 間の同値のみを追加した。

Mathlib の既成 tension/flow API に依存せず、既存の `SimpleGraph.Coloring`、`RegionPotential`、Port/Flow reachability API を組み合わせている。

## 検証

次の production / audit build が成功した。

```text
lake build DkMath.Tromino.PortTensionColoring \
  DkMathTest.Tromino.PortTensionColoringAxiomAudit
Build completed successfully (1559 jobs).
```

既存 API の回帰 build も成功した。

```text
lake build DkMath.Tromino.PortCombinatorialMap \
  DkMathTest.Tromino.PortCombinatorialMapAxiomAudit \
  DkMath.Tromino.RegionPotential \
  DkMathTest.Tromino.RegionPotentialAxiomAudit \
  DkMath.Tromino.GraphColoringBridge \
  DkMathTest.Tromino.GraphColoringBridgeAxiomAudit
Build completed successfully (1557 jobs).
```

既存依存由来の warning は残るが、対象 build に error はない。指示された境界に従い、ここで停止する。
