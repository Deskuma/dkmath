# NumberGeometry-TwoPointGauge NGEO-004 実装報告

## 1. 結果

Outcome A。point-centered square-mass level set と shared-point transport を実装し、similarity による level-set image と intersection の自然性を Lean で検証した。

`MassLevelSet` は円や sphere を primitive にせず、square mass の等値集合として定義している。SilverRatio 固有座標、radical landing、prime scale、UnitCycle、logarithm、2p phase、cyclotomic theory、FLT は実装していない。

## 2. 変更ファイル

- `DkMath/NumberGeometry/LevelSet.lean`
  - level set、shell bridge、similarity image、SharedPoint、intersection transport を追加。
- `DkMath/NumberGeometry.lean`
  - `DkMath.NumberGeometry.LevelSet` を公開 facade から import。
- `DkMathTest/NumberGeometry/LevelSetAxiomAudit.lean`
  - 新規公開 API の `#check` と主要定理の `#print axioms` を追加。
- `docs/dev/NumberGeometry-TwoPointGauge-260924-v0/report-004.md`
  - 本報告。

`Basic.lean`、`Gauge.lean`、`Transport.lean` は今回変更していない。

## 3. MassLevelSet

```lean
def MassLevelSet (A : Point) (rho : ℝ) : Set Point :=
  {P | pairMass A P = rho}
```

`rho` は radius ではなく square mass parameter として扱っている。次を追加した。

- `mem_massLevelSet`
- `massLevelSet_zero`

`massLevelSet_zero` は `MassLevelSet A 0 = {A}` を `pairMass_eq_zero_iff` から証明している。負 level の emptiness や、一般の非負 level の存在性は追加していない。

## 4. Natural shell bridge

`onNatShell_iff_mem_massLevelSet` を追加した。

```text
OnNatShell K n P
  ↔ P ∈ MassLevelSet K.source ((n : ℝ) * massGauge K)
```

既存の `OnNatShell` を再定義せず、mass level の語彙へ接続している。

## 5. Similarity transport

任意の real scale `c` に対して次を追加した。

- `mem_massLevelSet_similarity`
- `image_massLevelSet_similarity_subset`

したがって `c = 0` でも forward transport は成立する。

また、`c ≠ 0` の場合に次を追加した。

- `similarityMap_injective`
- `similarityMap_surjective`
- `mem_massLevelSet_similarity_iff`
- `image_massLevelSet_similarity`

特に exact image equality は次の仮定で成立する。

```text
similarityMap t c R '' MassLevelSet A rho
  = MassLevelSet (similarityMap t c R A) (c ^ 2 * rho)
```

zero scale ではこの equality を主張していない。`c = 0` では target level が zero level の singleton になる一方、source level が空であり得るため、一般の image equality は自動的には成立しない。今回は arbitrary scale の forward inclusion と、nonzero scale の exact equality を分離した。

## 6. SharedPoint

次の最小 predicate を追加した。

```lean
def SharedPoint (S U : Set Point) (P : Point) : Prop :=
  P ∈ S ∧ P ∈ U
```

あわせて以下を追加した。

- `sharedPoint_iff_mem_inter`
- `sharedPoint_massLevelSet_similarity`

後者は `c = 0` を含む全スケールで、二つの mass constraints の共通点を同時に transport する forward theorem である。交点の存在・一意性・算術 landing は主張していない。

## 7. Intersection naturality

`image_inter_similarity` を追加した。

```text
similarityMap t c R '' (S ∩ U)
  = (similarityMap t c R '' S) ∩
    (similarityMap t c R '' U)
```

これは `c ≠ 0` を仮定し、`Set.image_inter` と `similarityMap_injective` を再利用している。set-level intersection の一般 theorem を重複実装していない。

## 8. 検証

以下はすべて成功した。

```text
lake build DkMath.NumberGeometry.LevelSet
Build completed successfully (2425 jobs)

lake build DkMath.NumberGeometry
Build completed successfully (2426 jobs)

lake build DkMathTest.NumberGeometry.LevelSetAxiomAudit
Build completed successfully (2427 jobs)

lake build DkMath
Build completed successfully (10276 jobs)
```

新規 substantive theorem の `#print axioms` はすべて次の既存 logical infrastructure のみだった。

```text
[propext, Classical.choice, Quot.sound]
```

`sorry`、`admit`、`sorryAx`、`unsafe`、新規 `axiom` は使用していない。新規 production/test/report ファイルを含む空白検査も成功した。

## 9. Deferred scope

positive mass level と metric sphere の `sqrt rho` bridge は追加していない。circle interpretation は数学的な読み替えに留め、`Metric.sphere` を production primitive にしていない。

SilverRatio の `concyclic4` への bridge、共有点の存在性・一意性、共有点の integer/radical-integer normalized mass は後続の calibration/bridge checkpoint に延期した。

ここで NGEO-004 を終了し、NGEO-005 の radical decomposition には進まない。
