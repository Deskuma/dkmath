# TRM-044 実施報告

## 実施内容

- `PortTriangulationReduction.lean` に旧領域・face-center 領域の actual-port 分類定理を追加した。
  - `faceStar_port_at_oldRegion_cases`
  - `faceStar_port_at_centerRegion_cases`
- 旧領域では、TRM-043 の exact rotation formula を基礎に、radial-old 起点の偶数・奇数 iterate と old-edge 起点の対応する iterate を帰納的に証明した。
- `oldFace_backward_reachable` を追加し、旧 face cell 内の `portFaceEquiv.symm` による backward reachability を face-orbit の iterate reachability から導出した。
- `faceStar_oldRegion_cyclic` と `faceStar_centerRegion_cyclic` を追加し、領域ごとの回転 cyclicity を証明した。
- `faceStarRotationSystem` を定義し、face-star network の local rotation と cyclicity を `PortRotationSystem` にパッケージした。
- `faceStarFaceStep_oldEdge`、`faceStarFaceStep_radialOld`、`faceStarFaceStep_radialCenter` により、crossing と local rotation の合成による exact 3-step face cycle を証明した。
- old-edge、radial-old、radial-center の各 canonical member について、3-step return、1-step/2-step no-return、`firstPortFaceReturn = 3` を証明した。
- `faceStarTriangle` とその card theorem を追加し、canonical triangle が old-edge、radial-old、radial-center の 3 ports からなることを証明した。
- canonical triangle が old-edge、radial-old、radial-center のいずれを起点としても同じ `portFaceOrbit` になることを証明した。
- `faceStarTriangle_coverage` により、すべての actual port がいずれかの canonical triangle に含まれることを証明した。
- `faceStar_everyFaceCell_card_three` により、face-star rotation/crossing pair のすべての `PortFaceCell` が cardinality 3 であることを証明した。
- `DkMathTest/Tromino/PortFaceStarTriangularAxiomAudit.lean` を追加し、指示書 R の 18 項目と主要 5 theorem の `#print axioms` を監査対象にした。

## 検証

- `lake build DkMath.Tromino.PortTriangulationReduction`
- `lake build DkMathTest.Tromino.PortFaceStarTriangularAxiomAudit`
- `lake build DkMath.Tromino.PortFaceStarSubdivision`
- `lake build DkMath.Tromino.PortRotationSystem`
- `lake build DkMath.Tromino.PortFaceOrbit`
- `lake build DkMath.Tromino.PortCombinatorialMap`
- `git diff --check`
- 新規監査ファイルに対する whitespace check
- production source に対する `sorry`、`admit`、`unsafe`、`axiom` の forbidden-construct scan
- 主要 theorem の `#print axioms` を確認した。依存は `propext`、`Classical.choice`、`Quot.sound` の既存基盤に限られ、新規 axiom はない。

上記の対象ビルドおよび回帰ビルドはすべて成功した。

## Outcome A

Face-star rotation/triangular dynamics complete。face-star local rotation を `PortRotationSystem` に昇格し、生成された全 face cell が kernel-check 済みで cardinality 3 となるところまで完了した。
