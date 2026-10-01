# TRM-040 実施報告

## 実施内容

- `PortFaceStarIndexing` と、有限 face cell／face boundary port の明示的 indexing existence theorem を追加した。
- semantic な三分割 port carrier `FaceStarPortDesc` (`oldEdge` / `radialOld` / `radialCenter`) を追加した。
- `Fintype.card (FaceStarPortDesc M) = 3 * M.portCount` を kernel-check した。
- `faceStarNetwork` に旧領域と face-center 領域を実装し、領域数 `V + F` を確認できる API を追加した。
- 旧領域・中心領域の injectivity と相互排他を追加した。
- old-edge、old-side radial、center-side radial の actual port constructors を依存 `Fin` cast 付きで追加した。
- `PortTriangulationReduction` に carrier card／region-count の公開 theorem を追加した。
- `PortFaceStarSubdivisionAxiomAudit` に主要定義・定理の `#check` と `#print axioms` を追加した。

## 検証

- `lake build DkMath.Tromino.PortFaceStarSubdivision`
- `lake build DkMath.Tromino.PortTriangulationReduction`
- `lake build DkMathTest.Tromino.PortFaceStarSubdivisionAxiomAudit`

いずれも成功した。

## 境界

今回の実装範囲は、face-star の semantic carrier、明示的 indexing、領域／actual-port encoding までである。crossing／rotation transport、三角 face orbit、Euler／genus preservation、coloring restriction、universal target equivalence は次の実装段階に残る。
