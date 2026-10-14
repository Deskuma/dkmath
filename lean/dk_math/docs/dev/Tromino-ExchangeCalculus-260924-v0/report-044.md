# TRM-045 実施報告

## 実施内容

- `DkMath/Tromino/PortFaceStarMap.lean` を新規作成した。
- `faceStar_region_cases` により、face-star network の全 region を old region または face-center region に分類した。
- `faceStar_oldWalk_valid` と `liftFaceStarOldWalk` を追加し、old port walk の各 edge を `faceStarOldEdgePort` に写して face-star crossing 上の valid walk に lift した。
- `liftFaceStarOldWalk_edges` により、lift 後の edge list が map による像となることを確認した。
- `faceStar_oldRegion_reachable` と `faceStar_oldRegions_connected` により、元 map の connectivity を old region 間へ lift した。
- `faceStar_faceCell_nonempty` と `faceStar_faceCell_representative` を追加した。
- `faceStar_center_attachment` により、各 old face cell に対して radial-old edge で old region と face-center region を接続した。
- `faceStar_region_reaches_old` と `faceStar_regionConnected` により、任意の新 region が old region に到達し、face-star crossing が globally region-connected であることを証明した。
- `faceStar_nonemptyRegions` を追加した。
- `faceStarCombinatorialMap` を定義し、face-star crossing、rotation、nonempty region、global connectivity を `PortCombinatorialMap` にパッケージした。
- `faceStarCombinatorialMap_crossing`、`faceStarCombinatorialMap_rotation`、`faceStarCombinatorialMap_localRotation` の calibration theorem を追加した。
- `faceStarCombinatorialMap_everyFaceCell_card_three` により、packaged map の全 face cell の cardinality 3 を既存 theorem から transport した。
- `DkMathTest/Tromino/PortFaceStarMapAxiomAudit.lean` を追加し、指示書 O の API と指定 5 theorem の `#print axioms` を監査対象にした。

## 検証

- `lake build DkMath.Tromino.PortFaceStarMap`
- `lake build DkMathTest.Tromino.PortFaceStarMapAxiomAudit`
- `lake build DkMath.Tromino.PortTriangulationReduction`
- `lake build DkMath.Tromino.PortRegionWalk`
- `lake build DkMath.Tromino.PortCombinatorialMap`
- `lake build DkMath.Tromino.PortFaceOrbit`
- `git diff --check`
- production source に対する `sorry`、`admit`、`unsafe`、`axiom` の forbidden-construct scan
- `#print axioms` による `liftFaceStarOldWalk`、`faceStar_center_attachment`、`faceStar_regionConnected`、`faceStarCombinatorialMap`、`faceStarCombinatorialMap_everyFaceCell_card_three` の依存確認

対象ビルドと回帰ビルドはすべて成功した。確認された依存公理は既存基盤の `propext`、`Classical.choice`、`Quot.sound` である。

## Outcome A

Face-star connected combinatorial map complete。face-star network を connected `PortCombinatorialMap` にパッケージし、packaged map の全 face cell が cardinality 3 となることを kernel-check した。
