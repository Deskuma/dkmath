# TRM-047 実施報告

## 実施内容

- `DkMath/Tromino/PortFaceStarColorReduction.lean` を新規作成した。
- `faceStar_allFacesTriangular` と `faceStarGenusZero_allFacesTriangular` により、packaged face-star map と genus-zero wrapper が全 face triangular であることを既存の face-cell cardinality theorem から証明した。
- `faceStar_oldEdge_source` と `faceStar_oldEdge_target` により、old-edge port の source／target を `oldRegion` へ calibration した。
- `faceStarOldRegionEmbedding` と injectivity theorem を追加した。
- `faceStar_oldAdjacency_of_port` と `faceStar_oldAdjacency` により、元 map の adjacency を old-region adjacency へ埋め込んだ。
- `faceStarRestrictColoring` を定義し、face-star SimpleGraph coloring を old-region へ pullback した。
- `faceStarRestrictColoring_apply` と edge distinction corollary を追加した。
- `faceStar_colorable_imp_original` と `faceStarGenusZero_colorable_imp_original` により、face-star colorability から元 map の colorability への一方向 reduction を証明した。
- `faceStar_tetrahedral_iff_colorable` により、genus-zero face-star map 上の tetrahedral assignment と four-state colorability の局所同値を証明した。
- `faceStar_tetrahedral_imp_original_colorable` により、face-star tetrahedral assignment から元 map の colorability を導出した。
- `DkMathTest/Tromino/PortFaceStarColorReductionAxiomAudit.lean` を追加し、指定 API と中心 theorem の `#print axioms` を監査対象にした。

face-star coloring の元 map から face-star map への逆向き extension、universal target、Four Color theorem の存在主張、Eisenstein realization は導入していない。

## 検証

- `lake build DkMath.Tromino.PortFaceStarColorReduction`
- `lake build DkMathTest.Tromino.PortFaceStarColorReductionAxiomAudit`
- `lake build DkMath.Tromino.PortFaceStarEuler DkMath.Tromino.PortTriangularTetrahedral DkMath.Tromino.PortTensionColoring DkMath.Tromino.PortFaceStarMap`
- `git diff --check`
- production source に対する `sorry`、`admit`、`unsafe`、`axiom`、`noncomputable` の forbidden-construct scan
- `#print axioms` による `faceStar_allFacesTriangular`、`faceStar_oldAdjacency`、`faceStarRestrictColoring`、`faceStar_colorable_imp_original`、`faceStar_tetrahedral_imp_original_colorable` の依存確認

対象ビルド、監査、回帰ビルド、形式検査は成功した。中心 theorem の依存公理は既存基盤と同じ `propext`、`Classical.choice`、`Quot.sound` であり、新規公理は追加していない。

## Outcome A

Packaged triangular coloring restriction complete。packaged face-star map の all-triangular 性、old-region adjacency embedding、coloring pullback、face-star tetrahedral assignment から元 map colorability への一方向 reduction を kernel-check した。
