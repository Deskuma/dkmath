# TRM-046 実施報告

## 実施内容

- `DkMath/Tromino/PortFaceStarEuler.lean` を新規作成した。
- `faceStar_portCount` により、face-star port 数 `D' = 3D` を証明した。
- `faceStarOldPortToFaceCell` を定義し、old port を対応する face cell へ写した。
- `faceStarOldPortToFaceCell_val`、`faceStarTriangle_oldEdge_mem`、`faceStarTriangle_oldEdge_unique` により、old-edge triangle の所属と一意性を証明した。
- `faceStarOldPortToFaceCell_injective` と `faceStarOldPortToFaceCell_surjective` を証明し、`faceStarFaceCellEquiv` を構成した。
- `faceStar_faceCount` により、face-star face 数 `F' = D` を証明した。
- `faceStar_vertexCount` により、vertex 数 `V' = V + F` を証明した。
- `two_mul_edgeCount_eq_portCount` により `2E = D` を用意し、`faceStar_edgeCount` と `faceStar_edgeCount_eq_add_portCount` により `E' = 3E = E + D` を証明した。
- `portCombinatorialMap_eulerCharacteristic_eq` と `faceStar_eulerCharacteristic` により、Euler characteristic の保存を証明した。
- `faceStar_preserves_combinatorial_genus` と `faceStar_combinatorial_genus_iff` により、任意 genus の保存を証明した。
- `faceStarGenusZero` と count／Euler の calibration corollary 群を追加した。
- `DkMathTest/Tromino/PortFaceStarEulerAxiomAudit.lean` を追加し、指定 API、中心 theorem の `#print axioms`、triangle／dual-triangle fixture の count 回帰を監査対象にした。

## 検証

- `lake build DkMath.Tromino.PortFaceStarEuler`
- `lake build DkMathTest.Tromino.PortFaceStarEulerAxiomAudit`
- `lake build DkMath.Tromino.PortFaceStarMap DkMath.Tromino.PortTriangulationReduction DkMath.Tromino.PortEulerCount DkMath.Tromino.PortCombinatorialMap`
- triangle fixture で old `(V,E,F,D,χ) = (3,3,2,6,2)`、star `(5,9,6,18,2)` を確認した。
- dual-triangle fixture で old `(V,E,F,D,χ) = (2,3,3,6,2)`、star `(5,9,6,18,2)` を確認した。
- `git diff --check`
- production source に対する `sorry`、`admit`、`unsafe`、`axiom`、`noncomputable` の forbidden-construct scan
- 新規 production declaration の `#print axioms` 監査

対象ビルド、監査、回帰 fixture、形式検査は成功した。中心 declaration の依存公理は既存基盤と同じ `propext`、`Classical.choice`、`Quot.sound` であり、新規公理は追加していない。

## Outcome A

Face-star count identities、Euler characteristic preservation、任意 genus preservation、genus-zero wrapper を kernel-check した。
