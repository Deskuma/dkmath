# TRM-048 実施報告

## 実施内容

- `DkMath/Tromino/PortTriangularReduction.lean` を新規作成した。
- `exists_faceStarGenusZeroTriangulation` により、`exists_portFaceStarIndexing` から indexing-free face-star triangulation と colorability reduction を構成した。
- `exists_faceStarGenusZeroTetrahedralReduction` により、face-star tetrahedral assignment から元 map colorability への existential reduction を追加した。
- `PortGenusZeroTriangularFourColorTarget` を universal proposition schema として定義した。
- `portGenusZeroFourColorTarget_imp_triangular` と `portGenusZeroTriangularFourColorTarget_imp_general` を証明した。
- `portGenusZeroTriangularFourColorTarget_iff_fourColorTarget` により、triangular four-color target と既存の general target の同値を証明した。
- `PortGenusZeroTriangularTetrahedralTarget` を universal proposition schema として定義した。
- `portGenusZeroTriangularTetrahedralTarget_iff_triangularFourColorTarget` により、triangular tetrahedral target と triangular four-color target の同値を証明した。
- `portGenusZeroTriangularTetrahedralTarget_iff_fourColorTarget` により、triangular tetrahedral target と既存の general target の同値を証明した。
- `DkMathTest/Tromino/PortTriangularReductionAxiomAudit.lean` を追加し、reduction theorem、target schema、branch-closing equivalences の `#print axioms` を監査対象にした。
- `CURRENT_STATE.md` と `ROADMAP.md` に TRM-048 の完了状態と exact remaining gap を反映した。

Universal target 自体、Four Color theorem、任意の元 coloring から face-star coloring への extension、A/B/C assignment の universal existence、Eisenstein realization は証明していない。

## 検証

- `lake build DkMath.Tromino.PortTriangularReduction`
- `lake build DkMathTest.Tromino.PortTriangularReductionAxiomAudit`
- `lake build DkMath.Tromino.PortFaceStarColorReduction DkMath.Tromino.PortFaceStarEuler DkMath.Tromino.PortTriangularTetrahedral DkMath.Tromino.PortTensionColoring`
- `git diff --check`
- production source に対する `sorry`、`admit`、`unsafe`、`axiom`、`noncomputable` の forbidden-construct scan
- `#print axioms` による `exists_faceStarGenusZeroTriangulation`、`portGenusZeroTriangularFourColorTarget_iff_fourColorTarget`、`portGenusZeroTriangularTetrahedralTarget_iff_triangularFourColorTarget`、`portGenusZeroTriangularTetrahedralTarget_iff_fourColorTarget` の依存確認

対象 build、audit、regression build、形式検査は成功した。監査された theorem の依存公理は既存基盤と同じ `propext`、`Classical.choice`、`Quot.sound` であり、新規公理は追加していない。

## Exact remaining Gap

`PortGenusZeroTriangularTetrahedralTarget`、すなわち、すべての all-triangular genus-zero Port map が tetrahedral A/B/C face assignment を持つことの universal existenceである。

Four Color theorem は未証明である。

## Outcome A

Universal triangular reduction complete。triangular four-color target と general target、triangular tetrahedral target と両 four-color target の equivalence を kernel-check し、TRM branch の reduction endpoint を確定した。
