# TRM-039 実装報告

## 実装

`DkMath/Tromino/TetrahedralClosure.lean` を追加し、TRM-038 の `TrominoState` をそのまま四面体局所 carrier として形式化した。

- `TetraFace := TrominoState`、canonical face color、4 face theorem
- 2-element Finset による `TetraEdge`、6 edge theorem
- edge delta、nonzero theorem、`{deltaA, deltaB, deltaC}` image theorem
- 3 delta fiber の各 cardinality 2、partition、同一 delta の opposite-edge disjointness
- 固定 face からの 3 nonzero direction、他の 3 face への equivalence と image theorem
- incident edge cardinality 3 と incident delta image
- color-level `tetraRollBottom`、double roll、12 color-level roll steps
- roll edge delta と reverse calibration
- 3 nonzero V4 labels の zero-sum / pairwise-distinct / exact `{A,B,C}` equivalence
- list rolling formula、append composition、zero-XOR return

`DkMath/Tromino/PortTriangularTetrahedral.lean` を追加し、triangular Port face の局所 normal form を接続した。

- `IsTriangularPortFace` と `PortAllFacesTriangular`
- `facePortLabelSet` と nonzero label image subset
- triangular face の `faceCellLabelSum = 0` と exact `{deltaA,deltaB,deltaC}` image の同値
- conserved triangular face の crossing-pair exclusion
- `IsTetrahedralFacePattern` と dual-face Kirchhoff の同値
- genus-zero map における `HasTetrahedralFaceAssignment` と
  `HasDualFaceKirchhoffV4Assignment`、`PortFourStateColorable` の存在問題同値
- all-triangular conserved map の `DualLoopFree`
- `tetraStampColor` の append law と zero-holonomy closed-walk return

監査ファイルでは、4/6/3/12 の有限 cardinality、edge-delta fibers、incident edges、roll kernel、三非零 V4 closure、triangle coloring fixture の `{A,B,C}` pattern、`triangleAllDeltaA` の pattern failure、dual-loop exclusion、genus-zero existence equivalence、stamp transport を kernel-checked theorem として確認した。

## 境界

本実装は universal tetrahedral assignment existence、Four Color theorem、任意 map の triangulation reduction、一般 dual PortNetwork、rigid tetrahedron orientation、topological realization、physical board/game state、move minimization を扱わない。

したがって、all-triangular genus-zero map の次の未解決 fork は、triangulation reduction と tetrahedral assignment existence の二択として保存される。

## 検証

- `lake build DkMath.Tromino.TetrahedralClosure`
- `lake build DkMath.Tromino.PortTriangularTetrahedral`
- `lake build DkMathTest.Tromino.TetrahedralClosureAxiomAudit`
- `lake build DkMathTest.Tromino.PortTriangularTetrahedralAxiomAudit`
- `DkMath.Tromino.PortGenusZeroHolonomy`
- `DkMath.Tromino.PortF2Exactness`
- `DkMath.Tromino.PortDualityKernel`
- `DkMath.Tromino.PortTensionColoring`
- `DkMath.Tromino.LocalFrameEquiv`
- production forbidden-construct scan
- `#print axioms` による主要 local-normal-form / existence-equivalence theorem の監査
