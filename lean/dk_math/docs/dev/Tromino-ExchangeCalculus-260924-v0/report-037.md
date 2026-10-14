# TRM-038 実装報告

## 実装

DkMath/Tromino/PortGenusZeroHolonomy.lean を追加し、TRM-037 の F₂ exactness を V4 face conservation と zero holonomy に接続した。

- assignmentEdgeLabel と assignmentEdgeLabel_edgeCellOfPort
  - crossing pair の厳密な region index 順序による代表元なしの edge label 抽出
  - crossing 反転の calibration theorem
- portEdgeLabelEval
  - F₂ edge chain から TrominoState への線形評価
  - edge basis、singleton、任意 list、Port walk、Flow/Port round-trip の評価定理
- faceCellLabelSum
  - face boundary edge chain の V4 評価
  - port representative による face-boundary label sum との一致
  - representative independence
- IsFaceCellKirchhoff
  - face-cell conservation と IsDualFaceKirchhoff の同値
- boundary-two/evaluation adjunction
  - portEdgeLabelEval (portBoundary2 ... y) の face-cell sum 表現
  - face conservation による face-boundary space 全体の annihilation
- genus-zero closure
  - TRM-037 の portGenusZero_closed_portWalkEdgeChain_mem_faceBoundarySpace を利用
  - closed structural walk の XOR が zero
  - IsDualFaceKirchhoff -> IsZeroHolonomyV4Tension
  - 固定 assignment の IsDualFaceKirchhoff ↔ IsZeroHolonomyV4Tension
- coloring reconstruction
  - face conservation から label recovery 付き coloring reconstruction
  - HasDualFaceKirchhoffV4Assignment ↔ PortFourStateColorable
  - PortGenusZeroDualFaceKirchhoffTarget ↔ PortGenusZeroFourColorTarget

DkMathTest/Tromino/PortGenusZeroHolonomyAxiomAudit.lean では、edge evaluation、face-cell reconciliation、adjunction、closed-walk closure、coloring recovery、triangle coloring、primal Kirchhoff と dual-face conservation の区別を監査した。

## 境界

本実装は、genus-zero map ごとの face-conservative assignment の存在を証明するものではない。したがって、Four Color theorem、一般 dual PortNetwork の構成、topological realization、tetrahedron orientation holonomy、PortGenusZeroDualFaceKirchhoffTarget 自体の証明は含まない。

tetrahedral rolling の解釈として、face boundary は rolling route の V4 delta、IsDualFaceKirchhoff は elementary face boundary の zero delta、TRM-037 と TRM-038 は genus-zero certificate 上の closed route の zero color holonomy を与える。

## 検証

- lake build DkMath.Tromino.PortGenusZeroHolonomy
- lake build DkMathTest.Tromino.PortGenusZeroHolonomyAxiomAudit
- production forbidden-construct scan
- principal converse、fixed-assignment equivalence、coloring reconstruction、target equivalence の #print axioms
