# TRM-043 実施報告

## 実施内容

- `PortTriangulationReduction.lean` に actual-port calibration を実装した。
- old-region の slot `0` と `1` をそれぞれ `oldEdge` と `radialOld` に対応させる encoder theorem を追加した。
- face-center region では、`faceCellOfPort` の subtype、`faceEquiv.symm (faceEquiv F) = F`、`facePortEquiv` の dependent `Fin` transport を明示して `radialCenter` の encoder theorem を追加した。
- 次の decoder calibration theorem を追加した。
  - `faceStarPortDecode_oldEdgePort`
  - `faceStarPortDecode_radialOldPort`
  - `faceStarPortDecode_radialCenterPort`
- 次の actual crossing formulas を追加した。
  - `faceStarCross_oldEdge`
  - `faceStarCross_radialOld`
  - `faceStarCross_radialCenter`
- 次の actual rotation formulas を追加した。
  - `faceStarRotate_radialOld`
  - `faceStarRotate_oldEdge`
  - `faceStarRotate_radialCenter`
- `PortFaceStarSubdivisionAxiomAudit.lean` に上記 12 theorem の `#check` と、3 encoder・1 crossing・1 rotation の `#print axioms` を追加した。

## 検証

- `lake build DkMath.Tromino.PortTriangulationReduction`
- `lake build DkMathTest.Tromino.PortFaceStarSubdivisionAxiomAudit`
- `lake build DkMath.Tromino.PortFaceStarSubdivision`
- `lake build DkMath.Tromino.PortCombinatorialMap`
- `lake build DkMath.Tromino.PortFaceOrbit`
- `lake build DkMath.Tromino.PortRotationSystem`
- `git diff --check`
- 対象 production source の forbidden construct scan

上記 Lean build はすべて成功した。actual-port の 3 encoder、3 decoder、3 crossing、3 rotation の exact calibration が kernel-check 済みである。

## Outcome A

TRM-043 の actual constructor calibration closure を完了した。次段の cyclicity、global orbit、coloring、Hamiltonian boundary、universal exchange provider は本実装単位の対象外として追加していない。
