# TRM-042 実施報告

## 実施内容

- `PortTriangulationReduction.lean` に actual-port codec を実装した。
- `Fin` の arity transport、`finProdFinEquiv` による old-region slot 分解、face-center の subtype fiber、`Sigma` の region 分解を合成した。
- 次の computable API を追加した。
  - `faceStarPortEquiv`
  - `faceStarPortEncode`
  - `faceStarPortDecode`
  - `faceStarPortDecode_encode`
  - `faceStarPortEncode_decode`
- `faceStarDescSource` と `faceStarPortDecode_source` を追加し、descriptor ごとの source-region を kernel-check した。
- `faceStarCrossing` を semantic crossing の transport として実装し、involutive と changesRegion を descriptor cases で証明した。
- `faceStarLocalRotation` を semantic rotation の transport として実装し、既存の face-orbit 補題を用いて preservesRegion を証明した。
- descriptor 上の transport formulas として `faceStarCrossing_encode`、`faceStarLocalRotation_encode` を追加した。
- `DkMathTest/Tromino/PortFaceStarSubdivisionAxiomAudit.lean` に codec、crossing、rotation の API および `#print axioms` を追加した。

## 検証

- `lake build DkMath.Tromino.PortTriangulationReduction`
- `lake build DkMathTest.Tromino.PortFaceStarSubdivisionAxiomAudit`

上記はいずれも成功した。

## Outcome P

TRM-042 の stop condition にある actual constructor の exact formulas は未完了である。
具体的には、次の calibration bridge が残っている。

    faceStarPortDecode I (faceStarOldEdgePort I p) = .oldEdge p
    faceStarPortDecode I (faceStarRadialOldPort I p) = .radialOld p
    faceStarPortDecode I (faceStarRadialCenterPort I p) = .radialCenter p

この bridge が未完了のため、actual constructor を直接使う
`faceStarCross_oldEdge`、`faceStarCross_radialOld`、`faceStarCross_radialCenter`、
および三つの actual rotation formulas は追加していない。
codec、actual `PortCrossing`、actual `PortLocalRotation`、source-region 証明、
descriptor-level transport formulas までは実装済みである。

## 次の実装単位

actual constructor と `faceStarPortEncode` の exact calibration を、old slot と
face-center subtype の `Sigma.ext`／`Subtype.ext` bridge として固定し、TRM-042 の
six exact formulas を追加する。
