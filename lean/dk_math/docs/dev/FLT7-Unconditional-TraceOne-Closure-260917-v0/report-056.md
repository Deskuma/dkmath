# FLT7TC-005R50 — Source-plane norm-minus-seven landing

## 実装結果

`instruction-056.md` の source-plane norm-minus-seven landing を、R49 の
provenance を保った中立モジュールとして実装した。

追加した production module:

`DkMath/FLT/Seven/SevenRealCubicSourcePlaneNormSeven.lean`

追加した facade import:

`DkMath/FLT/Seven.lean`

追加した検証 client:

- `DkMathTest/FLT/SevenRealCubicSourcePlaneNormSevenApi.lean`
- `DkMathTest/FLT/SevenRealCubicSourcePlaneNormSevenAxiom.lean`
- `DkMathTest/FLT/SevenRealCubicSourcePlaneNormSevenR50Scratch.lean`

## Source-plane axis and neutral identities

`sourcePlaneNormSevenAxis := linearSource 2 (-3)` を定義し、次を kernel-check
した。

- `sourcePlaneNormSevenAxis = 2 - 3 * alpha`
- `norm sourcePlaneNormSevenAxis = -7`
- `IsSourcePlane sourcePlaneNormSevenAxis`
- 任意の `A B C : ℤ` について
  `thetaSquareInt (sourcePlaneNormSevenAxis * ofThetaCoordinates A B C)
   = -3 * B + 14 * C`
- `3 * B = 14 * C` から積の source-plane 帰結
- 任意の `x` について
  `thetaSquareInt (sourcePlaneNormSevenAxis * x)
   = -3 * thetaLinearInt x + 14 * thetaSquareInt x`

さらに、linear-source norm formula

`norm (linearSource a b) = a^3 + 2*a^2*b - a*b^2 - b^3`

を実装した。

## Three calibrations

次の三校正と norm `-7` を実装した。

- `linearSource (-3) 1 = eisensteinAxis`
- `linearSource 1 2 = ramifiedAxis`
- `linearSource 2 (-3) = sourcePlaneNormSevenAxis`

`Y0 = 1`, `Y1 = ofThetaCoordinates 9 14 3`,
`Y2 = ofThetaCoordinates (-10) (-14) (-3)` に対応する積と projective log を
kernel-check した。

- `sourcePlaneNormSevenAxis * Y0 = linearSource 2 (-3)`
- `sourcePlaneNormSevenAxis * Y1 = eisensteinAxis`
- `sourcePlaneNormSevenAxis * Y2 = ramifiedAxis`
- `projectiveLog Y0 = (0, 0)`
- `projectiveLog Y1 = (0, 5)`
- `projectiveLog Y2 = (0, 1)`

`Y1` と `Y2` の norm-one も実装し、それぞれの explicit unit lift を公開した。

## R49 packet landing

`DirectOrbitTrivialCommonFactorSharpenedPacket P` から、
`Y := (P.t ^ (7^9) : SevenRealCubicIntˣ)` について、次を一つの theorem
`directOrbitTrivialCommonFactorSharpenedPacket_correction_line` にまとめた。

- `3 * thetaLinearInt Y = 14 * thetaSquareInt Y`
- `Y ≠ 1`
- `norm Y = 1`
- `projectiveLog (Additive.ofMul Y) = 0`

この correction line を source-plane multiplication formula に代入し、
次の landing theorem を kernel-check した。

`directOrbitTrivialCommonFactorSharpenedPacket_source_plane_landing`

- `IsSourcePlane (sourcePlaneNormSevenAxis * Y)`
- `norm (sourcePlaneNormSevenAxis * Y) = -7`

## Boundary audit

Part F/G の narrow/full binary-cubic classification、Part H の `C = 1` exclusion、
Part I の dichotomy collapse は、この checkpoint の kernel-checked endpointには
含めていない。有限探索の完全性、association-only classification、fundamental-unit
basis、Thue/Baker theorem、successor/descent、FLT7 conclusion は追加していない。

したがって R50 の結果は、source-plane norm-minus-seven landing と三校正が green
となった **Outcome B** である。

## 検証結果

Lean は並列実行せず、次を順番に実行し、すべて exit 0 だった。

1. `lake build DkMath.FLT.Seven.SevenRealCubicSourcePlaneNormSeven`
2. `lake build DkMath.FLT.Seven`
3. `lake build DkMathTest.FLT.SevenRealCubicSourcePlaneNormSevenApi`
4. `lake build DkMathTest.FLT.SevenRealCubicSourcePlaneNormSevenAxiom`
5. `lake env lean DkMathTest/FLT/SevenRealCubicSourcePlaneNormSevenR50Scratch.lean`

axiom audit は production theorem と correction/landing theorem が
`[propext, Classical.choice, Quot.sound]`（norm formula は `[propext]`）であることを
確認した。新規 R50 source/API/scratch に `sorry`, `admit`, `axiom`, `unsafe`,
`native_decide` はない。
