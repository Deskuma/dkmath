# TRM-041 実施報告

## 実施内容

- TRM-040 が carrier-level partial であったことを確認した。
- face-star の semantic crossing
  oldEdge p と oldEdge (M.crossing.cross p) の交換、
  radialOld p と radialCenter p の交換を実装した。
- semantic crossing の involution を kernel-check した。
- semantic rotation を実装した。
  - radialOld p -> oldEdge p
  - oldEdge p -> radialOld (rho p)
  - radialCenter p -> radialCenter (phi⁻¹ p)
- semantic rotation の明示的な逆同値と左右逆元を kernel-check した。
- audit に semantic crossing／rotation の declarations と axiom checks を追加した。

## 検証

- lake build DkMath.Tromino.PortTriangulationReduction
- lake build DkMathTest.Tromino.PortFaceStarSubdivisionAxiomAudit

いずれも成功した。

## 現在の境界

actual dependent-Fin port decode の逆方向証明が残っている。具体的には、
任意の actual port の q.1 を finSumFinEquiv.symm で分解し、旧領域では
finProdFinEquiv.symm、中心領域では facePortEquiv.symm で戻した結果が、
元の Sigma port と等しいことを示す bridge である。

この bridge が未完のため、actual crossing／rotation transport、
PortCombinatorialMap の完成、三角 face theorem、Euler／genus、
coloring restriction、universal reduction equivalence はまだ公開していない。
未証明命題や axiom による代替は行っていない。
