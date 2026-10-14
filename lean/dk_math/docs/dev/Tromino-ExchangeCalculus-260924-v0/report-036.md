# TRM-037 実装報告

## 実装内容

- `DkMath.Tromino.PortF2Exactness` を追加し、Port F2 chain complex
  `C2 -> C1 -> C0` の genus-zero exactness を実装した。
- A–B: `portBoundary2_edgeCellOfPort` により、edge representative に依存しない
  `y F + y G` の boundary-2 coefficient を証明し、constant face chain の kernel
  包含を閉じた。dual-loop の自己隣接も F2 の `a+a=0` として含む。
- C–F: `PortFaceAdjacent`、反射・対称・推移可能な
  `PortFaceReachable`、rotation step、同一 primal region、region walk からの
  face reachability を追加した。
- G–I: strong map の face-cell connectivity、boundary-2 kernel の隣接伝播、
  `PortConstantFaceSpace` と `ker ∂2` の一致（face 非空条件付き）を証明した。
- J–K: vertex augmentation、`range ∂1 = ker augmentation` を追加した。
  逆包含は base region から各 region への chosen walk を係数付きで総和する構成的証明である。
- L–O: `ZMod 2` の有限体 instance をロードし、rank-nullity、face 非空性、
  `finrank` の Euler identity を実装した。
- P: 主定理
  `portGenusZero_faceBoundarySpace_eq_cycleSpace` を証明した。
- Q: genus-zero の closed `PortRegionWalk` の edge-parity chain が face-boundary
  space に属することを追加した。
- R: triangle および triangle-dual fixture の C0/C1/C2、cycle space、
  face-boundary space の次元と主定理による一致を監査し、triangle closed walk の
  face-boundary membership も確認した。
- `DkMathTest.Tromino.PortF2ExactnessAxiomAudit` を追加した。

## 意味上の境界

今回の endpoint は、connected strong Port combinatorial map の
combinatorial genus zero における F2 chain exactness
`im ∂2 = ker ∂1` である。これは finite combinatorial map の cycle generation
を与えるが、V4 flow の universal existence、zero-holonomy converse、Four Color
theorem、または一般 genus の exactness は主張しない。次段階は指示どおり、
face-boundary conservation から zero holonomy / TRM-031・TRM-033 側へ接続する。

## 検証

`lean/dk_math` で以下が成功した。

```text
lake build DkMath.Tromino.PortF2Exactness
lake build DkMathTest.Tromino.PortF2ExactnessAxiomAudit
lake build DkMath.Tromino.PortF2Chains
lake build DkMath.Tromino.PortV4Chains
lake build DkMath.Tromino.PortDualityKernel
lake build DkMath.Tromino.PortCombinatorialMap
lake build DkMath.Tromino.IntegralMod2Bridge
```

`git diff --check`、新規 production/audit/report の diff check、production
forbidden-construct scan（`sorry`, `admit`, `unsafe`, `axiom`,
`noncomputable`）を実施した。production file の `#print axioms` でも、
新規 exactness theorem は禁止された新規公理を導入していない。
