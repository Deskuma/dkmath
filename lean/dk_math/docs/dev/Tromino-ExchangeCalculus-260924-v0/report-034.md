# TRM-035 実装報告

## 実装内容

- `DkMath.Tromino.LocalFrameEquiv` を追加し、有限パネル・4 色・hole・3 色 body・delta を持つ `TrominoExchangeFrame` と、cardinality、gap、非零 delta、body 上の delta 像、frame equivalence、局所交換の共役を定義・証明した。
- Gaussian `block2` パネルと Eisenstein mod-2 `TrominoState` パネルを実装し、両者の frame equivalence、gap/delta 保存、局所交換対応を追加した。
- `DkMath.Tromino.PortV4Chains` を追加し、頂点・辺・面の `PortF2 × PortF2` chain alias、座標分解 linear equivalence、V4 boundary、座標 compatibility、`boundary1 ∘ boundary2 = 0`、cycle/face-boundary inclusion を実装した。
- delta の座標恒等式、頂点 Kirchhoff 条件の座標版、三角形 face vector と dual vector の有限検証を追加した。
- `PortF2Chains` に face-cell representative invariance、reverse walk edge chain、cross-indicator edge coefficient の一般補題を追加し、既存の三角形・dual calibrations を回収した。
- `LocalFrameEquivAxiomAudit` と `PortV4ChainsAxiomAudit` を追加した。

## 境界

この実装は有限・計算可能な frame、mod-2 chain、局所座標および有限 wave の検証に限定する。genus-zero exactness、ring equivalence、full lattice equivalence、universal flow、Four Color theorem は主張していない。all-face `portBoundary2 R C (fun _ => 1) = 0` は本 checkpoint の必須条件ではないため、新しい無条件主張としては追加していない。

## 検証

以下を `lean/dk_math` で実行し、全て成功した。

```text
lake build DkMath.Tromino.LocalFrameEquiv DkMath.Tromino.PortV4Chains
lake build DkMathTest.Tromino.LocalFrameEquivAxiomAudit DkMathTest.Tromino.PortV4ChainsAxiomAudit
lake build DkMath.Tromino.PortF2Chains DkMathTest.Tromino.PortF2ChainsAxiomAudit
lake build DkMath.Tromino.PortDualityKernel DkMathTest.Tromino.PortDualityKernelAxiomAudit
lake build DkMath.Tromino.PortKirchhoffFlow DkMath.Tromino.FourColorCell
```

production files の forbidden construct scan (`sorry`, `admit`, `unsafe`, `axiom`, `noncomputable`) は該当なし。次の候補は、今回の frame/chain bridge を用いた積分 mod-2 bridge の限定的な追加である。
