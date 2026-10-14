# TRM-036 実装報告

## 実装内容

- `DkMath.Tromino.IntegralMod2Bridge` を追加し、`GaussianInt = Zsqrtd (-1)` と `TraceOneInt (-1)` の座標 parity を `TrominoState = ZMod 2 × ZMod 2` へ送る computable additive homomorphism を定義した。
- Gaussian の `0, 1, i, 1+i`、Eisenstein の `eisensteinCoord 0 0`, `eisensteinCoord 1 0`, `eisensteinCoord 0 1`, `eisensteinCoord 1 1` を明示的に監査し、両 parity map の surjectivity と computable section を証明した。
- Gaussian `block2` の integral coordinate map を追加し、panel color と parity の一致、gap-relative parity と `frameDelta` の一致を証明した。既存の `gaussianEisensteinFrameEquiv` は、Gaussian integral relative direction を mod-2 に落としたものとして実現した。
- 既存 block2 の body 順序 `(0,0), (1,0), (0,1)` に対する gap-relative direction はそれぞれ `deltaC, deltaB, deltaA` であることを固定した。
- 三つの非零 Gaussian direction と標準 Eisenstein direction の parity image が共通の `{deltaA, deltaB, deltaC}` になることを Finset image で証明した。
- Gaussian/Eisenstein の誘導 mod-2 multiplication、積との compatibility、`deltaB²` と `deltaC²` の calibrations を追加した。Gaussian 側では `deltaC² = 0`、Eisenstein 側では `deltaC² = deltaB` であり、非零 Eisenstein square の非零性から zero-preserving multiplicative equivalence の不存在を証明した。
- `PortV4Chains` の既存 coefficient convention との接続として、共通 parity coefficients と triangle coloring / triangle-dual balanced assignment の有限 calibrations を監査した。
- `DkMathTest.Tromino.IntegralMod2BridgeAxiomAudit` を追加した。

## 意味上の境界

形式化したのは、二つの実整数座標 carrier が同じ additive V4 と三つの local direction を持つこと、および induced multiplication が異なることだけである。GaussianInt と EisensteinInt の ring equivalence、`Z[i]/(2)` と Eisenstein quotient の同一視、full lattice/topological equivalence、genus-zero exactness、universal dual flow、Four Color theorem は主張していない。今回の multiplication obstruction は、TRM-035 の frame equivalence が additive/exchange level に限定される理由を kernel-checked に示す。

## 検証

`lean/dk_math` で以下を実行し、成功した。

```text
lake build DkMath.Tromino.IntegralMod2Bridge
lake build DkMathTest.Tromino.IntegralMod2BridgeAxiomAudit
lake build DkMath.Tromino.LocalFrameEquiv
lake build DkMath.Tromino.PortV4Chains
lake build DkMathTest.Tromino.LocalFrameEquivAxiomAudit
lake build DkMathTest.Tromino.PortV4ChainsAxiomAudit
lake build DkMath.Lib.NumberTheory.EisensteinCoordinates
```

`#print axioms` では新規 parity、multiplication、obstruction theorem に `sorryAx` はなく、production forbidden-construct scan (`sorry`, `admit`, `unsafe`, `axiom`, `noncomputable`) も該当なしだった。次は指示どおり genus-zero exactness `im ∂2 = ker ∂1` に戻る。
