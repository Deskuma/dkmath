# Test: DkMath

DkMath のテストプロジェクト。DkMathlib への依存を持ち、DkMath の理論を利用して様々な補題や例を実装する。
DkMathlib の理論が正しく機能しているかを確認するためのプロジェクトであり、DkMathlib のテストコードも兼ねる。

ライブラリの依存関係は [AGENT.md](../../../AGENT.md) を参照すること。逆依存に注意。

$$
\mathrm{DkMath.*} \;\to\; \mathrm{DkMath.Lib.*} \;\to\; \mathrm{DkMathlib.*}
$$

## Completionの公開入口

`CompletionFacadeAudit.lean` は `DkMath.Completion` だけをimportし、
一般核と数論・Gnomon consumerの参照、任意の平方殻の恒等式を確認する。
`DkMathTest.lean` へ登録済み。GN-PUB-002ではテストのビルドを行わず、
同じ検証本体を独立smokeとしてLeanで確認した。
[実装報告](../docs/dev/FLT-GN-regular-261018-v0/AnalysisGN/IMPLEMENTATION-GN-PUB-002.md) を参照。
