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

## NOTE-032の枝交換の境界

`Lib/RepresentationTheory/CofixedBranchSwap.lean` を通常入口へ登録した。
標数2、奇標数のせん断、真でない吸収空間、mod8の残る枝を実際の有限表現・整数で確認する。
本作業ではテストをビルドせず、同一の検証本体を独立Lean資料として確認した。
[実装報告](../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-001-261025.md) を参照。

`Lib/NumberTheory/EllipticFrobeniusBranchSwap.lean` は003Cの算術境界と具体曲線を確認する。
非Frey曲線の実際のFrobeniusで方向交換と3捩れ点の和まで検証した。
通常テストと同じ本体を独立Lean資料で確認した。
[003C報告](../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-003C-261025.md) を参照。

`Lib/NumberTheory/ValuationPrimeExistence.lean` は004の住所の存在を確認する。
ℚ(X)の37上の住所、ℚの代数閉包上のFrobeniusと、1・異なる素数・正標数の境界を扱う。
通常テストの同一本体を独立Lean資料で確認した。
[004報告](../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-004-261025.md) を参照。
