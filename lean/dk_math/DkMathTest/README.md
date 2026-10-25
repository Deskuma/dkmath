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

`Lib/NumberTheory/EllipticSplitDyadic.lean` は005Aの分裂接錐を確認する。
実際の非Frey曲線と同じ3捩れ点で、Frobenius差は滑らか、和は滑らかでないことを証明した。
通常テストの同一本体を独立Lean資料で確認した。
[005A報告](../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-005A-261025.md) を参照。

`Lib/RepresentationTheory/CofixedDeterminant.lean` は005Bの一般核を検証する。
安定性とCofixed性の違い、一次元条件、指標と逆指標、非零の右上成分、三次元非可逆写像を扱う。
通常テストの同一本体を独立Lean資料で確認した。
[005B報告](../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-005B-261025.md) を参照。

`Lib.RepresentationTheory.CofixedImage` tests the same quotient/projection image,
zero-map kernel guard, equivariance and cofixedness boundaries, and the actual
elliptic [p] multiplication map whose full torsion kernel cannot be a line.
[005C1 report](../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-005C1-261025.md).

`Lib.NumberTheory.EllipticFiniteKernel` uses the actual curve y²=x³−x and its
rational point (1,0): same two-point kernel, fixed-field degree two, normalization
constant one, translation/Galois invariance, trace versus average, and trivial kernel.
[005C2A report](../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-005C2A-261025.md).

`Lib.NumberTheory.EllipticFiniteKernelPoles` checks actual poles at O and (1,0)
on y²=x³−x, regularity at (-1,0), total pole orders 4/6, individual transcendence,
cancellation with equal valuations, constant functions, and the trivial kernel.
[005C2B report](../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-005C2B-261025.md).

`Lib.NumberTheory.EllipticFiniteKernelDegree` checks the actual subfields ℚ(tⁿ):
coprime degrees 2,3 generate ℚ(t), while degrees 4,6 generate ℚ(t²).
Repeated degree 2 and a zero common factor check the guards. The previous actual
curve/kernel example now has finite positive degrees and a genuine monic relation.
[005C2C1 report](../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-005C2C1-261025.md).

`Lib.NumberTheory.EllipticFiniteKernelGeneration` checks relative degrees 2,3 and ambient
degrees 4,6 for the same actual curve/kernel, unconditional fixed-field generation,
minimal-polynomial degree 2 and an actual monic quadratic relation. The trivial kernel
also has degrees 2,3 and generates its fixed field.
[005C2C report](../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-005C2C-261025.md).

`Lib.NumberTheory.EllipticFiniteKernelModel` checks the same actual two-point kernel:
model equation, injectivity, generic nonsingularity, fixed-field image, degree two and
rational coefficient descent. The trivial kernel recovers the original model with Δ=64.
The contrasting cusp y²=x³ has a nonsingular generic point (t²,t³), degrees two and three
and full field generation, but Δ=0 and a singular origin. This is a boundary for inference
from generic data, not a counterexample to elliptic finite-kernel quotients.
[Quotient-model report](../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-QUOTIENT-MODEL-261025.md).

`Lib.NumberTheory.EllipticFiniteKernelSpecialization` checks actual finite evaluation
on y²=x³−x with H={O,(1,0)} and R=(−1,0), producing target coordinates (−2,0).
It verifies the same equation and two-torsion root, orbit invariance, the pole guard,
a three-root discriminant example, the cusp separation guard, and the trivial-kernel
all-point zero fiber with target ellipticity actually supplied. The even kernel has
distinct points R,R+Q with the same x-image, guarding against universal separation claims.
[Point-specialization report](../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-POINT-SPECIALIZATION-261026.md).

`Lib.NumberTheory.EllipticFiniteKernelNonsingular` uses the full three-torsion kernel
on the actual curve y²=x³−x, proves its order nine and oddness, and checks the same
target discriminant, rational-function degree nine, finite-fiber bound and separated
two-torsion images. It also checks rational target ellipticity, all-point zero fiber
and orbit invariance without an external ellipticity instance. The old two-point
kernel cannot satisfy the new odd-cardinality guard.
[Target-nonsingularity report](../docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE032-TARGET-NONSINGULAR-261026.md).
