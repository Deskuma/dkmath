# NOTE-012: 実際のtorsionの幾何学的有限性

日付: 2026-10-20。NOTE-012 §5 の工程1・2を実装した。
標数0かつn≠0なら、同じ曲線の実際のE[n]が有限であることを証明した。
これにより、素数指数のFrey表現の開核・正規有限レベルに、有限性や位数p²の追加入力が不要になった。

## 1. 今回の到達点

| 工程 | 実装結果 | 範囲 |
| --- | --- | --- |
| 倍写像と除法多項式 | 実際の非特異点Pについて `[n]P=O ↔ ψₙ(P)=0` | 標数0、整数n |
| 一変数の座標拘束 | n倍零の有限座標点のxは `ΨSq n` の根 | 実際のn倍写像の核から導出 |
| E[n]の有限性 | 非零多項式の有限個の根と、各x上の有限ファイバーから証明 | 標数0、n≠0。素数性は不要 |
| Freyの開核・有限レベル | `residualKernel_isOpen_of_prime`、`residual_normal_finite_level`、`residual_factorsThroughFiniteLevel_of_prime` | 同じSource、素数p。Finite・位数の追加仮定なし |
| 位数p² | 未証明 | 次の幾何学的計算 |
| 次元2・GL₂実現 | 今回は無条件化していない | 正確な位数の入力が必要 |

本体6モジュール、教科書解説を含め1,703行。名前付き公開宣言237個。
回帰は名前付き5補題と4例、依存監査は別のモジュールで実施する。
全ての新規Leanモジュールにimport後の `#print "file: モジュール名"` を置いた。

## 2. 実装したモジュール

| モジュール | 数学的な役割 |
| --- | --- |
| `EllipticDivisionSequence` | 正規化EDSの再帰からnet恒等式を証明 |
| `EllipticDivisionUniversal` | 有理係数の普遍曲線、座標環、普遍点、任意の点への評価 |
| `EllipticDivisionCoordinates` | ψ・φと、2で割って構成するy座標の分子ω |
| `EllipticDivisionMultiplication` | 普遍点の倍写像、座標環での恒等式、実際の点への特殊化 |
| `EllipticTorsionFinite` | 実際の点群の核の有限性、有限性インスタンス、開核・有限レベル |
| `FreyResidualGeometry` | 同じFrey Sourceへの適用 |

前四つの補助宣言は `DkMath.Lib.NumberTheory.EllipticDivision` に隔離した。
利用側の主要APIは既存の `EllipticTorsionRepresentation` と `Frey.Source` 名前空間で公開する。
`DkMath.Lib`、`DkMath.FLT`、`DkMathTest` の公開入口へ配線した。

## 3. 有理係数による短縮

参照した一次ソースは
[Def_WeierstrassCurve_EDSEngine.lean](https://github.com/anthropics/fermats-last-theorem/blob/main/Definitions/Def_WeierstrassCurve_EDSEngine.lean)。
取得した版は1,870行、blob SHAは `1baedebf5d82fbcf4a1d543f7a7582ac96edcfc5`。
これをそのままimportせず、必要な楕円列・普遍点・倍写像の経路を現在のMathlibへ翻訳した。
外部の互換モジュール、参照実装の一般的な可除列の拡張、位数公式のパッケージはimportしていない。

Frey曲線はℚ上にあるので、今回は普遍係数をℤからℚへ変更した。
y座標の分子を

\[
\omega_n=\tfrac12(\psi^c_n-a_1\phi_n\psi_n-a_3\psi_n^3)
\]

で定義できる。`ψc` にはMathlibの `complEDS₂` を使う。
これにより、一般の可換環でωの整係数性を導くための補完列・還元不変量の構成を省いた。
`two_mul_ωe` と `map_ωe` が、この分子の恒等式と特殊化の可換性を保証する。
この短縮の代償として、正標数への適用は今回の定理に含めない。
ここでの標数0は曲線の座標体の条件であり、残余表現の係数体 `ZMod p` が標数pであることとは両立する。

再利用・翻訳した四モジュールにはApache-2.0の表示、出典、変更内容を記した。
ライセンス本文と上流NOTICEには、同じNumberTheory層の既存の
`RegularKummer/LICENSE` と `RegularKummer/ANTHROPIC-NOTICE` を参照している。
今回新たに組み立てた有限性・Frey facade・回帰・監査はリポジトリのMIT形式に従う。

## 4. 普遍点から実際の点へ

普遍曲線の非零な次数のψが消えないことは、尖点曲線の点(1,1)への特殊化で示す。
この特殊化では正規化EDSが整数nの列になるので、n≠0なら普遍分母は非零である。
普遍体上では座標有理式が定義でき、net恒等式を加法公式へ翻訳して整数倍の座標と一致させる。

次にJacobian座標で多項式等式へ戻し、普遍座標環から任意の標数0の非特異点へ評価する。
特殊化でψが零になる場合も、JacobianのZ座標が零の点、すなわち無限遠点として扱える。
このため `zsmul_eq_smulEval` は「分母が非零」という追加仮定を要求しない。

`smul_eq_zero_iff_evalEval_ψ` が、実際の点群の整数倍とψの消滅を同値にする。
`evalEval_ψ_sq` は座標環の曲線方程式を使い、二変数ψの平方を一変数 `ΨSq` の評価へ変換する。
有限性ではこの二つの前向きの接続だけを使う。

## 5. 根を数えずに有限性を得る

主要な定理の形は次の通りである。

```lean
finite_torsion_of_ne_zero
  (E : WeierstrassCurve K) (n : ℕ) (hn : n ≠ 0) :
  Finite (Torsion E n)
-- Kには Field と CharZero を要求する。
```

証明は以下の経路を通る。

1. 実際のn倍写像の核の点Pが無限遠点なら、有限集合 `{O}` に入る。
2. P=(x,y)なら、`torsion_some_coordinate_root` によって `ΨSq n` の根へ拘束される。
3. `ΨSq_ne_zero` とn≠0から多項式の非零性を得る。
4. `Polynomial.finite_setOfPred_isRoot` によって根の集合は有限。
5. `Affine.finite_preimage_xRep0` により各根の上の点も有限。
6. 有限和と部分集合の有限性から、元の同じ核の有限性を得る。

実際の点群を別の有限モデルへ置き換えたり、位数p²を仮定したりしていない。
n=0では除法多項式も零になるので、この手順は使えない。非零次数の条件を保持した。
利用するのは非特異点の群則であり、特異点を群へ付け加えることもしていない。

`torsionFinite` はこの証明を `NeZero n` の下で標準インスタンスとして公開する。
素数pのFrey表現には自動的に適用され、NOTE-011の開核・有限レベルの証明へ接続する。

## 6. 回帰と残る境界

実在するSource 2、すなわち(4,3,5)からの曲線について、**その同じ曲線の37-torsion** の
有限性と有限レベルを証明した。仮想的なSource 37だけに依存する検査にしないためである。
既存の非零2-torsion点(0,0)の座標拘束も確認する。
Source 37では、有限性・開核・正規有限レベルをFiniteやhcardを受け取らずに使えることを確認する。

正確な位数については
[card_torsion_of_isAlgClosed の証明本体](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean)
の素数限定経路も調べた。今回取得した版は1,336行、blob SHAは
`865709609f50e0e2ef445df7c01d01768ca731c5`。
奇素数の場合も、倍写像の全射性、一般ファイバーの平方因子の除去、ファイバーの正確な個数を結ぶ
`exists_double_fiber_card` と `card_nTorsion_odd_fibers` が残る。
今回の有限性証明はこの個数計算に依存しない。

したがって、今回でNOTE-012の工程1・2を固定し、工程3の位数p²、工程4・5の次元2・GL₂実現を残す。
既約性・Weil対・行列式・慣性作用・Artin導手・FLTの終点も今回の結論には含めない。

検証コマンドと結果は [validation-note012.txt](evidence/validation-note012.txt)、
ルート入口の検査は [RootSmokeNOTE012.lean](evidence/RootSmokeNOTE012.lean) に記録する。

焦点を絞った回帰ビルドは3,163 jobs、依存監査ビルドは3,164 jobs成功。
新規237宣言と回帰5補題の公理監査、および12経路の依存監査が通った。
公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
`lake build DkMath DkMath.FLT DkMath.Lib DkMathTest` は11,547 jobs成功し、新規モジュールに警告はない。
ルートsmoke、`lake env lean DkMathTest.lean`、マーカーチェッカー、`git diff --check` も成功した。
