# NOTE-011: 同変比較・次元と有限レベルの教科書実装

日付: 2026-10-20。NOTE-011 §8 の前半を実装し、後半は位数・有限性の必要条件を
明示した定理として接続した。元のSource、曲線、幾何学的点、座標作用を保持している。

## 1. 今回の証明範囲

| 項目 | kernelで確認する内容 | 供給していない入力・結論 |
| --- | --- | --- |
| 安定部分加群・既約性 | 実際の表現上の述語と同変線形同型による相互輸送 | Frey表現の既約性そのもの |
| 標準torsionByとの比較 | 点を保つZMod n線形同型、独立に制限した座標作用との可換性、部分加群の順序同型 | 外部リポジトリの宣言のimport |
| 次元2 | **実際のE[p]の位数p²を引数として**有限性と次元2を導出 | 楕円曲線の位数p²公式の幾何学的証明 |
| 開核 | **実際のE[n]が有限なら**、全点の開固定部分群の有限共通部分として証明 | 全nについての有限性の無条件証明 |
| 有限レベル | 上の開核から正規な有限中間体Lを選び、Lの固定部分群が核に含まれることを証明 | Weil対、行列式、慣性作用、Artin導手 |

追加本体は6モジュール458行（教科書docstring込み）、公開宣言42個。
回帰は9個の名前付き補題と4個のexample、依存監査は別モジュールに置いた。
全ての新規モジュールにimport後の `#print "file: モジュール名"` を挿入した。

## 2. 同じ点を保つ翻訳

`EllipticTorsionGaloisStable.lean` の前半は任意の表現についての線形代数である。
`IsStable ρ N` は全ての群元によるNの保存、`IsIrreducible ρ` は非零性と安定部分加群の分類。
同変線形同型eに対してNの像の安定性はNの安定性と同値になり、既約性も双方向に輸送できる。
後半でこれを実際のE[n]へ特殊化する。

`EllipticTorsionStandardEquiv.lean` は既存の加法同型を線形同型へ強化する。
標準側の `standardRepresentation` は `pointAction` を整数torsion条件へ制限して構成し、
比較する作用を同型による共役として定義して済ませることはしていない。
その上で `torsionByLinearEquiv_equivariant` が二つの座標作用の可換性を証明する。
同型とその逆は元の点をそのまま返す。

`torsionSubmoduleEquiv` は全ての部分加群の順序同型である。
`standard_isStable_iff` と `standard_isIrreducible_iff` が安定性・既約性を相互翻訳する。
`FreyResidualIrreducibility.lean` では同じ `Source.rationalCurve` 上の述語と同値を公開する。

参照した一次ソースは
[標準torsionと既約性の定義](https://github.com/anthropics/fermats-last-theorem/blob/main/Definitions/Def_FLTPrelim_GaloisRep.lean)。
その定義と同じく非零条件を保持した。これによりE[1]の零空間を既約と呼ぶことを防いでいる。

## 3. 次元2の依存調査と残る幾何学

ローカルMathlib 4.34.1を検索し、除法多項式の `Basic.lean` と `Degree.lean` は確認したが、
`card_torsion_of_isAlgClosed` や `finrank_zmod_torsionBy_point_eq_two` に対応する
実際の点群の位数・次元providerは見つからなかった。
`smul_eq_zero_iff_evalEval_ψ`、`zsmul_eq_smulEval` の名前もローカルMathlibには存在しなかった。
検索したMathlibのコミットは `d13f23b723b8a846827a245b89c10fc7d3f11612`。

公開されている
[位数公式の証明本体](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean)
を確認した。これは1,268行のファイルで、さらに `Definitions.Def_WeierstrassCurve_EDSEngine` に依存する。
次の段階を含むため、終端の短い位数公式だけを取り込むことはできない。

1. 実際の点の倍写像を除法多項式の評価に接続する。
2. 座標有理式の分子・分母の互いに素性と、倍写像のファイバーを扱う。
3. 根の重複度と点の数を結び、素数torsionの位数を数える。
4. 一般nには素数冪・互いに素な積への拡張を行う。

今回必要な素数pの位数p²についても、少なくとも前半の幾何学を別の証明単位として実装する必要がある。
この調査は全依存ソースの移植や再ビルドを行ったものではない。

今回の `finrank_eq_two_of_card_sq` はhcardを明示的な引数とし、
`Nat.card` が無限型では0になることを利用して、p²≠0から有限性を取り出す。
そこから `Module.natCard_eq_pow_finrank` とp≥2による冪の単射性を使う。
標準torsionByの位数入力も `standard_card_sq_iff` を通して接続できる。
曲線が楕円曲線で標数がpでないという仮定からhcardを生成する部分は未実装である。
したがって、実際のE[37]の無条件な次元2やGL₂表現を完成したとは主張しない。

## 4. 有限性だけで進められた接続

`EllipticTorsionFiniteLevel.lean` では

\[
\ker\rho_n=\bigcap_{P\in E[n]}\operatorname{Stab}(P)
\]

を集合として証明する。E[n]の有限性を入力すると、既存の各点の開固定部分群から核の開性が従う。
さらに `krullTopology_mem_nhds_one_iff_of_normal` によって、正規かつ有限次元の中間体Lを選び、
`L.fixingSubgroup ≤ representationKernel E n` を得る。
有限性だけで十分なので、この部分に位数p²や次元2は要求しない。

`FactorsThroughFiniteLevel` は有限中間体Lと「Lの全元を固定するσにはρ(σ)=1」という条件。
これは参照した
[ResidualGaloisRepの有限レベル定義](https://github.com/anthropics/fermats-last-theorem/blob/main/Definitions/Def_GaloisRep_Residual.lean)
と同じ量化の形である。実際の有限群上の行列表示や基底の選択までは構成していない。

`FreyResidualFiniteLevel.lean` の `residual_profile_of_card_sq` は、同じSourceの実際の位数入力から
次元2・開核・有限レベルをまとめる条件付き入口である。既約性を結論に含めていない。

## 5. 検証

回帰では、実在するSource 2の非零2-torsion点について、標準表示でも非零かつ全ガロア元で固定されること、
生成部分加群が非零で安定であることを確認する。この部分加群の真部分性までは主張していない。
また、E[1]の零空間は既約でないことと、有限性が実証できるE[1]で有限レベルが得られることを確認する。
Source 37の次元2・開核・有限レベルの回帰では、有限性または位数公式の引数を保持した。

検証コマンド・結果は [validation-note011.txt](evidence/validation-note011.txt) に記録する。
ルートの公開入口は [RootSmokeNOTE011.lean](evidence/RootSmokeNOTE011.lean) で確認する。

`lake build DkMathTest.FLT.Note011DependencyAudit` は3,150 jobs成功。
本体42宣言と回帰9補題の公理監査、12経路の依存監査が通った。
`lake build DkMath DkMath.FLT DkMath.Lib DkMathTest` は11,539 jobs成功。
ルートsmoke、`lake env lean DkMathTest.lean`、マーカーチェッカー、`git diff --check` も成功した。
新規8モジュールに警告はなく、監査対象の公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
