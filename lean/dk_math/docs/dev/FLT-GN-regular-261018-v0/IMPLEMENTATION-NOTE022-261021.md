# NOTE-022: ファイバーの総和から主イデアルの非零生成元へ

日付: 2026-10-21。標数0の楕円曲線E、代数閉包上の実際の点群、非零自然数nについて

\[
\boxed{\sum_{[n]P=T}P=[n]T},\qquad
\boxed{I_{n,T}\text{ が主}\iff[n]T=O}
\]

を証明した。T∈E[n]のとき、ファイバーイデアルの非零生成元f(n,T)を選び、
同じ関数体内にw(n,T)=f(n,T)/f(n,O)を構成した。分母・分子・商の非零性も証明した。
**付値公式・移動による比例性・Weil対の存在・円分行列式の無条件化はまだ結論していない。**

## 1. 実装と公開入口

| モジュール | 内容 |
| --- | --- |
| `DkMath.Lib.Algebra.FiniteTorsionSum` | 逆元での相殺、四元2-torsionの総和、一般の有限なn倍核の総和 |
| `DkMath.Lib.NumberTheory.EllipticMultiplicationFiber` | 実際の核とファイバーの平行移動全単射、非空・有限・位数n²、総和nT |
| `DkMath.Lib.NumberTheory.EllipticPrincipalPointIdeal` | 整数重み付き主分数イデアル判定、Oを単位イデアルとする整イデアル積の主性判定 |
| `DkMath.Lib.NumberTheory.EllipticWeilFunction` | ファイバーイデアル、主性の必要十分条件、非零生成元、関数体内の非零な商 |
| `DkMath.FLT.FreyWeilFunction` | 同じSourceの曲線への接続。Sourceの指数pと倍写像の指数nは独立 |

本体5モジュール、名前付き公開宣言42個。教科書docstringとimport後の
`#print "file: モジュール名"` を付け、`DkMath.Lib`・`DkMath.FLT`・ルート`DkMath`と
回帰・監査の`DkMathTest`へ配線した。

## 2. 総和で本当に必要なのは四元2-torsion

一般可換群Gの有限なn倍核をsとする。
2P≠0の点は逆元と異なり、Pと−Pの組で総和から消せる。
残るのは2P=0の点だけである。

nが奇数なら、nP=0と2P=0からP=0なので、残る総和も零。
nが偶数なら、G[2]全体がsに入り、残る集合はちょうどG[2]である。
G[2]が四元なら、非零の異なるA,Bを選んで

\[
G[2]=\{0,A,B,A+B\},\qquad \sum G[2]=2A+2B=0
\]

となる。`sum_kernel_eq_zero` はこの一般群の議論を形式化した。
ここにはG[n]の位数n²、素数冪構造、基底選択、Weil対は不要である。
四元性は省略できず、回帰では二元群ZMod 2の全元の総和が非零であることも確認した。

実際の曲線には、既存の `card_torsion_sq E 2` からG[2]の四元性を供給する。
これにより、NOTE-020の素数冪基底や新たな全指数の構造同型を使わずに総和を証明できた。

## 3. ファイバーを同じ点の平行移動として捉える

`fiberSet E n T` は{P | n•P=T}である。
n≠0の全射性から一つのRを取りnR=Tとする。

\[
E[n]\simeq F_{n,T},\qquad Q\longmapsto Q+R,
\quad P\longmapsto P-R
\]

という、点の値を保持する全単射 `fiberEquiv` を作る。
既存の有限核から有限性、位数公式から点数n²、全射性から非空性を供給する。
有限性や位数を新たな仮定として受け取ってはいない。

実際の有限集合について

\[
\sum_{P\in F_{n,T}}P
=\sum_{Q\in E[n]}(Q+R)
=\sum_{Q\in E[n]}Q+n^2R
=nT
\]

を証明した。T∈E[n]という仮定は最後に総和を零へ特殊化するときにだけ必要である。
n=0は有限性を保証できないので、このAPIでは明示的に除いた。n=1は含む。

## 4. 点群と同じ曲線の類群を結ぶ

Mathlibの `Point.toClass` は、非特異点の群からその曲線のアフィン座標環の類群への
単射な加法準同型であり、P=(x,y)を可逆分数イデアル(X−x,Y−y)の類へ送る。
`ClassGroup.mk_eq_one_iff` と `Point.toClass_eq_zero` により

\[
\prod_{i\in s}\mathfrak m_{P_i}^{m_i}\text{ が主分数イデアル}
\iff\sum_{i\in s}m_iP_i=O
\]

を実装した。整数mᵢの負指数は逆分数イデアルである。
これは座標環の類群の定理であり、円分整数環の類群条件を代入したものではない。

Oには単位イデアルを割り当てる `pointIdeal` と、その可逆分数イデアル表示
`pointIdealUnit` を作り、Oを含む点集合にも同じ判定を拡張した。
この規約によりファイバー積からOを除く操作を表せる。
Oをアフィン素点として扱ったわけではなく、無限遠点の付値を導入したわけでもない。

最後に分数イデアルの主性を整イデアルの主性へ戻し、
`isPrincipal_prod_pointIdeal_iff` を得た。
この橋自体には代数閉性・標数0・全類群の自明性を要求しない。
ここでは既存Mathlibの `Point.toClass` の実証明を利用しており、
NOTE-021のDedekind定理をこの主性の橋で新たに証明し直したものではない。

## 5. 非零生成元と商を実際に構成する

`fiberIdeal E n hn T` は、同じファイバーの点イデアルの積である。
前節の同値と総和nTを接続して

```lean
fiberIdeal_isPrincipal_iff :
  (fiberIdeal E n hn T).IsPrincipal ↔ n • T = 0
```

を証明した。従ってT∈E[n]から主性を供給できる。
各点イデアルは非零で、その有限積も非零なので、主イデアルの生成元も非零となる。
`weilNumerator` はこの証明の下で生成元を選び、
`span_weilNumerator` は生成するイデアルが実際の積と一致することを保証する。

`weilFunction` は同じ分数体への包含を通して

\[
w(n,T)=\frac{f(n,T)}{f(n,O)}
\]

を定義する。包含の単射性により分子・分母は関数体内でも非零であり、商も非零。
目標点Oでは同じ非零関数同士の商なのでw(n,O)=1となる。
有限性や主性が不明な枝を1で埋める定義は採用せず、n≠0とnT=0をAPIに残した。

生成元は単元倍の不定性を持つ非標準的な選択である。
零・極の位数、無限遠点での次数、移動の比例定数はこの選択だけからは得られない。

## 6. 実在するSourceによる境界の回帰

`FreyWeilFunctionTest` の19宣言は、既存のSource 2=(4,3,5)の同じ曲線を使う。
非零2-torsion点T=(0,0)の2倍ファイバーは非空で四点、総和は零、積は主であり、
選択した分子は非零で実際の積を生成し、Sourceの候補関数も非零である。
37倍の零ファイバーは1369点で総和零。指数1・Oの単位イデアル・w(1,O)=1も検査した。

さらに同じ全射性で2R=Tとなる実際の点Rを選んだ。
2R≠0、4R=0なので、これは位数4の点である。
Rを2倍ファイバーの目標にすると総和は2R=T≠0となり、ファイバーイデアルも主でない。
従って「ファイバーが四点だから主」という推論や、nT=0の省略はできない。
一つの非零点の点イデアル自体が主でないことも、同じ主性判定で検査した。

## 7. 参照と検証

次のAnthropic実装を参照し、一般群と実際の曲線のproviderを分離した。

- [主分数イデアルと点の総和](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_CoordinateRing_isPrincipal_prod_XYIdeal_zpow_iff.lean): blob `f70f027f91903199d7019d7256810f37e761687a`。
- [逆元相殺と四元2-torsion](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_sum_eq_zero_of_forall_mem_iff_smul_eq_zero.lean): blob `9ef7b6e7a069030c8f12e05baf7d44cb9e9983c4`。
- [Weil関数の定義](https://github.com/anthropics/fermats-last-theorem/blob/main/Definitions/Def_EllipticCurve_WeilPairingFun.lean): blob `87db2103488123818b08bf0d9302badff87ac510`。
- [ファイバーからWeil分子へ](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_valuation_weilNum.lean): blob `74864cced2b6198ce5ee7d72f60cb748f7647cab` を参考に、DkMathの実証明providerへ翻訳した。

参照元に基づく四つのライブラリモジュールにApache-2.0の帰属、元ファイル・blob・変更点と
既存のLICENSE/NOTICEへの参照を保持した。外部未移植providerやP2Mマクロはimportしない。
主性の段階でOを単位元として一様に扱い、有限点部分型への積の組み替えを避けた。
総和は既存の標数0・代数閉包上の点群へ接続するため、任意標数への一般化は今回行っていない。

`Note022DependencyAudit` は42本体宣言・19回帰宣言の公理と13経路の型・opaque本体を検査する。
許可する公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
全射性・有限核・位数公式、逆元相殺、Point.toClass、生成元と非零性の実際の経路を要求する。
Weil対データ・torsion基底選択・外部未移植定理・FLT終点・大域Kummer入力は禁止する。
一般群の補題の監査経路はDkMathの数論層にも依存しない。

最終focused buildは3183 jobs、`lake build DkMath DkMath.FLT DkMath.Lib DkMathTest` は11608 jobsで成功した。
新規モジュールに警告はなく、全体ビルドでは既存の別モジュールのsorry警告5件が再掲された。
実行結果は [validation-note022.txt](evidence/validation-note022.txt)、
ルート入口の再検査は [RootSmokeNOTE022.lean](evidence/RootSmokeNOTE022.lean) に記録した。
ルートsmokeと `lake env lean DkMathTest.lean` の直接検査も成功した。

## 8. 次の境界

有限点の付値公式、平行移動でP+S=Oとなる例外、座標環のノルムの次数による無限遠点の処理が次の課題である。
今回の分子と商は、そのための幾何学的入力として構成した。
付値輸送・比例定数、双加法性・交代性・非退化性・ガロア同変性、`exists_weilPairingData` は未実装。
NOTE-018の円分行列式の結論は、引き続き幾何学的Weil対データを要する条件付き定理である。
