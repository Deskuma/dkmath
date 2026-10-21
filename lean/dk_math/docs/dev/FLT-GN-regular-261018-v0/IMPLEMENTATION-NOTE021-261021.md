# NOTE-021: Weil対へ向けた座標環・一般点・平行移動

日付: 2026-10-21。NOTE-021 §4の最初の幾何学的Coreとして、代数閉体上の楕円曲線の
実際のアフィン座標環のDedekind性、関数体の一般点、点による平行移動の自己同型を実装した。
有限点と座標環の非零素イデアルの対応も証明し、同じFrey Sourceの曲線へ接続した。
**WeilPairingDataの存在、円分行列式の無条件化は未実装である。**

## 1. 公開モジュール

| モジュール | 内容 |
| --- | --- |
| `DkMath.Lib.NumberTheory.EllipticCoordinateRing` | 点イデアルの分類、非特異点の局所単項性、DVR、Dedekind性 |
| `DkMath.Lib.NumberTheory.EllipticFunctionField` | 有限点の座標、実際の一般点、非定数点への代入の単射性、分数体への延長 |
| `DkMath.Lib.NumberTheory.EllipticFunctionFieldTranslation` | 平行移動の引き戻し、逆・合成・恒等・座標作用・忠実性 |
| `DkMath.Lib.NumberTheory.EllipticFunctionFieldPlaces` | 有限点とHeightOneSpectrum、座標環の評価 |
| `DkMath.FLT.FreyWeilGeometry` | 同じSourceの曲線のDedekind性と忠実な関数体平行移動 |

本体5モジュール910行、名前付き公開宣言73個。日本語の教科書docstringを付けた。
import後の `#print "file: モジュール名"` を各新規Leanファイルに保持し、
`DkMath.Lib`・`DkMath.FLT`・ルート`DkMath`、回帰・監査の`DkMathTest`へ配線した。

## 2. 座標環をDedekind整域へ

体F上のWeierstrass曲線Wについて、座標環を

\[
A=F[X,Y]/(W(X,Y))
\]

とする。点(x,y)のイデアルは二つの座標差で生成される。

\[
\mathfrak m_{x,y}=(X-x,Y-y).
\]

`mk_mem_XYIdeal_iff` は、曲線上の点での消滅とこのイデアルへの所属を同値にする。
剰余環がFと同型なので極大であり、X−xが座標環で非零なので零イデアルではない。
代数閉体上では、有限型剰余体がFへ戻ることから、全ての極大イデアルがこの形になる。

局所単項性の核心は、共役y座標を用いた関係式

\[
(Y-y)(Y-\operatorname{negY}(x,y))=(X-x)g(X,Y).
\]

非特異性から偏微分の少なくとも一方が非零である。
これを点での評価を通して局所環の単元へ翻訳すると、左の第二因子またはgが単元となる。
従って極大イデアルはX−xまたはY−yの一方で生成される。
Noether性・非体性と合わせて局所環がDVRとなり、全非零素イデアルへ供給してDedekind性を得る。
零でない素イデアルの極大性には、AがF[X]上の二元基底を持つ有限加群であることを使う。

このCoreは標数0を仮定しない。Dedekind定理では代数閉性と楕円曲線性を仮定する。
単なる任意の平面曲線に同じ結論を主張したものではない。

## 3. 一般点と分数体への延長

既存Mathlibの実際の分数体 `W.FunctionField` を使い、座標環のX,Yの像を
`genericX`・`genericY` とする。座標環の定義関係を関数体へ写すことで曲線方程式が成立し、
楕円曲線性から非特異な実際の `genericPoint` を構成する。

関数体値の非零点Qへの座標代入 `pointHom` は座標環上で定義できる。
しかし分数体へ延長するには、非零分母を零へ送らない単射性が必要である。
`pointHom_injective_of_ne_baseChange` は、Qが定数点でないという仮定から単射性を導く。
核が非零なら、座標環の非零素イデアルは極大なので点イデアルになる。
その二つの座標差が核へ入ることからQの座標がともに定数となり、仮定と矛盾する。
この証明は先に完成した点イデアルの分類を実際に用いている。

`pointPull` はこの単射な代入を `IsFractionRing.liftAlgHom` で延長する。
一般点がどの定数点にも等しくないことは、X−aの座標環内での非零性から証明する。
有限点の座標を返す `Point.xc`・`Point.yc` は無限遠点では便宜上0を返すため、
座標から点を復元する補題には非零性を明示する。

## 4. 平行移動を関数体の自己同型にする

定数点Sについて、一般点Gの移動G+Sは非零であり、どの定数点にも等しくない。
従って前節の単射性を適用でき、

\[
\tau_S^*:F(W)\longrightarrow F(W),\qquad f\longmapsto f(G+S)
\]

を構成できる。座標環上で二つの座標への作用を比較し、分数体の普遍性で延長して

\[
\tau_S^*\circ\tau_T^*=\tau_{S+T}^*,\qquad \tau_0^*=1
\]

を証明した。−Sによる移動が逆となり、`transEquiv` は実際の代数自己同型になる。
`AlgEquiv.trans` の適用順序に合わせ、APIの合成式では右側が
`(transEquiv T).trans (transEquiv S)` になる。

さらにX,Yへの作用が同じならG+S=G+Tなので、一般点を群の消去則で消しS=Tとなる。
`transEquiv_injective` はこの作用の忠実性を与える。
自己同型の対象は関数体である。有限点に極を持つ関数も移動させるので、
アフィン座標環そのものの自己同型とは主張していない。

## 5. 有限点から付値の場所への入口

`placeOf P hP` は有限点Pを座標差の非零素イデアルへ送る。
`placeOf_surjective` と `placeOf_injective` は、代数閉体上で
有限点と `IsDedekindDomain.HeightOneSpectrum` の対応を証明する。
後者では、一方の点で他方の座標差を評価することで両座標の一致を得る。

これは有限点でのDVR・付値へ進む入口であり、付値そのものの輸送を証明したわけではない。
アフィン座標環の場所には無限遠点が含まれない。
Weil関数の因子を論じる前に、無限遠点の付値と有限点の付値を合わせる必要がある。

## 6. 実在するSourceによる回帰と監査

`DkMathTest.FLT.FreyWeilGeometry` の12宣言は、実在する原始ピタゴラスSource 2
(a,b,c)=(4,3,5)の同じ曲線を使う。
座標環のDedekind性、点(0,0)の局所DVR、一般点の非定数性、有限場所の被覆を検査した。
既存の非零2-torsion点を同じ幾何学的点として読み、その移動が非恒等で、
二度合成すると恒等へ戻ること、一般点への作用が実際の群の和であることを証明した。
また、定数点(0,0)への評価が非零のX類を消すため単射でないことを証明した。
これにより、点への評価と関数体の埋め込みの区別も回帰で保持する。

`Note021DependencyAudit` は本体73宣言・回帰12宣言の公理と、12本の選択した
型・opaque本体の依存グラフを検査する。
許可する公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
幾何学Coreの選択経路ではねじれ点表現providerを禁止し、
全選択経路でWeil対データ・外部未移植定理・FLT終点・大域Kummer入力を禁止する。
全リポジトリの既存定理へ拡大した無依存性を主張する監査ではない。

focused buildは3149 jobs、`lake build DkMath DkMath.FLT DkMath.Lib DkMathTest` は11601 jobsで成功した。
新規モジュールに警告はなく、全体ビルドでは既存の別モジュールのsorry警告5件が再掲された。
検証コマンドと結果は [validation-note021.txt](evidence/validation-note021.txt) に記録した。
ルートimportの [RootSmokeNOTE021.lean](evidence/RootSmokeNOTE021.lean) と、
`lake env lean DkMathTest.lean` の直接検査も成功した。

## 7. 参照元とDkMathへの翻訳

次のAnthropic実装を読み、必要な部分を分割・移植した。

- [座標環のDedekind性](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.lean): blob `08c1b731e747c7eab951239a306657dac633d42f`。
- [関数体の引き戻し](https://github.com/anthropics/fermats-last-theorem/blob/main/Definitions/Def_EllipticCurve_FunctionFieldPullback.lean): blob `ce8783a9e9613db1c4c0323ce93fb0d89917ee65`。

外部の未移植providerやP2Mマクロには依存しない。
現在のMathlibのTFAE添字、Dedekindの局所DVR判定、整拡大における極大性のAPIへ合わせた。
有限加群の証拠を明示的な局所providerにし、点イデアル分類を実証明から供給した。
各移植ファイルにApache-2.0の帰属・元ファイル・blob・変更点を記載し、既存のLICENSE/NOTICEを参照する。

## 8. 次の未解決境界

`exists_weilPairingData` はまだ追加していない。
次は無限遠点を含む付値、平行移動による付値輸送、Weil関数とその因子、
双加法性・交代性・ガロア同変性・非退化性を実際の幾何学から供給する必要がある。
その後にNOTE-018の条件付き行列式定理へ接続する。
互換的基底・Tate加群や、一般FLTの終点も今回の結論ではない。
