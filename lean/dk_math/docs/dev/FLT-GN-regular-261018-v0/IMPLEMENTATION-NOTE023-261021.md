# NOTE-023: 同じWeil分子と商の有限点付値

日付: 2026-10-21。NOTE-022で構成済みの分子f(n,T)と商w(n,T)について、
非零自然数n、T∈E[n]、有限点P≠Oの下で

\[
\boxed{\operatorname{ord}_P f(n,T)=\mathbf1_{[n]P=T}},\qquad
\boxed{\operatorname{ord}_P w(n,T)=\mathbf1_{[n]P=T}-\mathbf1_{[n]P=O}}
\]

を証明した。同じ曲線の座標環のDedekind性、実際の有限場所、既存の生成イデアル等式を接続している。
**ノルム次数・無限遠点・平行移動による付値輸送・Weil対の存在は今回の結論には含めない。**

## 1. モジュールと公開入口

| モジュール | 内容 |
| --- | --- |
| `DkMath.Lib.NumberTheory.EllipticPointIdealValuation` | 相異なる点イデアルの積を生成する任意の元の付値、生成元の選択によらない一致 |
| `DkMath.Lib.NumberTheory.EllipticWeilValuation` | 実証明によるDedekind性の供給、有限点付値と整数位数、既存の分子と商への公式 |
| `DkMath.FLT.FreyWeilValuation` | 前章の同じSourceの分子・候補関数への接続 |

本体3モジュール、名前付き公開宣言15個。日本語の教科書docstringとimport後の
`#print "file: モジュール名"` を付けた。
`DkMath.Lib`・`DkMath.FLT`・ルート`DkMath`と、回帰・監査の`DkMathTest`へ配線した。

## 2. 重複度1を素イデアルの二乗から判定する

座標環AがDedekind整域であるとする。点集合sについて

\[
(r)=\prod_{Q\in s}\mathfrak m_Q
\]

を満たす任意のrを取る。Oの寄与は、前章と同じ単位イデアルという規約である。
各点イデアルは非零で、その積も非零なのでr≠0となる。
有限点Pの場所vで、Qのイデアルがv以下ならQ=Pである。
この事実は、極大イデアルの包含から等号を得て、NOTE-021の `placeOf_injective` で点を復元して示す。

P∈sなら、積からPの一因子を取り出すことによってr∈vを得る。
もしr∈v²なら、イデアルの整除式で非零のvを一つ消去すると

\[
v\mid\prod_{Q\in s\setminus\{P\}}\mathfrak m_Q
\]

となる。vの素性から右辺のある因子がv以下となり、その点はPに等しい。
しかしPは残りの集合から除かれているので矛盾する。
従ってr∈vだがr∉v²であり、重複度はちょうど1である。

P∉sなら、r∈vと仮定した時点で同じ素性の議論がP∈sを強制するので矛盾する。
この場合の重複度は0となる。

`intValuation_of_span_eq_prod` はこの議論を、実際の整数付値の不等式

\[
v(r)\le\exp(-1),\qquad v(r)\not\le\exp(-2)
\]

へ結び付け、離散的な整数指数が−1であることを証明した。
相異なる点を一度ずつ含むFinsetであることが重要で、重複を持つ積に同じ公式を無条件では適用しない。

## 3. 乗法的付値と整数位数の符号を区別する

Mathlibの付値は `WithZero (Multiplicative ℤ)` に値を取り、

\[
v_P(f)=\exp(-\operatorname{ord}_P(f))
\]

という規約を持つ。従って一重零点はexp(−1)<1、一重極はexp(1)>1に対応する。
`finitePointValuation` は、同じ有限点の `HeightOneSpectrum.valuation` を同じ関数体上で使う。
座標環のDedekind性はNOTE-021の実証明から供給し、追加の環構造仮定として受け取らない。
この付値と整数位数の一般部分は標数0を要しない。既存のWeil関数への適用部分は標数0の範囲である。

`finitePointOrder P hP f hf` は−log(v_P(f))と定義する。
hP:P≠Oとhf:f≠0を明示し、無限遠点や零関数の位数を便宜的な整数で埋めない。
`finitePointValuation_ne_zero` からlogの商の法則の条件を供給し、

\[
\operatorname{ord}_P(f/g)=\operatorname{ord}_P(f)-\operatorname{ord}_P(g)
\]

を証明した。

## 4. 既存の分子・商をそのまま測る

`span_weilNumerator` は

\[
(f(n,T))=I_{n,T}=\prod_{[n]Q=T}\mathfrak m_Q
\]

を与える。この等式を一般の点イデアル積の補題へ渡し、
`valuation_weilNumerator` で

\[
v_P(f(n,T))=\begin{cases}\exp(-1)&[n]P=T,\\1&[n]P\ne T\end{cases}
\]

を証明した。前章の主性証明や生成元を、別の入力に置き換えていない。
`valuation_weilFunction` は既存の商の定義と付値の商の法則から、二つの値の比を与える。
最後に `order_weilNumerator`・`order_weilFunction` が整数値の指示関数の公式を得る。

生成元の選択の不定性は、`intValuation_generator_independent` で扱った。
二つの元が同じ点イデアル積を生成すれば、全ての有限点で付値が一致する。
これは任意の生成元に対する定理であり、選択された一つの分子だけに限らない。
有限点の付値一致だけから、その比が定数だと結論する定理は追加していない。

## 5. 実在するSourceでの回帰

`FreyWeilValuationTest` の20宣言は、既存のSource 2=(4,3,5)の同じ曲線を用いる。
非零2-torsion点T=(0,0)と、前章の実際の点Rで2R=Tとなるものを使う。

- Rではf(2,T)が一重に消え、f(2,O)は消えない。商の位数は+1。
- Tでは2T=O≠Tなので、f(2,T)は消えず、f(2,O)が一重に消える。商の位数は−1。
- 全射性から2Q=Rとなる実際のQを取り、Q≠O、R≠Tを証明する。Qは両ファイバーの外で、商の位数は0。
- 目標Oなら分子と分母が相殺される。指数1と37倍の零点目標でも位数0を検査した。
- 別の元rが同じ実際のファイバーイデアルを生成するとき、Rでの付値が既存の分子と一致することも検査した。

測定する分子・商の非零性は前章の実証明から供給した。
P=Oでの測定や大きな多項式の数値展開は行っていない。

## 6. 参照元・翻訳・監査

次のAnthropic実装を読み、現在のMathlibとDkMathの既存APIへ翻訳した。

- [分子の付値](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_valuation_weilNum.lean): blob `74864cced2b6198ce5ee7d72f60cb748f7647cab`。
- [商の付値](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_valuation_weilFun.lean): blob `b3f224d0557e987b11afe147aa507cd7fa5837c9`。

二つのライブラリファイルにApache-2.0の帰属、元ファイル・blob・変更点、既存のLICENSE/NOTICE参照を保持した。
P2Mマクロや外部未移植providerはimportしない。
前章の `pointIdeal` と `placeOf` の一致を明示し、一般の生成元の測定を分子の構成から分離した。

`Note023DependencyAudit` は15本体宣言・20回帰宣言の公理と、13経路の型・opaque本体を検査する。
許可する公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
素イデアル積・非零因子の消去・二乗への所属判定・場所の単射性、実際のDedekind性と生成イデアル等式、
非零性とlogの商の法則を、対応する経路で要求する。
一般の点イデアル付値の経路ではDkMathのtorsion表現providerも禁止する。
全選択経路でWeil対データ・torsion基底選択・外部未移植定理・FLT終点・大域Kummer入力を禁止する。

最終focused buildは3187 jobs、`lake build DkMath DkMath.FLT DkMath.Lib DkMathTest` は11613 jobsで成功した。
新規モジュールに警告はなく、全体ビルドでは既存の別モジュールのsorry警告5件が再掲された。
検証結果は [validation-note023.txt](evidence/validation-note023.txt)、
ルート入口は [RootSmokeNOTE023.lean](evidence/RootSmokeNOTE023.lean) に記録した。
ルートsmokeと `lake env lean DkMathTest.lean` の直接検査も成功した。

## 7. 次の境界

NOTE-024に分けたノルム次数と局所付値の総和の対応、無限遠点に関係する次数公式、
平行移動でP+S=Oとなる例外を含む付値輸送は未実装である。
同じ零点・極から比例定数を得る段階、双加法性・交代性・ガロア同変性・非退化性も後続となる。
`exists_weilPairingData` と円分行列式の無条件化は今回証明していない。
