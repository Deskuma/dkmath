# NOTE-032 アフィンAbel対応から、同じ全点写像の加法性と有理捩れ像へ

2026-10-26 / `dev/FLT-GN-regular-261018-v0`

## 今回の到達点

**既存の全点関数の加法性を証明し、核H・全射性・Galois同変性を持つ実際の点群準同型へ昇格した。Cofixed直線があれば、同じℚ係数標的上に非零有理p捩れ点を得る。**

標数0・奇数位数有限核Hについて、源、核、X_H,Y_H、標的方程式、関数体引き戻し、既存の全点関数を保持した。準同型のtoFunは既存の全点関数そのものである。外部のAbel対応・Picard同値・点準同型・isogeny providerを入力していない。

今回の短い接続は、無限遠点Oの整数係数の補正を許した**アフィンAbel対応**である。Pic⁰の全構成や主因子の次数公式までは実装していない。以下の正確な命題だけで、今回必要な点加法性を導ける。

## 1. 整数重みと可逆分数イデアル

代数閉体k上の楕円曲線Wについて、有限支持因子Dを実際の点群で合計する。

```text
pointSum(D) = ∑ P ∈ support(D), D(P) • P
```

有限点Pには座標差イデアルI(P)を、Oには単位イデアルを対応させ、

```text
I(D) = ∏ P ∈ support(D), I(P) ^ D(P)
```

を可逆分数イデアルとして保持する。負の重みには分数イデアルの逆元を使用する。

既存の`EllipticPrincipalPointIdeal`は、Mathlibの単射な加法準同型`Point.toClass`により

```text
I(D)が主 ⇔ pointSum(D)=O
```

を供給する。ここで必要なのは、これを前回の全点付値による主因子の定義へ接続することである。

## 2. 同じ付値から同じ主イデアルを復元する

`DedekindFractionalValuation`では、任意のDedekind整域Rとその分数体Fに対して次を証明した。

- 非零分数イデアルは全ての高さ1素点での整数指数で決まる。
- 主分数イデアル(f)の指数は、同じfの正規化付値の負の対数である。

後者はf=a/bと表示して、分子・分母の素イデアル指数の差を付値の商に一致させる。

`WeierstrassDivisorAbel`では、同じモデルの有限点と高さ1素点の全単射を証明し、I(D)の有限点Pでの指数がD(P)であることを証明した。代数閉性が全てのアフィン素点を実際のk点に戻す段階で必要になる。

D=div(f)なら、I(D)と(f)は全アフィン素点で同じ指数を持つ。従ってI(D)=(f)であり、

```text
Dが実際の主因子 ⇒ pointSum(D)=O
```

を得る。無限遠点は点群でOなので、この方向ではOの係数の値は総和に寄与しない。

## 3. 無限遠の係数補正という接続

逆にpointSum(D)=Oなら、I(D)は主分数イデアルであり、実際の非零生成関数fを選べる。有限点ではその位数がD(P)に一致する。残る一点Oに対して

```text
n = −log(v_O(f)) − D(O)
```

を置けば、D+n[O]は全点でfの主因子となる。公開した双方向形は

```text
(∃ n : ℤ, D+n[O]が実際の主因子) ⇔ pointSum(D)=O
```

である。これは`exists_principal_correction_iff`としてカーネル検証されている。

**補正nが−deg(D)であることを今回の命題に含めていない。** 主因子の次数公式や点群とPic⁰の全同値を仮定した証明ではない。また、任意の付値族に対し任意の有理関数の位数が有限支持となるという命題へ一般化していない。因子は引き続き有限支持型であり、生成関数の非零性も保持している。

## 4. 同じ点関数の加法性

`WeierstrassPrincipalPushHom`は、代数閉体上の楕円曲線W,Vの間の点関数gについて、次の一般定理を証明した。二つの係数体は異なっていてもよい。

```text
g(O)=O
かつ、有限支持主因子のgによる押し出しが主因子
⇒ g(P+Q)=g(P)+g(Q)
```

証明で使う有限支持因子はD=[P]+[Q]−[P+Q]である。点の総和はOなので、前節によりD+n[O]が主因子になる。これを押し出した主因子の点の総和もOであり、

```text
g(P)+g(Q)−g(P+Q)+n•g(O)=O
```

を得る。最後の項はg(O)=Oから消える。P,Q,P+QがOとなる場合も同じ証明に含む。全射性やファイバー位数は、この一般定理の仮定ではない。

この接続により、無限遠での次数公式を待たずに前回の主因子輸送を点加法性へ運べた。

## 5. 同じ有限核と同じSourceへ適用する

`EllipticFiniteKernelHom`は、源の基底変換モデルの`modelPointValuation`と既存`pointValuation`を一致させ、前回の同じ`kernelDivisorPush_isPrincipal`を適用する。

| 公開API | 結果 |
| --- | --- |
| `oddKernelPointMap_add` | 既存全点関数の加法性 |
| `oddKernelPointHom` | 同じtoFunを持つ加法準同型 |
| `oddKernelPointHom_ker` | 群準同型の核が正確に同じH |
| `oddKernelPointHom_surjective` | 同じ準同型の全射性 |
| `oddKernelQuotientEquiv` | 同じ点群の商E/Hと同じ標的点群の加法同型 |
| `descendedKernelPointHom` | 既存K係数モデルへ移した同じ準同型 |
| `descendedKernelPointHom_equivariant` | 標準実点Galois作用との同変性 |

`FreyFiniteKernelHom`は同じSource、一次元残余直線L、実点核H、既存ℚ係数標的へ接続する。pは素数、p≠2という条件を保持する。

既存`EllipticCofixedImage` / `FreyCofixedImage`の条件付き定理に、今回内部構成した準同型・核一致・Galois同変性を供給した。これにより

```text
IsCofixedOn(ρ,L)
⇒ ∃ P∉L, ∃ R∈同じℚ係数標的,
     p•R=O ∧ R≠O ∧ baseChangePoint(R)=既存の同じ降下点関数(P)
```

が、写像を外部入力にせず成立する。準同型のE[p]への制限の像の位数もpと証明した。Cofixed直線自体の存在を結論しているわけではない。

## 模範証明との対応と選択理由

ローカルに保持された[模範証明blob](https://api.github.com/repos/anthropics/fermats-last-theorem/git/blobs/fa5eda1fdc857b6445c21720c78805e7ecded543)の、主因子保存→Pic⁰押し出し→種数1の点群との同値→同じ点関数との一致、という経路を再確認した。Git blobハッシュも照合する。

DkMathには既に`Point.toClass`を用いた点イデアル積の主性判定があった。この既存資産から、全Picard理論を整備する経路と、Oの係数補正を使って必要な加法性を直接取り出す経路を比較した。今回の点関数はOを保つため、後者を選んだ。外部証明ライブラリはimportせず、既存DkMathとMathlibの分数イデアル分解から新しい証明を組み立てた。

## 検証

本体5所有者、34定理・8定義、551行。対象テスト9定理、Source37の5定理。教科書docstring、Lib昇格マーカー、import直後のファイルマーカーを付け、既存のLib・FLT・テスト入口へ登録した。

対象テストは同じy²=x³−x、非巡回のE[3]（位数9）、非零2捩れ点R=(−1,0)を用いる。任意の二点の加法性、実際の群準同型の核、商群同型の全単射性、既存ℚモデルの加法性、既存の非零Weil主因子の点総和、非零点差の非主性、無限遠補正付き加法関係を確認した。さらに同じ像から非零有理2捩れ点を得た。

Source37の5定理では、既存点関数の加法性、核H、同変性、37捩れ像の位数37、Cofixedからの同じ標的の非零有理37捩れを確認した。

- `./lean-build.sh DkMath.FLT.FreyFiniteKernelHom`
- `./lean-build.sh DkMathTest.Lib.NumberTheory.EllipticFiniteKernelHom`
- Source37の直接Lean検証。
- 56宣言の`#print axioms`監査。
- 禁止構文・外部証明import・Lib依存方向・docstring・昇格マーカー・ファイルマーカー・入口登録・既存所有者保持・差分空白の検査。

[evidence](evidence/note032-abel-hom.json)と[検証記録](evidence/validation-note032-abel-hom.txt)に結果を残す。フルビルド・全testは今回実行していない。

失敗と修正: 分数イデアルの分解定理には分数体引数を明示した。`Points E`と元の幾何学的点型の違いにより付値の書き換えが失敗した箇所では、型を明示した等式の合成を使った。Pointの加法群には古典的等号判定を所有者固有のlocal instanceで供給し、重複import時の名前衝突を避けた。

## 残る境界

今回の結果は、同じ座標で定義された点群準同型、正確な核、全射性、商群同型、Galois同変性、有理p捩れ像までである。スキーム射としてのisogenyやスキーム商の構成は結論に含めていない。

構成した標的の整数係数モデル、Δ・c₄による局所還元保持、零成分輸送、そこでの算術的排除は未完了である。**元のSourceの曲線の有理捩れ排除を、異なる標的曲線へ適用してはならない。** 一般hno・Frey残余既約性・一般FLTの新たな無条件証明は結論していない。

次の数学的境界は、今回構成した標的の局所・整数モデルを整え、非零有理p捩れ像に対する排除へ進めることである。
