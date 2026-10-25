# NOTE-032 — 標的三次モデルの明と暗

2026-10-25。branch `dev/FLT-GN-regular-261018-v0`。
開始時HEAD: `04f54ce47a7d79d2e930211b271df27b2ffb01b8`。開始時の作業ツリーはclean。
細かな枝番を追加せず、「同じ固定体から標的三次モデルとその降下まで」を一括実装した。

**明: 同じX_H,Y_HのWeierstrassモデル、係数の一意性、実際の座標環・関数体の単射、
像F_Hと次数|H|、安定核の場合のK係数への降下が確定した。**

**暗: 標的モデルのΔ≠0、全点でのisogeny、標的零成分への輸送は残る。**
一般点の非特異性だけでこの暗部を埋めてはいけない。その理由を尖点三次曲線で形式化した。
005C全体、`hno`、一般Frey既約性、一般FLTの完了とはしない。

## 1. 数学の配置と一般性

Kは標数0の体、EはK上の楕円曲線、kはKの代数閉包、FはEの幾何学的関数体、
HはE(k)内の同じ有限部分群とする。既存の正規化座標和X_H,Y_Hを使い続ける。
F_Hは同じHの平行移動固定体であり、新しい代替核や生成元を入力しない。

| 所有者 | 定理 / 定義 | 今回固定した数学 |
| --- | ---: | --- |
| [QuadraticFixedField](../../../DkMath/Lib/Algebra/QuadraticFixedField.lean) | 1 / 0 | 二次中間拡大の非自明な反射の固定元 |
| [ValuationRationalPolynomial](../../../DkMath/Lib/Algebra/ValuationRationalPolynomial.lean) | 3 / 0 | 既約分子分母、有限値での検出、Bezoutによる分母除去 |
| [ValuationCubicModel](../../../DkMath/Lib/Algebra/ValuationCubicModel.lean) | 1 / 0 | 正則な座標補正による残差の極上界4 |
| [EllipticFiniteKernelReflection](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelReflection.lean) | 9 / 0 | 同じ二関数の反転公式、Oを区別した補正和 |
| [EllipticFiniteKernelPolynomial](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelPolynomial.lean) | 4 / 0 | 有限値の零点、核外正則関数の多項式化、極から次数上界 |
| [EllipticFiniteKernelModel](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelModel.lean) | 19 / 3 | 残差、三次モデル、同じ方程式、非特異な一般点 |
| [WeierstrassCoordinateEvaluation](../../../DkMath/Lib/NumberTheory/WeierstrassCoordinateEvaluation.lean) | 9 / 2 | 任意の拡大体への代入、座標環単射、分数体写像、係数の一意性 |
| [EllipticFiniteKernelModelMap](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelModelMap.lean) | 5 / 2 | 同じモデルの一意性、実際の関数体単射と像・次数 |
| [EllipticFiniteKernelModelDescent](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelModelDescent.lean) | 3 / 1 | 安定核のモデルのガロア固定とK係数降下 |
| [FreyFiniteKernelModel](../../../DkMath/FLT/FreyFiniteKernelModel.lean) | 5 / 2 | 同じSource、同じ直線、同じ実点核への公開入口 |

本体10所有者、59定理・10定義、1149行。
Lib公開宣言には `[DkMath.Lib]` と教科書docstring、各Leanにはimport直後のファイルマーカーを付けた。
LibからFLTへの逆依存はない。公開入口 `DkMath.Lib` / `DkMath.FLT` に登録した。

反転公式・分母除去・極の評価・Y_H∉k(X_H)までは任意の標数を扱う。
反転がY_Hを動かす証明以降は標数0を明示する。2の可逆性だけへの最適化は行っていない。
Hの位数は任意で、素数・奇数とは限らない。安定性は係数降下でだけ必要となる。

## 2. 反射が二次関係の係数を制御する

前回確定した `[F_H:k(X_H)]=2` を使う。
楕円曲線の負写像による関数体自己同型ιについて、実際の有限和を添字P↦−Pで置換し、

```text
ι(X_H) = X_H
ι(Y_H) = −Y_H − a₁ X_H − a₃
```

を証明した。無限遠点Oの便宜的座標0を有限点の反転公式へ代入してはいけない。
Oの一項を除いて有限点を計算し、その一項が残すa₃を復元した。

Y_Hはk(X_H)に属さない。Oでの極位数は3である一方、k(X_H)の非零値は
極位数2の生成元による偶数の付値合同類に入るからである。
標数0でι(Y_H)=Y_Hなら、Y_H=−(a₁X_H+a₃)/2となり、この非所属に矛盾する。

残差を

```text
R = Y_H² + a₁ X_H Y_H + a₃ Y_H − X_H³
```

と置く。Rは同じF_Hに属しιで固定される。二次拡大の固定中間体の次数の塔から、R∈k(X_H)。
自己同型をF_Hへ制限する新しいデータは不要で、周囲のFで固定元の中間体を作って交わりを取った。

## 3. 有理式から多項式へ、そして三次モデルへ

超越的fについて、f−cに零点がないなら、その逆数は全点で正則となる。
既存の「全点正則なら定数」というDkMath定理に戻すとfが代数的となり矛盾する。
従ってfの各有限値cは、実際の点の付値v(f−c)<1で検出できる。
X_HはHで極を持つので、この検出点はHの外にある。

R=p(X_H)/q(X_H)を既約な多項式の比で書く。非定数qには代数閉体k内で根cがある。
その検出点でq(X_H)の値は1未満であり、Rの正則性からp(X_H)の値も1未満となる。
しかしpとqのBezout等式を評価すると、値1の定数1が値1未満になってしまう。
従ってqは定数で、RはX_Hの多項式である。既約性と検出点を仮定のまま残してはいない。

OではX_H−x,Y_H−yが正則である。元の曲線方程式と

```text
Y_H²−y² = (Y_H−y)(Y_H+y)
X_H³−x³ = (X_H−x)(X_H²+X_H x+x²)
```

を比較すると、Rの極は高々4となる。X_Hの極位数は2なので多項式次数は高々2。
この三係数から実際の `kernelModel E H : WeierstrassCurve k` を選び、

```text
Y_H² + a₁ X_H Y_H + a₃ Y_H = X_H³ + a₂' X_H² + a₄' X_H + a₆'
```

を証明した。a₁,a₃は元と同じ。**a₂'=a₂や明示的Vélu係数公式は今回の結論ではない。**
同じ座標を保ったまま係数を構成できることを優先した。

## 4. 座標環の単射から、実際の関数体単射へ

一般のWeierstrassモデルWについて、方程式解x,yへの代入を `AdjoinRoot.lift` で定義する。
xが超越的でy∉k(x)なら、二元基底で書いた任意の座標環元p(x)+q(x)yの像が零となるのは、
p=q=0の場合だけである。これで座標環単射を示し、分数体への実際の代数準同型へ延長した。

この一般定理に同じkernelModelと同じX_H,Y_Hを入れると、

```text
k(kernelModel) ↪ F
image = k(X_H,Y_H) = F_H
[F:image] = |H|
```

が得られる。写像を存在providerとして受け取るのではなく、代入から構成した。
同じ曲線モデルの `kernelModelGenericPoint` も実際のPointとして構成し、Oでないことを証明した。
ただし、これらは全点での群準同型やisogenyをまだ与えない。

## 5. 同じモデルの一意性とK係数への降下

同じX_H,Y_Hが二つのWeierstrass方程式を満たし、a₁,a₃が同じなら、式の差はX_Hの
二次以下の多項式となる。X_Hの超越性で全係数が一致するので、モデルは実際に等しい。
変数変換による同型だけの結論ではない。

Hがガロア安定なら、既存の同じ二関数の半線形不変性から、モデルをσで移した方程式も
同じX_H,Y_Hで満たされる。一意性によりモデル自身がガロア固定となる。
残るa₂',a₄',a₆'それぞれに固定体定理を適用し、実際のK係数モデルと基底変換の等式を得た。
安定性は「核を集合として保存する」条件であり、各核点がK有理である必要はない。

Sourceでは同じ残余直線Lとdim L=1から、方程式・非特異な一般点・関数体単射・像・次数pを公開した。
同じLの安定性があればℚ係数モデルも得られる。Source37では次数37を内部計算した。
Lの存在や安定性自体を新たに結論しない。元の曲線のhratをこの標的へ流用しない。

## 6. 明暗を同じ教科書で検査する

[境界のLean](evidence/Note032QuotientModelBoundary.lean) と
[通常テスト所有者](../../../DkMathTest/Lib/NumberTheory/EllipticFiniteKernelModel.lean) は
ファイルマーカー以外で同じ本体を持つ。

| 明: 実際の楕円曲線と核 | 暗: 一般点情報だけでは足りない例 |
| --- | --- |
| E: y²=x³−x、Q=(1,0)、H={O,Q} | W: y²=x³、x=t²、y=t³ |
| 同じHのモデル方程式、座標環単射、非特異な一般点 | 同じ方程式と非特異な一般点 |
| 同じ固定体への実際の関数体単射、次数2 | [k(t):k(t²)]=2、[k(t):k(t³)]=3 |
| 同じ二元核のモデルのℚ係数降下 | k(t²,t³)=k(t) |
| 自明核では元のEへ戻り、モデルのΔ=64 | WのΔ=0、原点が特異 |

尖点の例は、**今回の有限核モデルが特異だという主張ではない**。
「方程式・非特異な一般点・次数2,3・生成」だけから全体の非特異性を推論する経路の反例である。
実際の有限核商では、元の楕円曲線と平行移動作用に由来する追加の幾何学を使う必要がある。

## 7. 再利用と検証

一般の因子・商スキーム理論や外部模範解答のライブラリ全体を追加せず、
DkMathの点付値、正則関数の定数性、反転、次数の塔、座標環二元基底を接続した。
`WeierstrassCoordinateEvaluation` の座標代入部分は、既存の
`EllipticFunctionField.pointHom` を任意の標的拡大体へ再構成した。
元の模範解答のblob `ce8783a9e9613db1c4c0323ce93fb0d89917ee65` と
Apache-2.0 / NOTICEの由来を同ファイルに保持した。今回は新たな外部コードの取得はしていない。

実施済みの検証:

- `lake build DkMath.FLT.FreyFiniteKernelModel`: 成功、4084 jobs、警告0。新しいLib全所有者を依存として検査。
- `lake env lean .../Note032QuotientModelBoundary.lean`: 12定理・1定義を本体再 elaboration、警告0。
- `lake env lean .../Note032QuotientModelSmoke.lean`: 同じSource37の5定理、警告0。
- 本体69宣言＋境界13宣言＋Source37の5宣言、計87宣言の `#print axioms`。
  依存は標準の `propext / Classical.choice / Quot.sound` の範囲内。
- 禁止構成・外部証明import・docstringとLibマーカー・ファイルマーカー・Lib逆依存・入口登録・
  旧所有者と直前契約の保持・ローカルリンク・`git diff --check` を検査。

入口登録は静的検査である。利用者との分担に従い、今回のフルビルド、ルートビルド、
`lake test` / `DkMathTest` 全体ビルドは実行していない。
[検証記録](evidence/validation-note032-quotient-model.txt)、[構造化証拠](evidence/note032-quotient-model.json)。

## 8. 次に一括して扱う課題

次は「三次モデルを商楕円曲線・isogenyへする」という幾何学の単位となる。
標的Δ≠0、全点での正則延長と加法性、同じHとの点核の一致、係数体上の同変性を結ぶ必要がある。
その後、標的の零成分・還元構造を輸送し、既存のCofixed像からの有理捩れ構成へ接続する。
関数体の次数|H|を点isogenyの存在へ読み替えたり、源の有理捩れ排除を標的へ流用したりしない。
