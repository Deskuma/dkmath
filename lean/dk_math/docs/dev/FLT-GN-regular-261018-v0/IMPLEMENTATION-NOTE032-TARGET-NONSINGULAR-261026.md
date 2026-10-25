# NOTE-032 — 奇数核の三根分離と標的非特異性の一括完了

2026-10-26 JST。branch `dev/FLT-GN-regular-261018-v0`。
開始時HEADは `cadb45a294d7c0a6920aa9fa60e9fed392417b8a`、作業ツリーはclean。
内部の枝番は追加せず、有理式・有限ファイバー・軌道計数・三根分離・標的楕円性・Source入口をまとめて実装した。

**標数0の楕円曲線と奇数位数の同じ有限核Hについて、同じkernelModelのΔ≠0を証明した。**
三つの像の分離と標的IsEllipticを外部から受け取る必要はなくなった。
同じ全点関数の零ファイバーHも、この二つの未供給入力なしに使える。
同じ安定核から降下したK係数モデルも楕円曲線となる。

ただし全点関数はまだ加法群準同型ではない。従ってisogeny、AddMonoidHom.ker、
整数係数モデル、局所還元と零成分の輸送、一般hnoを完了とはしない。

## 1. 更新後の状況

以下の標的非特異性の行は、標数0・奇数位数H（Sourceでは素数p≠2）を対象とする。
偶数核に対する新しい非特異性定理は今回供給していない。

| 数学的部品 | 更新後の状態 |
| --- | --- |
| 同じ有限核・固定体・同じX_H,Y_H | 既存の同じ構成を保持 |
| 極・次数・F_H=k(X_H,Y_H) | 既存の証明を再利用 |
| 同じWeierstrass方程式 | 既存の同じモデルを保持 |
| 三つの2捩れ像の分離 | **奇数位数Hで証明済み** |
| 同じ標的のΔ≠0、IsElliptic | **奇数位数Hで証明済み** |
| K/ℚ係数モデルへの降下 | 既存の降下に、同じモデルの楕円性を追加 |
| 同じ全点関数 | **奇数位数Hで標的IsEllipticの外部入力を除去** |
| 同じ全点関数の零ファイバー=H | **奇数位数Hで外部IsElliptic入力なしに証明済み** |
| 実点の加法群準同型φ | 未構成。全点関数の加法性が残る |
| ker φ=H | 群準同型の核としては未供給。関数の零ファイバーとの区別を保持 |
| φのガロア同変性 | 未供給 |
| 整数係数、局所還元、零成分輸送 | 未供給 |
| 一般hno | 未完了 |

## 2. 実装所有者

| 所有者 | 定理 / 定義 | 内容 |
| --- | ---: | --- |
| [StrictFiberCardinality](../../../DkMath/Lib/Algebra/StrictFiberCardinality.lean) | 1 / 0 | 一つの小さいファイバーを利用する厳密な総数上界 |
| [EllipticFiniteKernelRationalFiber](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelRationalFiber.lean) | 7 / 0 | 元のxの有理式、相対次数、分子分母次数、有限ファイバー多項式 |
| [EllipticFiniteKernelTwoTorsion](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelTwoTorsion.lean) | 5 / 0 | 奇数核と2捩れの交わり、xファイバー計数、2捩れ像の単射性 |
| [EllipticFiniteKernelNonsingular](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelNonsingular.lean) | 6 / 1 | 実際の三点、同じ標的Δ≠0・楕円性、K係数楕円性、全点関数と零ファイバー |
| [FreyFiniteKernelNonsingular](../../../DkMath/FLT/FreyFiniteKernelNonsingular.lean) | 5 / 1 | 同じSource・直線・実点核への接続とℚ係数楕円曲線 |

本体5所有者、24定理・2定義、567行。
Lib公開宣言には `[DkMath.Lib]` と教科書docstring、各Leanにはimport直後のファイルマーカーを付けた。
既存の座標和・モデル・評価や証明は変更せず、Libから研究層への逆依存も追加していない。

一般性は次の通り。

- Kは標数0の体、kはKの代数閉包、Eは同じK上の楕円曲線、Hは同じE(k)内の有限部分群。
- 有理式と有限ファイバーの上界にはHの奇数性を要求しない。
- 三根分離と標的非特異性では `Odd (Nat.card H)` を明示する。
- 素数位数、巡回性、生成元、奇数核の代表集合は不要。位数9の全3捩れ核も扱える。
- ガロア安定性はK係数への降下でだけ保持する。各核点の個別固定は要求しない。
- Sourceでは同じ一次元直線Lを保持し、p≠2と位数pから奇数性を内部供給する。

## 3. 反転固定体へ戻し、同じX_Hの有理式を得る

FをEの幾何学的関数体とする。自明核の正規化二関数は元の一般座標x,yへ戻る。
既存の次数公式を自明核へ適用して `[F:k(x)]=2` を得た。
反転はxを固定し、標数0ではyを実際に動かす。
従って既存の二次固定体定理から、反転固定元はk(x)へ戻る。
特に同じX_Hはk(x)に属する。

前回の `[F:k(X_H)]=2|H|` と次数の塔から

```text
[k(x):k(X_H)] = |H|
```

となる。非零因子2を実際に消去し、次数を追加providerにはしない。

xの超越性による `RatFunc.algEquivOfTranscendental` でk(x)をk(t)へ実現し、
同じX_Hに対応するr∈k(t)を選ぶ。中間体のmapによるrelfinrankの保存と、
MathlibのRatFuncの次数公式を使うと

```text
X_H = r.num(x) / r.denom(x)
max(deg r.num, deg r.denom) = |H|
```

が得られる。別のVélu座標や明示的係数公式へ置き換えていない。

## 4. 関数体次数を、実点の有限ファイバーへ接続する

有限値cに対し、多項式

```text
p_c(T) = r.num(T) − c r.denom(T)
```

を作る。r.denom(x)はxの超越性から非零、X_Hも非定数なのでp_cは非零。
また `deg p_c ≤ |H|` である。

核の外の実点Pで `kernelXAt(P)=c` なら、前回の評価定理から
`v_P(X_H−c)<1` となる。元のxは有限点Pで正則なのでr.denom(x)も正則であり、

```text
p_c(x) = (X_H−c) r.denom(x)
```

の付値は1未満となる。
一般xと実点のxc(P)の局所合同を多項式評価へ運ぶと、p_c(x)は定数p_c(xc(P))へ合同。
非零定数の付値は1なので、結局p_c(xc(P))=0である。

ここで `r.denom(xc(P))≠0` を追加の仮定にはしていない。
分母を払った恒等式を先に使い、その後に正則評価を行うためである。
従って同じ有限値cへ移る**相異なるx座標の集合**Tは、非零多項式p_cの根の集合へ入り、

```text
|T| ≤ deg p_c ≤ |H|
```

となる。これは関数体次数から実点計数への、前回未接続だった部分である。

## 5. 半軌道を選ばず、全軌道と一つの厳密ファイバーで分離する

異なる非零反転固定点P,Rが同じ標的x値へ移ると仮定する。
奇数位数Hの反転固定点はOだけである。実際、加法位数は2と|H|の両方を割る。
従ってP,RはHの外にあり、二つの軌道P+H,R+Hも互いに素である。
もし両軌道に共通点があればP−R∈Hであり、これも反転固定点なのでP=Rとなってしまう。

二つの軌道の和集合Sは2|H|点を持ち、Oを含まない。
H移動不変性から全て同じX_H値cを持つ。TをSのx座標の像とすると、前節で|T|≤|H|。

一方、同じx座標を持つ有限点は同じ点か互いの負なので、各xファイバーは高々2点。
Pは反転固定点であるため、x=xc(P)のファイバーは高々1点となる。
ファイバーの個数を足し合わせると、ここで厳密な不等式が得られる。

```text
2|H| = |S| < 2|T| ≤ 2|H|
```

矛盾である。従って同じX_Hは、核の外の反転固定点を分離する。

[模範解答の半軌道計数](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_veluX_oddOrderSummingSet_injOn_psi2Sq_roots.lean)
の「像が一致すれば次数より多くの根ができる」という核心を、DkMathの既存次数と実点評価で再構成した。
参照したGit blobは `7d20d1868f13706680f16addb3fdaaeb58be9c51`。
今回は巡回生成元や半軌道の代表を選ぶ代わりに、全軌道と一つの厳密ファイバーを用いた。
同所有者にはAnthropicの著作権・Apache-2.0・既存LICENSE/NOTICEへの参照を保持した。
前回取得済みの固定ソースを再読し、blobと照合した。新たな外部証明importは追加していない。

## 6. 三つの実点から、同じ標的のΔ≠0へ

元のEの2捩れ三次式は、EのΔ≠0と2≠0から相異なる三根を持つ。
代数閉体k上でその三根を実際に取り、Mathlibの
`Point.isRoot_twoTorsionPolynomial_iff` で同じE(k)の非零2捩れ点へ持ち上げた。
点のx座標の相異性を保つので、この三点は相異なる。

奇数位数Hには非零2捩れ点が入らないため三点は全てHの外にある。
前節で三つの特殊化x値が互いに異なることが証明された。
前回の `kernelAt_twoTorsion_root` でこれらは同じ標的三次式の根となり、
前回の三根判定へそのまま接続して、同じkernelModelのΔ≠0が確定する。

このIsEllipticを内部で供給して `oddKernelPointMap` を構成した。
源の各点は、HならO、Hの外なら同じ二つの特殊化値からなる非特異点へ移る。
零ファイバー=HとH軌道不変性も、標的楕円性の外部入力なしで利用できる。
関数の加法性はこの計数からは結論していない。

同じ安定核のK係数モデルについては、既存の基底変換の等式と判別式のmap公式を使い、
そのΔが零なら代数閉包モデルのΔも零になるという矛盾で楕円性を証明した。

## 7. Source入口と指数37

同じSource・直線L・実点核pointSubgroupを保持した。
Lの一次元性から位数p、p≠2から奇数性を供給して、同じ `residualKernelModel` の
Δ≠0とIsEllipticを証明した。
核の外の任意の実点でのNonsingularも内部供給する。

新入口 `residualOddKernelPointMap` は、標的IsEllipticの追加入力を持たない。
零ファイバーは同じpointSubgroupである。安定直線なら、同じモデルに基底変換で等しい
ℚ係数の楕円曲線が存在する。

[指数37の検査](evidence/Note032TargetNonsingularSmoke.lean) では、同じSource37と同じLについて、
判別式、楕円性、全実点の非特異性、全点関数の零ファイバー、安定時のℚ係数楕円曲線を確認した。
分離やIsEllipticを仮定として受け取らず、Sourceや直線そのものの存在は入力のままである。

## 8. 具体例と検証

[通常テスト](../../../DkMathTest/Lib/NumberTheory/EllipticFiniteKernelNonsingular.lean) と
[独立境界検査](evidence/Note032TargetNonsingularBoundary.lean) は、マーカー以外で同じ本体を持つ。
同じ実曲線y²=x³−xの全3捩れ核E[3]を使い、位数9と奇数性を内部供給した。
巡回生成元や素数位数を要求しない例である。

- 同じ9点核の標的Δ≠0と、実際に分離した三つの2捩れ像。
- 同じ有理式の分子分母最大次数9と、同じ有限ファイバーの相異なるx座標の上界9。
- 同じ全3捩れ核のガロア安定性と、同じℚ係数標的のIsElliptic。
- 標的IsElliptic入力なしの全点関数、正確な零ファイバー、同じH軌道不変性。
- 従来の二元核には今回の奇数条件を供給できないこと。
  これは偶数核の標的が特異という主張ではない。

実施した検証:

- `lake build DkMath.FLT.FreyFiniteKernelNonsingular`: 成功、4094 jobs、警告0。
- 独立境界Lean: 10定理・1定義、成功、警告0。
- Source37のLean: 5定理、成功、警告0。
- 本体26宣言＋境界11宣言＋Source37の5宣言、計42宣言の公理監査。
  依存は `propext / Classical.choice / Quot.sound` の範囲内。
- 禁止構成・外部証明import・Lib逆依存・教科書docstringと昇格マーカー・ファイルマーカー・
  入口登録・旧所有者と直前契約の保持・ローカルリンク・JSON・差分の空白を検査。

入口はDkMath.Lib、DkMath.FLT、DkMathTestへ登録し、静的に確認した。
利用者との分担に従い、フル/ルートビルド、`lake test`、DkMathTest全体ビルドは実行していない。
[検証記録](evidence/validation-note032-target-nonsingular.txt)、[構造化証拠](evidence/note032-target-nonsingular.json)。

次の数学的単位は、構成済みの同じ全点関数を加法群準同型・有理isogenyへ接続することである。
整数係数モデルと局所還元・零成分輸送は、その後も別に評価する。
