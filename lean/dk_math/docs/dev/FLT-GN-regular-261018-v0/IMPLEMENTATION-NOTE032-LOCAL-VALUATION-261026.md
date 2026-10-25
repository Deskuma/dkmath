# NOTE-032 全点関数と引き戻しの局所付値を一致させる

## 1. 結果

同じ奇数核H、同じ二座標、同じ標的モデル、同じ全点関数φ、同じ関数体引き戻しιについて、
全ての源の点Pと全ての標的関数gに対して

\[
 v_P(\iota g)=v_{\phi(P)}(g)
\]

を証明した。双方は正規化された付値であり、付値環の一致だけではない。
P∈Hの無限遠像もP∉Hの有限像も含む。零関数も付値の等式に含む。

前回の軌道積を同じ標的関数体へ降ろしたg_fについても、f≠0なら

\[
 \operatorname{ord}_{\phi(P)}(g_f)
   =\sum_{Q\in H}\operatorname{ord}_{P+Q}(f)
\]

が全点で成立する。局所倍率1や場所の対応を外部providerから受け取らない。
内部枝番は追加せず、有限像・局所倍率・無限遠像・全点公式・Source接続をまとめた。

| 数学的部品 | 判定 |
|---|---|
| 同じ有限像点での座標環全体の評価合同 | 完了 |
| 同じ引き戻しと有限像点の局所中心の一致 | 完了 |
| 局所位数の共通の正整数倍率e_P | 完了 |
| CRTによる同じ源の軌道の局所パラメータ | 完了 |
| 軌道積を使ったe_P=1の内部証明 | 完了 |
| H上の極位数2,3から無限遠付値との正確な一致 | 完了 |
| 全点での付値一致・軌道積の標的位数公式 | 完了 |
| 主因子の大域的押し出しと加法性 | 未完了 |
| isogeny・有理像のp捩れ性・整数モデル・零成分輸送・hno | 未完了 |

## 2. 有限像点の中心を固定する

標的は既に代数閉包k係数なので、係数体を再び代数閉包へ拡大しない。
`WeierstrassFinitePlace`は実際のモデルWの座標環上に、有限点Tの座標差の素イデアルと
その評価準同型を構成する。評価の核は正確にこの素イデアルである。
同じモデルのOには、既存のノルム次数による無限遠付値を割り当てる。

P∉Hなら、前回の有限評価によりX_H,Y_Hは実際のφ(P)の二座標に合同。
二変数多項式の評価に沿って合同を延長すると、任意の座標環元bに対して
ι(b)はφ(P)でのbの評価値に合同となる。
従ってφ(P)の素イデアルの元はPで消え、その外の元はPで単元になる。
ここで使うιとφは、構成済みの`kernelModelPull`と`oddKernelPointMap`そのものである。

## 3. 局所倍率を一度保持し、次に1と証明する

`DiscreteValuationPullback`は一般のDedekind環と体の埋め込みを扱う。
局所中心を保つ場合、素イデアル冪の元の付値上界を輸送し、局所環の分母表示で
分数体へ延ばす。元と逆数の両方に適用すると局所単元は付値1へ写る。

標的の一様化元πを取りe=−log(v_P(ιπ))とすると、eは正整数。
非零gに対してgπ^{log(v_T(g))}は単元なので

\[
 \operatorname{ord}_P(\iota g)=e\operatorname{ord}_T(g)
\]

となる。eはPに依存してよいが、gごとに選び直すものではない。

次にe=1を内部供給した。P∉HならP+Q (Q∈H)は全て有限点で、互いに異なる。
その有限個の素イデアルは異なる極大イデアルであり、それぞれの二乗も互いに素。
`DedekindLocalParameter.exists_parameter`は中国剰余定理で、一点では一様化元に、
他の点では1に、各素イデアルの二乗を法として合同な座標環元aを作る。
従ってaの位数はPで1、他の指定点では0となる。
素イデアル自体が主であることや、類群が自明であることは仮定しない。

aを源の関数fと見れば、前回の軌道積N_H(f)のPでの位数は1。
既存の`kernelModelNorm`により、この軌道積は同じ標的関数g_fの引き戻しである。
先の倍率公式から1=e ord_T(g_f)。正整数eは1を割るためe=1が確定する。
`EllipticFiniteKernelUnramified`はこの証明を使い、有限像点で付値そのものの一致を得る。
この所有者名の「不分岐」は、この全点関数・引き戻しの正規化付値比較を指し、
スキームのétale射の構造体を構成したという意味ではない。

## 4. 核上の無限遠像も閉じる

H上では既存のX_H,Y_Hの付値がそれぞれexp(2),exp(3)。
`WeierstrassPolePullback`は、一般のWeierstrass座標代入に対して、これらの付値と
非零定数の付値1だけから、同じモデルの無限遠付値との一致を証明する。

座標環の任意の元をp(x)+q(x)yと書くと、二項の極位数は
2 deg pと2 deg q+3である。偶数と奇数なので非零の二項の最高値は相殺しない。
これは既存の二次ノルムの次数公式と一致し、無限遠付値の正規化も一致する。
分数表示で関数体全体へ延ばす。

`kernelModelPull_valuation_of_mem`はこの一般定理へ既存の極位数2,3を入力する。
全点付値`kernelTargetValuation`で有限像と無限遠像を合わせたのが
`kernelModelPull_valuation_all`である。
`kernelModelNorm_order_all`は、同じ引き戻しの軌道積等式と、前回の源の位数公式を
この付値比較へ接続する。大域的なファイバーの構成はこの証明では使わない。

## 5. 所有者とSource

本体は8所有者、31定理・8定義、823行。

- [DiscreteValuationPullback](../../../DkMath/Lib/NumberTheory/DiscreteValuationPullback.lean): 一般の局所中心と正整数倍率。
- [DedekindLocalParameter](../../../DkMath/Lib/NumberTheory/DedekindLocalParameter.lean): 有限個の素点でのCRT局所パラメータ。
- [WeierstrassFinitePlace](../../../DkMath/Lib/NumberTheory/WeierstrassFinitePlace.lean): 同じモデルの有限場所・評価・全点付値。
- [WeierstrassPolePullback](../../../DkMath/Lib/NumberTheory/WeierstrassPolePullback.lean): 極位数2,3による無限遠付値の正規化。
- [EllipticFiniteKernelLocalTransport](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelLocalTransport.lean): 同じ有限像点の中心と倍率を保持した公式。
- [EllipticFiniteKernelUnramified](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelUnramified.lean): 同じ軌道の局所パラメータから有限像点の倍率1へ。
- [EllipticFiniteKernelValuation](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelValuation.lean): 核上も含む全点付値の一致と位数公式。
- [FreyFiniteKernelValuation](../../../DkMath/FLT/FreyFiniteKernelValuation.lean): 同じSource・直線L・実点核の公開入口。

SourceではLの次元1から|H|=p、p≠2から奇数性を供給する。
同じ`residualOddKernelPointMap`・`residualKernelModelPull`の全点比較と、
同じ標的関数体へ降りた`residualKernelModelNorm`の全点位数公式を公開した。
LのGalois安定性は今回の幾何学的な付値比較には不要。

## 6. 模範証明との対応と残る境界

保存済みの模範解答
`S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed`
（[blob ed062b17e3fb1b5cfe9e452a95c32a266a067425](https://api.github.com/repos/anthropics/fermats-last-theorem/git/blobs/ed062b17e3fb1b5cfe9e452a95c32a266a067425)）で、
関数体写像に沿う場所の制限と、Vélu点関数による場所との一致が
点群への接続に使われている部分を確認した。

DkMathでは同じ源と標的の付値を直接比較し、有限像はCRT、無限遠像は極位数の偶奇で閉じた。
この既存の付値・座標環の経路により、模範解答の大きな所有者を一括importせずに実装した。
既存Apache所有者から拡張したDiscreteValuationPullbackとWeierstrassFinitePlaceには、
ライセンス・NOTICEと元のblobの参照を保持した。

今回の式は全ての源Pの像φ(P)での式である。
これを「標的の全点での主因子の押し出し」にするには、全ファイバーとH軌道の対応、
標的の場所への到達、大域的な有限支持の因子・点イデアルとの接続を閉じる必要がある。
零ファイバー=Hは既存だが、任意のファイバーの同定や全射性を今回証明したとはしない。
加法性・群準同型の核・isogeny・Cofixed有理像のp捩れ性は、その大域的接続の後に評価する。
整数係数モデル、局所還元と零成分輸送、一般hnoも未完了。

## 7. 検証

[対象テスト](../../../DkMathTest/Lib/NumberTheory/EllipticFiniteKernelValuation.lean) は
同じ曲線y²=x³−x、位数9の全3捩れ核、R=(−1,0)を使う。9定理・1定義。

- 全点での付値一致と、有限像点R・核上の無限遠像の両方。
- 同じ9点軌道の局所パラメータと、標的の有限像点の一様化元。
- 全点位数公式と、前回源で計算した−18を同じ標的のOで計算する例。
- Rの付値を二乗した実際の付値と、その位数が2倍になること。
  同じ関数の値exp(−1)とexp(−2)を分離し、正規化の証明を省けないことを確認する。

[Source37検査](evidence/Note032ValuationSmoke.lean) は3定理。
全点比較、Oの比較、全点軌道積位数公式を確認した。

対象本体・対象テストのビルド、Source37の直接Lean検査は全て成功、警告0。
本体39宣言・実例10宣言・Source37の3宣言、計52宣言の公理監査は
`propext / Classical.choice / Quot.sound`の範囲内。
新規コードの禁止構成、Lib依存方向、教科書docstring・昇格マーカー・ファイルマーカー、
入口登録、前回の所有者と契約資料の保持、差分の空白も検査した。
入口は静的確認。フルビルドとテスト全体は利用者側の分担である。

[検証記録](evidence/validation-note032-local-valuation.txt)、
[構造化証拠](evidence/note032-local-valuation.json)。
