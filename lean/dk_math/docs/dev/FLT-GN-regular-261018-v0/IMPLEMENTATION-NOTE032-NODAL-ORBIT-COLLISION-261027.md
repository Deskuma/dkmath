# NOTE-032 — 節点の巡回座標和・還元衝突点の輸送

2026-10-27。branch `dev/FLT-GN-regular-261018-v0`。
作業開始HEAD `bb59b81de5daebe9e206959efb7728844080349c`。
前章のフルビルド通過はユーザーから受領した。今回の検証は対象モジュールと独立スモークに限定する。

## 今回の到達点

滑らかな核側の二つの部品をまとめた。節点曲線上では実際の平行移動座標和を冪写像へ変換した。
一般ファイバーでは、核と同じ点へ還元する零成分点を同じ商写像で輸送し、同じ付値環標的で
滑らかにOへ還元することを証明した。安定核の場合は、同じ既存整数点準同型の像へも接続した。

| 部品 | 判定と範囲 |
| --- | --- |
| 原始n乗根の冪和・巡回座標和 | 任意の体・任意のnで証明。非衝突条件を保持 |
| 同じFrameの実点の平行移動和 | 証明。nP≠Oから各有限点の分母条件を内部供給 |
| 節点のn捩れ＝同じQの巡回部分群 | 原始根性・n≠0・二方向の分離の下で証明 |
| 同じ商による還元衝突点の輸送 | 証明。実核点Q、両点の滑らかさ、還元像の一致を保持 |
| 同じ既存整数像の滑らかさ | Sourceのq≠p・安定性の下で証明。2を除外しない |
| 非衝突の整点と同じ付値環商座標の還元接続 | 未完了 |
| 滑らかな核側の全E₀輸送・還元可換図式 | 未完了。今回の二部品を接続する工程が残る |

## 有限和に残る反対角線

`WeierstrassNodalOrbit` は、z(t)=t/(1−t)²について

\[
\sum_{j=0}^{n-1}z(t\zeta^j)=n^2z(t^n),\qquad t^n\ne1
\]

を証明する。有限等比和の二乗で分母を共通化し、根の冪和を使う。
0≤a,b<nでは、nがa+b+1を割る項はa+b+1=nの反対角線だけである。
そのn項と各冪和の重みnからn²が生じる。素数性、標数0、2・3・nの逆数は使わない。

同じFrameのδ=2α+a₁と節点x₀を用い、実際の点P,Qに対して

\[
\sum_{j=0}^{n-1}x(P+jQ)
 =nx_0+n^2\bigl(x(nP)-x_0\bigr)
\]

を得た。Qの節点比が原始n乗根で、nP≠Oという仮定を保持する。
Véluと同じ正規化「平行移動和−核座標和」も明示した。
核座標和を静的な和として残すため、12で割る標数制限が入らない。
これは同じ節点上の点の和についての定理であり、既存一般ファイバーの商像を
剰余でこの和へ同定した定理とは区別する。

比の単射性と原始根の冪表示から、nP=OとP∈ℤQも同値にした。
したがって衝突軌道は有限点公式の適用条件から正確に除かれる。

## 衝突点は核を引いて処理する

`EllipticFiniteKernelCollision` の主定理は、次の手順を実行する。

1. 指定した同じ整モデルで、滑らかな二点の差と実際の還元が可換であることを供給する。
2. 還元像が一致するP,QについてP−QがOへ還元することを得る。
3. 滑らかな点がOへ還元する条件を「点がO、またはx非整」と同値にする。
   全域還元関数は特異点も便宜的にOへ送るので、この同値には滑らかさが必要である。
4. 前章の無限遠近傍保存にOを加え、P−Qの同じ商像が滑らかでOへ還元すると結論する。
5. Q∈Hなら商準同型の加法性と核の等式からφ(P−Q)=φ(P)。元のPについて結論する。

源の還元型、臨界中心、接方向、全核の滑らかさは要求しない。
入力Qが実際の同じHの点であることを保持する。剰余の核点を無条件で持ち上げてはいない。

`FreyFiniteKernelCollision` は同じSource・L・H・付値環標的へこの定理を接続する。
q≠pの単元位数条件は既存算術で内部供給し、安定性の下では既存整数化の滑らかさ同値を使う。
整数標的と付値環標的の剰余座標の直接一致は結論しない。

## 模範証明との対応とライセンス

参照した模範実装は
[cyclotomic_velu_xLaw](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_cyclotomic_velu_xLaw.lean)
と、前章から取得済みの
[inZeroComponentAt_veluCoord_iff_of_multiplicative](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_inZeroComponentAt_veluCoord_iff_of_multiplicative.lean)。

前者の取得内容をGit blob `3070fac325fbd76952d37b988b13682b20dcadb4` と照合した。
約620行の全xLawから約90行の有限和核を抽出し、任意次数・任意標数の公開APIへ整備した。
実点への接続はDkMathの既存Frame、tc、点群加法、座標表示を用いて実装した。
この所有者はApache-2.0の元著作権・ライセンス・通知参照を保持する。

後者の約3600行の強い逆像同値全体は移植していない。
衝突点はDkMathの既存全点準同型と無限遠近傍保存から再構成した。
この再構成部分とSource接続・実例はMITの新規コードである。

## 実例と検証

- 標数2：原始5乗根の実点Pと、原始37乗根の実点Qを構成し、実37点の平行移動和を確認。
- 標数3：同様に7位数の実点Pと実37点核を使用。巨大な37乗展開を使わない。
- 原始根の生成点ではnP=Oとなることを確認し、非衝突条件の境界を検査。
- y²+xy+7y=x³の実3点核を再利用。47上では全核が滑らかに還元する。
  x(R)=1/47の点を代数閉包で構成し、P=Q+Rが核外でQと同じ点へ還元することを証明。
  この同じPの商像が滑らかで実際にOへ還元するところまで検査した。
- Source37の同じ付値環商像と既存整数像の終点を独立スモークで確認。

対象コマンド：

```sh
./lean-build.sh DkMath.Lib.NumberTheory.WeierstrassNodalOrbit
./lean-build.sh DkMath.FLT.FreyFiniteKernelCollision
./lean-build.sh DkMathTest.Lib.NumberTheory.WeierstrassNodalOrbit
./lean-build.sh DkMathTest.Lib.NumberTheory.EllipticFiniteKernelCollision
lake env lean docs/dev/FLT-GN-regular-261018-v0/evidence/Note032NodalOrbitCollisionSmoke.lean
```

本体3新規所有者16公開定理、対象実例7定理・1定義、Source37の2定理。
計26公開宣言を14・10・2に分けて公理監査した。
観測公理はpropext、Classical.choice、Quot.soundの範囲で、so#rryAx依存はない。
対象ビルドとスモークは警告なし。入口5importは静的に登録し、集約ルートはビルドしていない。

失敗時には、指定モデルの等式を使う補助定理へ`include hM`を明示し、
Pointsとmap後のPointの書換え差を型付き等式の推移と既存準同型のmap_zeroで処理した。
最初の抽出時の次数変数の衝突は、根の位数nと冪和指数mを分けて修正した。

証拠：
[スモーク](evidence/Note032NodalOrbitCollisionSmoke.lean)、
[JSON](evidence/note032-nodal-orbit-collision.json)、
[検証記録](evidence/validation-note032-nodal-orbit-collision.txt)。

## 次の接続

次は非衝突の整点について、同じP+jQの整性と剰余座標を確保し、
一般ファイバーの正規化和を今回の節点巡回和へ還元する。
同じ付値環標的の節点中心と比較して像の非特異性を得れば、
今回の衝突点処理と合わせて滑らかな核側の全E₀輸送へ進める。
Y座標と実際の剰余点の可換図式も別途必要である。

全零成分の逆像判定、正確なΔ深さ、q=p、スキームisogeny、
標的有理捩れの算術的排除、一般hnoは未完了。
