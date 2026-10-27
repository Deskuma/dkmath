# NOTE-032 — 非衝突軌道の座標還元と節点の冪写像

2026-10-27。branch `dev/FLT-GN-regular-261018-v0`。
作業開始HEAD `bf8cb28597673d51ccc48647f989a942cd8a64c1`。
前回のフルビルド通過はユーザーから受領した。今回の検証は対象モジュールとスモークに限定する。

## 証明した接続

前回は剰余曲線上の巡回座標和と、一般ファイバーの衝突点を扱った。
今回は非衝突の零成分点Pについて、一般ファイバーの同じ商座標X_H,Y_Hを
同じ付値環の剰余へ運び、前回の節点上の冪写像公式に接続した。

同じ実核Hの各点が滑らかに還元し、Pも滑らかで、Pの還元がHのどの点の還元とも
等しくないとする。還元の加法性より、各P+Qは滑らかに有限点へ還元する。
従って全てのx,y座標は付値環に入り、還元後の座標と元の座標の剰余が一致する。
ここでOに対する便宜座標は有限点の公式へ代入しない。

前から成立していた一般ファイバーの正規化和

\[
X_H(P)=\sum_{Q\in H}x(P+Q)-\sum_{Q\in H}x(Q)
\]

と同じY座標の式を使い、同じHを添字に残して次を得た。

\[
\overline{X_H(P)}=\sum_{Q\in H}x(\bar P+\bar Q)-\sum_{Q\in H}x(\bar Q),
\qquad
\overline{Y_H(P)}=\sum_{Q\in H}y(\bar P+\bar Q)-\sum_{Q\in H}y(\bar Q).
\]

有限和の各項の整性を先に示し、剰余環写像の加法性を使う。異なる核や点を新たに選ばない。
P∉Hという一般ファイバー側の条件も、剰余での非衝突から内部供給する。

さらに源の剰余曲線が分離した節点を持ち、Hの位数が素数nであれば、
同じ還元準同型の単射性から巡回列挙と原始n乗根を構成する。
非衝突からn倍点もOでない。前回の軌道和を使って

\[
\overline{X_H(P)}=n^2x(n\bar P)+(n-n^2)x_0-\sum_{Q\in H}x(\bar Q)
\]

を得た。x₀は同じ源の節点であり、2・3・nで割らない。
一般次数については同じ核の明示的な巡回列挙と原始根を仮定する定理も提供する。

`FreyFiniteKernelNoncollision` は同じSource・一次元L・実核・点へ素数位数版を適用する。
L≤E₀[p]から核点の滑らかさを供給し、位数p、p以外の住所でのpの単元性も内部供給する。
源の節点Frame、接方向の分離、Pの滑らかさと剰余での非衝突は保持する。

## 実例・検証

既存の実曲線y²+xy+7y=x³と実3点核O,(0,0),(0,−7)を47上で再利用した。
x=1の実点は既存の代数閉包内の構成から得る。源方程式と偏微分から、もし特異なら
剰余で32=0となるが、47は32を割らない。従ってこの点は滑らかである。
核の有限点のx座標は0であり、Oも含めた核の還元像とx=1の点は衝突しない。
同じ実点の商X,Yの47上の整性と、両剰余の同じ3点核による和を確認した。
前回の47上の核外衝突点とは異なる実例である。

対象モジュール・スモーク：

```sh
./lean-build.sh DkMath.Lib.NumberTheory.EllipticFiniteKernelNoncollision
./lean-build.sh DkMath.FLT.FreyFiniteKernelNoncollision
./lean-build.sh DkMathTest.Lib.NumberTheory.EllipticFiniteKernelNoncollision
lake env lean docs/dev/FLT-GN-regular-261018-v0/evidence/Note032NoncollisionSmoke.lean
```

本体2所有者10定理、対象実例4定理、Source37スモーク1定理。
15宣言を10・4・1に分けた公理監査ではpropext、Classical.choice、Quot.soundのみを観測した。
対象ビルドとスモークは警告なし。集約入口の3 importは静的登録した。
フルビルド・全テストはユーザー側の検証分担とする。

型上では、一般ファイバーのPointsとモデルmap後のPointで点群演算の定義的な表示が異なる。
還元点の等式を型付きの中間等式と写像の加法性でつないだ。また、Fin nからZMod nへの
同じ巡回列挙は剰余の値を比較して同定した。Source37の数値型変換も明示した。

証拠： [スモーク](evidence/Note032NoncollisionSmoke.lean)、
[JSON](evidence/note032-noncollision.json)、[検証記録](evidence/validation-note032-noncollision.txt)。

## 残る境界

今回のXの式を得たことと、剰余標的で(X_H,Y_H)が非特異であることは別である。
次は同じ剰余商標的の節点中心を、今回の式の定数項
`n*x₀ − ∑Q x( Q̄ )` と同定し、n倍点の源の節点からの非零距離を輸送する。
それにより非衝突点の滑らかさを示し、前回の衝突点と合わせて滑らかな核側の全E₀像へ進む。
還元点としてのY座標・可換図式には追加の証明が必要である。

逆像判定、正確なΔ深さ、q=p、スキームisogeny、標的有理捩れ排除、一般hnoも未完了。
