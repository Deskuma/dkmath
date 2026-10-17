# 六補正項が共有する七乗主イデアル

2026/10/17 JST

実装: [SevenCurrentCorrectionPower.lean](../../../DkMath/FLT/Kummer/SevenCurrentCorrectionPower.lean)。入口: `DkMath.FLT.Kummer`。
前章: [共通商の実三次構造](SEVEN-COMMON-QUOTIENT-REAL-NORM.md)。

## 固定するデータ

六因子族 `F : CurrentPhaseSeventhFamily p` と、小ノルムパケット
`S : DirectOrbitSmallerNormPacket p` を固定する。
以下の k、ε、r はそれぞれ **同じS** の `powerSplit.gapSplit.k`、`powerSplit.gapUnit`、
`powerSplit.gapRoot` である。別の存在証明から根を取り直さない。

前章の元の等式は

\[
w=\zeta^3\operatorname{ofReal}(\operatorname{axis}^{42k}\varepsilon r^7),
\quad
\theta_j^7+u=\lambda^{63}T_j^{-1}w.
\]

ここで `63=9*7`、`42k=(6k)*7` を使い、

\[
\Gamma=\lambda^9\operatorname{ofReal}(\operatorname{axis}^{6k}r),
\qquad
U_j=\zeta^3T_j^{-1}\operatorname{ofReal}(\varepsilon)
\]

と定義する。Gamma は `correctionCommonRoot S`、単元族は
`correctionPhaseUnit S : Fin 6 → Cˣ`。後者は単元型で構成されるため、
イデアルへの移送時に改めて可逆性を仮定する必要がない。

## 七乗主イデアルと相対係数

`correction_common_root_factor` は全六位相について

\[
\theta_j^7+u=U_j\Gamma^7
\]

を証明する。主イデアルへ送ると単元が消え、`correction_common_root_ideal` によって

\[
(\theta_j^7+u)=(\Gamma)^7
\]

となる。単なる六主イデアルの一致より強く、共通の七乗根となる主イデアルを指定できた。

また `correction_phase_unit_ratio` は単元群そのもので

\[
U_iU_j^{-1}=T_jT_i^{-1}
\]

を証明する。従って七乗剰余類へ射影しても同じ等式が成立する。
右辺にはSの根・深度・実三次単元が現れない。
ただし個々のU_jが七乗単元であるという主張ではない。
回帰例では、異なるSを使ってもこの比が変わらないことを確認する。

## 正の共通ノルムの七乗

六次ノルムは実三次像に対して平方となるので

\[
|N_C(\Gamma)|
=7^9 |N_R(\operatorname{axis}^{6k}r)|^2
=7^{9+12k}|N_R(r)|^2
=7^{9+12k}\operatorname{normRoot}^2.
\]

この値はSの `normRoot_pos` から正である。
単元ノルムの絶対値は1なので

\[
|N_C(\theta_j^7+u)|
=\left(7^{9+12k}\operatorname{normRoot}^2\right)^7.
\]

前章の `7M²` と両立する：`7*(9+12k)=63+84k`、根のノルムの指数は14。
今回は補正ノルムが正の完全七乗でもあることを、実際の元の七乗表示から証明した。

## 一つの保存パケット

`CurrentCorrectionPowerPacket F S` は共通根、六単元、明示的定義との一致、
全六因子表示、主イデアル七乗性、相対単元等式、根のノルム公式と正値性、
補正ノルムの七乗公式を保持する。
`currentCorrectionPowerPacket F S` が構成子を与える。
FとSは型の添字であり、因子表示とノルムで別々の根を選べない。

## 降下との境界

Sのrについて既存の `0<normRoot<gapSplit.a` がある一方、Gammaにはlambda^9と
axis^(6k)が付く。Gammaのノルムが既存の高さより小さいとは証明していない。
本パケットは次の許容反例source、その原始性・分岐条件、API再入を供給しない。
残る課題は、同じ六本の関係から新しい許容状態を構成し、**同じ新状態**の再入条件と
整礎測度の減少を同時に示すことである。

## 検証

公開6定理・3定義・1構造体の公理whitelist、3回帰例、型とopaque本文を辿る
3証明グラフの依存監査を用意した。依存監査では既存FLT終点、sorryAx、FltRegular、
選択因子receiverやKummer単元判定への近道を禁止し、既存のgap・商・powerSplitの来歴を確認する。
詳細は [検証記録](evidence/validation-seven-current-correction-power.txt)。
