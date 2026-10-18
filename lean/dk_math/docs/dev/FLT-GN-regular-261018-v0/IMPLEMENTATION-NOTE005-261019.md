# NOTE-005: GN → 三根の Gap → Frey 判別式 → 局所付値

2026-10-19。[NOTE-005](NOTE-005.md) の提案を代数・整数算術へ翻訳した。
以下は実際の `Cubic`、`WeierstrassCurve`、許容座標変換と付値に関する証明である。
判別式という名前の定数を置くだけのモデルや、モジュラー性を暗黙の仮定にした
FLT の終点は作っていない。

## 1. 研究単位の到達範囲

| 提案 | 実装範囲 |
| --- | --- |
| `FreyGapCubic` | 三根・三次多項式の因数分解、三次判別式、実際の Weierstrass モデル、正規化変換、整係数条件 |
| `GNFreyDiscriminant` | GN による実際の Δ の表示、FLT 方程式による (abc)^(2p) 表示、c₄、向き付けからの整係数条件の供給 |
| `FreyPrimeValuation` | 2の補正を含む付値保存則、奇素数での p 倍性、原始性による c₄ の非可除性、奇素数での判別式の支持 |
| `FreyRepresentationContract` | 表現自体は未実装。実際の整数曲線と局所算術を保持する `DkMath.FLT.Frey.Source` まで構成 |
| `ModularLevelObstruction` | 未実装。モジュラー性・レベル降下・尖点形式の不存在は新たな理論の供給を要する |

公開入口は `import DkMath.FLT.Frey`。中立な三モジュールは `DkMath.Lib`、
FLT の入口は `DkMath.FLT` と通常の `DkMath` からも参照できる。
各追加 Lean ファイルは import 直後に `#print "file: モジュール名"` を持つ。

## 2. 三つの判別式の倍率を区別する

A,B を環の元とし、三次式を

\[
f(X)=X(X-A)(X+B)=X^3+(B-A)X^2-ABX
\]

とする。三根は 0,A,−B、差の積は AB(A+B)。
Mathlib の `Cubic.discr` から、

\[
\operatorname{disc}(f)=(AB(A+B))^2
\]

を証明した。一方、Weierstrass モデル

\[
W_0=[0,B-A,0,-AB,0],\qquad y^2=f(x)
\]

の実際の不変量は、

\[
\Delta(W_0)=16(AB(A+B))^2,\qquad
c_4(W_0)=16(A^2+AB+B^2).
\]

**三次式の判別式と曲線の判別式には16倍の差がある。**
有理数上の許容変換 `(u,r,s,t)=(2,0,1,0)`、すなわち
`x=4X, y=8Y+4X` を Mathlib の `VariableChange` で構成すると、

\[
W=[1,(B-A-1)/4,0,-AB/16,0]
\]

となる。`variableChange_Δ` と `variableChange_c₄` を実際に適用し、

\[
\Delta(W)=2^{-12}\Delta(W_0)=\frac{(AB(A+B))^2}{256},
\qquad c_4(W)=A^2+AB+B^2
\]

を得た。ここで「正規化」はこの変換によるモデルを意味する。
全素数で最小モデルであることは証明していない。

NOTE の参照先でも同じ係数のモデルが用いられていることは、指定された版の
[PROOF-PATH §2](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md)
で照合した。実装の証明依存は Mathlib と DkMath のみであり、この外部実装の
FLT・モジュラー性定理を import していない。

## 3. 有理数上の変換と整係数性を分ける

2 はℚで単元なので上の変換は常に作れる。しかしℤでは2は単元ではない。
また、整数除算は有理数除算とは異なる。

`IntegralNormalization A B` は

\[
4\mid B-A-1,\qquad16\mid AB
\]

を保持する。この条件の下でのみ、整数モデル `integral A B` のℚへの写像が
正規化モデルと一致することを `integral_map` で証明する。
`normalization_of_oriented` は、奇数 p、p≥4、4∣a+1、b が偶数、から
A=a^p,B=b^p の分母条件を供給する。証明の核は

- b が偶数なら16∣b^p（p≥4）。
- a≡−1 (mod 4) なら奇数冪について a^p≡−1 (mod 4)。

である。入力の a,b,c、原始性、非零性はそのまま保持する。
任意の整数反例をこの向きへ移す符号・置換の一般定理は追加していない。

## 4. GN の因子を残した保存則

奇数 p に対し `gnFactor p a b = GN p (a+b) (-b)` と置くと、既存の Core から

\[
a^p+b^p=(a+b)\,GN_p(a+b,-b)
\]

が従う。a+b=0 の場合も正しい恒等式であり、Gap を割り消さない。
正規化モデルに代入すれば、

\[
\Delta(W)=\frac{(ab)^{2p}\big((a+b)GN_p(a+b,-b)\big)^2}{256}.
\]

ここまでは FLT の方程式を要求しない。さらに a^p+b^p=c^p なら、

\[
\Delta(W)=\frac{(abc)^{2p}}{256},\qquad
c_4(W)=c^{2p}-(ab)^p.
\]

整数モデルでは256を逆元として扱わず、

\[
256\Delta(W_{\mathbf Z})=(abc)^{2p}
\]

という等式を保持する。整数の GN 表示も同じく分母を払った形である。

## 5. 付値と原始性の独立した二つの入力

abc≠0 と素数ℓを前提に、整数値の有理数付値で

\[
v_\ell(\Delta(W))=2p\,v_\ell(abc)-8v_\ell(2)
\]

を証明した。奇素数なら後項が0になり、整係数性の下で

\[
v_\ell(\Delta(W_{\mathbf Z}))=2p\,v_\ell(abc),
\qquad p\mid v_\ell(\Delta(W_{\mathbf Z}))
\]

を得る。ℓ∣abc を仮定しなくてもこの等式は成立する。
GN の因子を残す場合には、非零の冪和に対し

\[
v_\ell(\Delta(W))=
2p\big(v_\ell(a)+v_\ell(b)\big)+
2\big(v_\ell(a+b)+v_\ell(GN_p(a+b,-b))\big)
\]

を証明した（ℓは奇素数）。非零の冪和から Gap と GN の非零性を得ており、
零で付値が0にデフォルトすることを利用して積公式を偽装していない。

もう一方の入力が原始性である。一般に IsCoprime A B なら、素元 q について

\[
q\mid AB(A+B)\Longrightarrow q\nmid A^2+AB+B^2
\]

を整数の可除性だけで証明できる。これを A=a^p,B=b^p に適用し、
ℓ∣abc なら ℓ∤c₄ を得る。さらに奇素数では
`ℓ ∣ Δ(W_ℤ) ↔ ℓ ∣ abc` を証明した。

`Source.local_arithmetic` は、これらの事実を同じ入力・同じ整数曲線についてまとめる。
`Source.reduction_isElliptic` は ℓ∤abc の時、実際に `ZMod ℓ` へ写したモデルが
Mathlib の `IsElliptic` を満たすことまで証明する。ℓ∣abc の時の最小性や
乗法的還元の一般理論までは実装していない。

## 6. 実例と証明境界

回帰例の実際に構成できる source は p=1、3+16=19。
モデルは `[1,3,0,-3,0]`、Δ=3249、c₄=313 となり、3での判別式付値は2、
5を法としたモデルは非特異、2での正規化判別式付値は `2·4−8=0` である。
このサンプルを p≥4 の FLT 反例の存在と混同しない。
37次では一般定理から GN 表示と整係数条件を特殊化し、巨大な展開を避けた。
分母条件が不成立の (A,B)=(1,1)、零 Gap、原始性を欠く場合も回帰例に含めた。

今回の結果は実際の曲線に関する代数・局所算術の入口である。
mod-p 表現、既約性、モジュラー性、レベル降下、レベル2尖点形式の不存在を
この算術から得たとはしていない。ℓ=p でも算術式は成立するが、表現の
不分岐性・有限性を得るための追加証明は別途必要である。

統合ビルド `lake build DkMath DkMath.FLT.Frey DkMathTest` は **11,493 jobs** で成功した。
公開宣言48件の公理監査と主要5経路の実依存監査、通常入口の smoke と
`DkMathTest.lean` の直接検査も通過した。公理は標準の `propext`、`Classical.choice`、
`Quot.sound` に限られる。新規コードの警告はない。
トラッカーは 2,289 組について不一致なしで、新規6モジュール全てのマーカーも確認した。

実行コマンドと公理・依存・マーカー検査の結果は
[evidence/validation-note005.txt](evidence/validation-note005.txt) に記録する。
