# NOTE-025: 平行移動の比例定数と片側のμₙ指標

日付: 2026-10-21。NOTE-022の同じ非零関数w(n,T)と、NOTE-024の位数保存から

\[
\exists! c(S,T)\in\overline K^\times,\quad
\tau_S^*w(n,T)=c(S,T)w(n,T)
\]

を構成した。標数0、n≠0、S,T∈E[n]を保持し、さらに

\[
c(O,T)=1,\qquad c(S+R,T)=c(S,T)c(R,T),\qquad c(S,T)^n=1
\]

を証明した。Tを固定した実際の指標

\[
c(-,T):E[n]\longrightarrow\mu_n
\]

をMathlibの`AddChar`として定義した。右側変数の加法性・交代性・非退化性・ガロア同変性、
`WeilPairingData`の存在と円分行列式の無条件化は今回の結論に含まれない。

## 1. 実装と読み順

| モジュール | 内容 |
| --- | --- |
| `DkMath.Lib.NumberTheory.EllipticFunctionFieldConstants` | 単元は非零定数、全有限付値が1の非零関数から一意な定数単元を復元 |
| `DkMath.Lib.NumberTheory.EllipticFunctionEigenvalue` | 全点の同じ位数から一意な比例定数、非零定数倍の固有関数 |
| `DkMath.Lib.NumberTheory.EllipticWeilCharacter` | 実際のWeil関数の移動固有値、乗法性、n乗根、定数倍の選び直しへの不変性 |
| `DkMath.FLT.FreyWeilCharacter` | 同じSourceの曲線と候補関数への接続 |

本体4モジュール・名前付き公開宣言28個。日本語の教科書docstringと、import後の正確な`#print "file: ..."`を付けた。
`DkMath.Lib`・`DkMath.FLT`・ルート`DkMath`へ公開し、回帰と監査を`DkMathTest`へ接続した。
一般の単元・付値・比例定数の判定は標数0を要求しない。既存のWeil関数に適用する段階で標数0を使う。

## 2. 単元のY成分をノルム次数で消す

座標環Aの単元u=p(x)+q(x)yのノルムは、係数体の多項式環でも単元なので次数0である。
NOTE-024の次数公式ではq≠0なら

\[
\deg\operatorname{Norm}(u)=\max(2\deg p,2\deg q+3)\ge3.
\]

これは次数0と矛盾するためq=0。残るノルムp²が単元なのでpも単元であり、体上の多項式環の単元は非零定数である。
q=0ではY成分の次数を加えないこと、零元は単元ではないことを保持している。

`isUnit_iff_eq_algebraMap`はこの必要十分条件を一般の係数体で証明する。
形式的な関数の値や定数判定のproviderを仮定せず、座標環の二元基底と実際のノルムを使う。

## 3. 全有限付値1から定数を復元する

非零有理関数gが全ての高さ1素イデアルvでv(g)=1なら、gとg⁻¹の両方の付値が1以下となる。
Mathlibの`HeightOneSpectrum.mem_integers_of_valuation_le_one`から、両方が同じ座標環に属すると分かる。
分数体への写像の単射性により、その座標環の代表元の積は1であり、gは単元である。
前節の分類からgは非零定数となる。

`exists_eq_algebraMap_of_valuation_eq_one`はg≠0を明示した上で、実際の係数体の定数を返す。
`existsUnique_unit_of_valuation_eq_one`は、係数体から関数体への埋め込みの単射性により、単元として一意に返す。
非零性は今回の数学的入力の一部であり、零関数を定数単元として扱わない。

次に、非零関数f,gの全点での位数が等しいとする。
−log vの一致と非零付値の`exp_log`から、乗法的付値の一致を復元する。
NOTE-021の`placeOf_surjective`により、全有限場所でv(f/g)=1となる。
従ってf/gは定数単元cであり、f=cgとなる。
`existsUnique_scalar_of_pointOrder_eq`はこの一般原理であり、Weil関数を要求しない。

## 4. 同じWeil関数の実際の移動比を使う

f=τ_S*w、g=wと置く。分子と分母の非零性は、既存のWeil関数の非零性と、実際の自己同型から供給する。
NOTE-024の`pointOrder_transEquiv_weilFunction_of_torsion`をそのまま渡し、一意なc(S,T)を得る。
`weilTranslationUnit`はこの存在定理から選んだ単元であり、`weilTranslationUnit_spec`が同じ関数体内の固有方程式を与える。
単に全有限場所での値が同じという結論を、新たな比例性の仮定に置き換えていない。

一意性はw≠0による消去と係数体の埋め込みの単射性による。
定数倍a*wに対しても、平行移動が定数を固定するので同じcが固有値となる。
`weilTranslationUnit_const_mul_unique`は、定数倍した関数の固有方程式を満たす任意の単元も同じcに一致すると示す。

さらに分子f(n,T)をa倍、分母f(n,O)をb倍に独立に選び直すと、商は(a/b)wとなる。
`weilNumerator_rescale_div`と`weilTranslationUnit_rescaled_numerators`は、実際の二つの分子を使ったこの商について、
固有方程式の解が元のc(S,T)であることとの同値を証明する。
a,bは係数体の単元であり、零倍による情報の消失は許さない。

## 5. 合成則と一意性から片側の指標を作る

平行移動の合成則を既存の関数wに適用すると

\[
\tau_{S+R}^*w=\tau_S^*(\tau_R^*w)
=c(R,T)c(S,T)w.
\]

係数体を固定することと一意性から、c(S+R,T)=c(S,T)c(R,T)を得る。
`weilTranslationUnitChar`は単元を値に取る`AddChar`である。
自然数倍への帰納からc(mS,T)=c(S,T)^mを証明し、実際のtorsion条件nS=Oからc(S,T)^n=1を得る。

`weilTranslationCharacter`は、この同じ値を`rootsOfUnity n (AlgebraicClosure K)`へ制限した`AddChar`である。
点の加法を根の乗法へ送るため、通常の加法準同型ではなく標準の`AddChar`型を使う。
`weilTranslationCharacter_val`は、その値が選択した同じ比例定数であることを保証する。
右側変数Tについて証明したのは、零目標ではw=1なのでc(S,O)=1となることだけである。

## 6. 回帰と依存監査

`FreyWeilCharacterTest`はSource 2=(4,3,5)の同じ曲線と非零2-torsion点Tを使う。
16宣言で、座標環の定数2の単元性、全有限場所での付値1、その一意な復元、
実際の移動固有方程式と一意性、二乗1、零移動、合成、μ₂への着地、Sourceの指標の加法則、定数2倍の固有関数を検査する。
零目標、指数1と37も検査する。非零目標を明示するが、指標の非自明性や交代性は結論しない。

`Note025DependencyAudit`は本体28宣言・回帰16宣言の公理と、13経路の型・opaque本体を検査する。
許容公理は`propext`・`Classical.choice`・`Quot.sound`のみ。
ノルム次数・Dedekindの整性判定・有限場所の全射性・既存の位数保存・非零性・平行移動の合成・n乗根への着地を要求する。
選択経路ではWeil対データ・旧FLT終点・外部未移植provider・大域Kummer入力を禁止する。
定数判定の一般補題ではDkMathのtorsion表現providerも禁止する。

検証結果は[validation-note025.txt](evidence/validation-note025.txt)、
ルートからの到達と公理表示は[RootSmokeNOTE025.lean](evidence/RootSmokeNOTE025.lean)に記録した。
focused buildは3206 jobs、`lake build DkMath DkMath.FLT DkMath.Lib DkMathTest`は11631 jobsで成功した。
ルートsmokeと`lake env lean DkMathTest.lean`の直接検査、tracker照合と`git diff --check`も成功した。
新規モジュールに警告はなく、統合ビルドでは既存の別モジュールのsorry警告5件が再掲された。

## 7. 参照元と未解決境界

次のAnthropic実装を読み、現在のMathlibとDkMathへ接続した。

- [全有限場所で付値1なら定数](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_FunctionField_exists_eq_algebraMap_of_valuation_eq_one.lean): blob `e6ef120f499a0d3a9b80eb48feb216ea8fbbd539`。
- [平行移動の比例定数](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_exists_transEquiv_weilFun_eq.lean): blob `d75949c4a12fcee6012c287a35a74f3f801e568f`。

定数判定の翻訳ファイルにApache-2.0の帰属・LICENSE/NOTICE参照・blob・変更点を保持した。
非零関数を明示的に引数に取り、参照実装の有限場所の非空性の補助構成を省いた。
単元のY成分の排除にはNOTE-024の自然数次数公式を再利用した。
比例定数の構成は、DkMathの全点位数保存を一般の関数比の一意性へ接続する形で実装した。
P2Mマクロや外部未移植providerはimportしない。

右側変数の加法性・交代性・非退化性・ガロア同変性は次の独立した境界である。
この片側指標の構成だけからWeil対の全公理、円分行列式、Frey表現の既約性、FLTの新たな閉鎖は導かない。
