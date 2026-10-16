# 深い Galois gap から、現在の単元の七乗根へ

回転固定性から整数合同を回復する補題が成立した。
現在の gap に適用すると、同じ一次パケットの単元について

\[
 \boxed{\delta=\kappa^7,\qquad\kappa\in C^\times}
\]

を得る。実ノルム二成分と共役位相一成分の障害は、現在のパケットではすべて零になる。
さらに同じ carrier の単元を吸収して

\[
 \boxed{C_j=(\zeta^j-1)\theta^7,\qquad\theta=\kappa\gamma}
\]

を構成した。元の `Q.delta` とその七乗根を明示しており、別の単元への取り替えではない。

## 1. 回転固定剰余は整数の像である

実三次環は既存の `SevenRealCubicInt` を使う。
一般補題は `Lib` へ移さず、モデル専用の
`SevenRealCubicRotationFixed.lean` に置いた。
名前空間は既存の `DkMath.FLT.Seven.SevenRealCubicInt` のままである。

主定理は依頼された型そのものである。

```lean
theorem rotation_fixed_mod_seven_integer
    (x : SevenRealCubicInt)
    (h : (7 : SevenRealCubicInt) ∣ rotateEquiv x - x) :
    ∃ n : ℤ, (7 : SevenRealCubicInt) ∣ x - (n : SevenRealCubicInt)
```

存在証明の整数は具体的に `n=x.fst` と選べる。
`rotation_fixed_mod_seven_fst` がこの強い形を証明する。
逆方向も成り立ち、`rotation_fixed_mod_seven_iff_integer` が必要十分条件を与える。

### theta 座標で見る理由

`theta=alpha-3` とする。既存の座標で

\[
 x=A+B\theta+C\theta^2\pmod7
\]

と書くと、回転差の座標は

\[
 \sigma_R(x)-x=3B\theta+(B+C)\theta^2\pmod7.
\]

`rotation_gap_thetaLinear_mod_seven` と `rotation_gap_thetaSquare_mod_seven` が
それぞれの式を証明している。固定なら `3B=0`、`B+C=0` なので `B=C=0` となる。
本章では新しい商環同型を構成せず、この二つの有限座標式と整数座標の可除性を検証した。

### 整数基底での明示的な証明

もとの整数基底の座標を `x=(a,b,c)` とすると、

\[
 \sigma_R(x)-x=(2c,-3b-3c,b).
\]

これが `7*w` なら `b=7*w.thd`、`2c=7*w.fst`。
後者から `c=7*(c-3*w.fst)` と書ける。
従って `x-a` の三座標はすべて7で割れる。
`seven_dvd_iff_coordinates` が、整数三座標の可除性を環内の可除性と結ぶ。

`ramifiedEval x=0` は一段の分岐因子で割れる条件であり、三座標すべてが7で割れる条件ではない。
`R/(alpha-3)` と `R/7R` の区別を保っている。

## 2. 現在の rho へ適用する

既存の実三次全分岐等式

\[
 7=\operatorname{axis}^3 U,\qquad U\in R^\times
\]

から、`axis^3` 自身も7で割れる。
現在の gap は既に `axis^32` で割れるので、

\[
 7\mid\sigma_R(\rho)-\rho.
\]

`current_rotation_gap_seven_dvd` は、既存の全分岐等式の単元係数を逆元で取り除き、
`7|axis^3` を gap の可除性へ適用する。
32乗の深さのうち3乗分だけで十分である。
一般の回転固定補題に適用して、

\[
 \exists n\in\mathbf Z,\qquad 7\mid\rho-n
\]

を得るのが `current_rho_congruent_integer` である。

これは rho が整数に**等しい**という結論ではない。
前章の `current_rho_not_integer` と両立する。
`current_rotation_ne_self` は、現在の非自明剰余比 tau から
`sigma_R(rho)≠rho` を証明し、合同と等式の違いを明示する。

## 3. 同じ delta に整数合同を輸送する

前章のパケットが持つのは

\[
 7\mid\delta+\operatorname{ofReal}(\rho).
\]

`7|rho-n` を `ofReal` で運び、差を取れば

\[
 7\mid\delta+n,
 \qquad\text{すなわち}\quad\delta\equiv-n\pmod7.
\]

これが `realPrimary_integer_congruence_of_rotation_fixed` である。
`realPrimary_seventh_of_rotation_fixed` は、この合同を既存の
`concrete_kummer_unit_power_criterion` にそのまま渡す。
単元補題は証明済みの定理を使い、追加の criterion 仮定を導入していない。

`current_primary_packet_unit_seventh` は、parameter が現在の rho に等しい
任意の `Q : PrimaryPacket` の同じ `Q.delta` に適用できる。
`current_primary_packet_obstruction_zero` が

\[
 \operatorname{normCoordinates}(Q.\delta)=0,
 \qquad\operatorname{phaseCharacter}(Q.\delta)=1
\]

を結論する。以前の実三次 alpha の非七乗例とは、回転固定性という仮定が異なる。

## 4. 根の選択への依存と、七乗剰余類の独立性

前章で、元の分解の補正単元 `delta0=epsilon*T_j^-1` が一次になることは、
元の根 beta の分岐剰余が1であることと同値だと証明した。
一次合同そのものは、任意の根の選択で成立しない。

しかし**七乗性**は根の選択によらない。
前章の初期正規化を同じ t で保持すると、

\[
 Q.\delta=\delta_0t^{-7}=\kappa^7
 \quad\Longrightarrow\quad
 \delta_0=(\kappa t)^7.
\]

`current_corrected_unit_seventh` は、現在の carrier の任意の receiver 分解
`C_j=lambda*epsilon*beta^7` から、この結論を返す。
raw の epsilon 自身を七乗と主張しているわけではない。
分岐因子の補正 `T_j` を外した単元の七乗性である。

## 5. 同じ carrier の単元を除く

`PrimaryPacket.unit_absorption` は、`Q.delta=kappa^7` を同じ分解に代入し、

\[
 Q.\operatorname{source}=(\zeta^{Q.\operatorname{phase}}-1)
       (\kappa Q.\gamma)^7
\]

を返す。
`currentCarrier_unit_free_factor_receiver` は前章の実際の receiver を呼び、
そこから得た同じ Q について kappa と theta を返す。
gap、parameter、位相、source の等式、`Q.delta=kappa^7`、`theta=kappa*Q.gamma`、
根の非分岐性、元の Fermat 方程式を保持する。
仮定には引き続き `CurrentCommonPrimeCyclotomicPacket` がある。

出力を、単元フィールドが1の新しい `PrimaryPacket` と見なしてはいけない。
単元の吸収後に `1≡-rho mod 7` が成立するとは限らないからである。
回帰例では、整数一次単元 delta=-1 を吸収したとき、同じ parameter に対する
delta=1 の一次合同が失われることを確認する。

## 6. 厳密減少の遷移に向けた境界

単元を吸収しても

\[
 (\theta)=(\kappa\gamma)=(\gamma)
\]

なので、根の主イデアルから定まる任意の自然数測度は厳密には減らない。
`unit_absorption_no_measure_drop` がその否定を証明する。
この単元除去を、求める降下の遷移と呼ぶことはできない。

さらに、現在の common-prime packet では、得られた theta をそのまま
実三次環の次の parameter に戻す経路も使えない。
`current_unit_free_root_not_real` は

\[
 \boxed{\neg\exists v\in R,\quad\theta=\operatorname{ofReal}(v)}
\]

を証明する。もし theta が実部分に属すれば、theta^7 も実部分に属す。
`C_j=(zeta^j-1)*theta^7` の端点を比較すると `sigma_R(rho)=rho` が従い、
現在の非自明な tau と矛盾するためである。
これは直接の実部分への再入だけの排除であり、別の算術的変換の不可能性ではない。

既存の `DirectOrbitSmallerNormPacket` と `directOrbit_twisted_state_measure_lt` には、
別の実三次 gap 抽出による小さい正のノルムと巡回的な七乗方程式がある。
また `SevenRamifiedFusionStrictDescentFailureBoundary` は、既存の深度減少と
新しい反例の再構成を区別している。
これらは今回の theta を次の同型の入力へ戻す証明ではない。

今回完成したのは、回転固定性、整数合同、同じ単元の七乗性、同じ carrier の単元除去である。
根の主イデアルや高さを厳密に減らし、その出力を次の許容入力へ戻す遷移は未構成である。
次段では、theta の六次環内での演算から新しい source と係数を作り、
再入条件と減少性の両方を同じ証人で証明する必要がある。

具体的な次の研究候補として、同じ二端点の三因子を使う方法がある。
`A_i=a-zeta^i*b` なら有限の線形恒等式

\[
 (\zeta^j-\zeta^k)A_i+(\zeta^k-\zeta^i)A_j+(\zeta^i-\zeta^j)A_k=0
\]

を持つ。全位相の単元除去を同じ source から束ねて代入すれば、三つの七乗根を結ぶ
加法関係を得る候補になる。ただし、この三因子の同時構成と遷移は本章では未実装。
残る係数単元、互いに素性、新しい source への再入、測度の厳密減少を別々に検査する必要がある。

## 実装と検証

公開18定理に日本語の docstring を付けた。回帰11例、公理 whitelist、四つの再帰的依存監査を備える。
回転固定性の証明には Kummer 単元補題を使わず、単元七乗性への橋では証明済みの
整数合同版 criterion を実際に使うことを依存グラフで検査する。

既存の `SevenRealCubicThetaSeventhPower` では、公開定理の型と係数式を保持して、
七乗の逐次展開を `x^7=x^4*x^2*x` による座標計算へ置き換えた。
二乗・四乗の補助恒等式は private とし、この変更も Lean のカーネルで検証する。
初回の全体入口検証で重かった依存先の計算を小さくするための証明変更である。


最終ビルドは Seven・DkMath 入口と新旧 suite、既存深度テストを含めて10,538 jobs 成功。
テスト入口 `DkMathTest.lean` と、Kummer／DkMath それぞれの入口 smoke も成功した。
新規18定理は標準3公理だけに依存し、変更した既存座標証明二つは `propext` と
`Quot.sound` のみ。全体では既存の sorry 警告5件を再表示するが、監査した新規証明グラフには含まれない。
全テスト glob の新規ビルドを主張する記録ではない。

- [実三次回転固定性](../../../DkMath/FLT/Seven/SevenRealCubicRotationFixed.lean)
- [現在の単元七乗性と単元除去](../../../DkMath/FLT/Kummer/SevenCurrentUnitSeventh.lean)
- [回帰・公理・依存監査](../../../DkMathTest/FLT/Kummer/SevenCurrentUnitSeventhSuite.lean)
- [検証記録](evidence/validation-seven-current-unit-seventh.txt)
