# 現在の carrier の一次合同：gap の検査と根の正規化

提案された必要条件を形式化すると、現在の carrier を排除する条件にはならず、
逆に一次合同を構成するのに十分な gap の深さが既存コードにあった。
`currentCarrier_ramified_element_receiver` の単元は、そのまま任意の選択で一次になるわけではない。
剥離根を分岐剰余1に選び直すと、同じ source の `PrimaryPacket` を供給できる。

本章の主な結論は次である。

\[
 \begin{gathered}
 \lambda^2\mid g,\quad \bar\rho\ne0,\quad \lambda\nmid\beta,\\
 C_j=(\zeta^j-1)\delta\beta^7
 \quad\Longrightarrow\quad
 \boxed{\left(\exists t\in C^\times:\
       \delta t^{-7}\equiv-\operatorname{ofReal}(\rho)\pmod7\right)
       \iff 7(\zeta^j-1)\mid g.}
 \end{gathered}
\]

ここで `C` は具体的六次円分整数環、`g=ofReal(x)` は実三次 gap、
`1≤j<7`、`bar(rho)` は分岐評価 `thetaResidue rho` である。
必要条件に加え、根の単元倍を許したときの十分性も証明した。
既存 FLT 終点や、七次の整数合同 Kummer criterion はこの証明に使わない。

## 1. 分岐因子の向きを、同じ元の等式で補正する

\[
 \lambda=1-\zeta,\quad
 S_j=1+\zeta+\cdots+\zeta^{j-1},\quad
 T_j=-S_j,\quad \ell_j=\zeta^j-1=\lambda T_j.
\]

`GNRamifierTwist` は既存の大域的円分単元 `T_j` である。
receiver の任意の分解

\[
 C_j=\lambda\varepsilon\beta^7
\]

に対して、`factor_after_ramifier_twist` が

\[
 C_j=\ell_j\delta_0\beta^7,\qquad\delta_0=\varepsilon T_j^{-1}
\]

を返す。この段階では根は変わらない。
`currentLinearCarrier_eq_realGNSource` によって、source は

\[
 C_j=\operatorname{ofReal}(\operatorname{rotate}(\rho)-\rho)
       +(1-\zeta^j)\operatorname{ofReal}(\rho)
\]

の同じ元と一致する。係数環は実三次環のままに保つ。

また `current_root_away` は receiver の任意の剥離根について `lambda∤beta` を証明する。
もし `lambda|beta` なら因子表示から `lambda^2|C_j` が従い、既存の
`currentLinearCarrier_not_mem_ramifiedPrime_sq` に反するためである。

## 2. 剰余1の根の七乗は mod 7 で1

`ramifiedEval_eq_one_iff_dvd` は

\[
 \operatorname{ramifiedEval}(\beta)=1\iff\lambda\mid\beta-1
\]

を具体的な素イデアルの零核から証明する。
既存の全分岐等式は

\[
 7=\lambda^6 U,\qquad U\in C^\times
\]

なので、`lambda^6|7` と `7|lambda^6` の両方向を得る。
`beta=1+lambda*z` の二項展開では、内部係数が7を含み、端項は `lambda^7` を含む。
従って

\[
 \lambda^7\mid\beta^7-1,\qquad 7\mid\beta^7-1.
\]

`seventh_sub_one_dvd_seven_of_residue_one` はこれを既存の一般二項係数補題から証明する。
整数冪基底から標数7の Frobenius へ進む方法と同じ目的の合同を、
分岐等式と有限の二項展開だけで得た。根の単元性は要求しない。

逆方向は、mod 7 の合同を分岐剰余 `F_7` に移して `a^7=a` を使えばよい。

\[
 \boxed{7\mid\beta^7-1\iff\operatorname{ramifiedEval}(\beta)=1.}
\]

この同値は `seventh_sub_one_dvd_seven_iff_residue_one`。
前章の `AllowedGauge` の条件が、ちょうど剰余1の単元であることも分かる。

## 3. 一次合同から gap の必要条件へ

`factor_gap_identity` は source と分解を比較して

\[
 g=\ell_j\bigl(\delta\beta^7+\operatorname{ofReal}(\rho)\bigr)
\]

を返す。まず `lambda^2|g` と `ell_j=lambda*T_j` から、括弧内は mod lambda で0になる。
`delta≡-ofReal(rho) mod 7` を分岐剰余へ移すと、

\[
 \bar\rho\,(\bar\beta^7-1)=0.
\]

`bar(rho)≠0` と `F_7` の Frobenius から `bar(beta)=1`。
ここが `root_residue_one_of_primary` であり、parameter の非零剰余という条件を省略しない。

従って mod 7 では `beta^7=1` となる。さらに

\[
 \delta\beta^7+\operatorname{ofReal}(\rho)
 =\delta(\beta^7-1)+\bigl(\delta+\operatorname{ofReal}(\rho)\bigr)
\]

の両項は7で割れるので、

\[
 \boxed{7\ell_j\mid g}
\]

を得る。提案された候補命題を実装した定理が `gap_divisible_of_primary` である。

## 4. 深い gap と根の剰余1から、一次合同を構成する

逆に `7*ell_j|g` と `bar(beta)=1` を仮定する。
`ell_j≠0` を取り消すと

\[
 7\mid\delta\beta^7+\operatorname{ofReal}(\rho).
\]

ここから `delta*(beta^7-1)` を引けば、
`7|delta+ofReal(rho)` となる。
`primary_of_root_residue_one` がこの十分性を証明する。

これにより深い gap のもとで、固定された分解について

\[
 \boxed{\operatorname{RealPrimary}(\delta,-\rho)
          \iff\operatorname{ramifiedEval}(\beta)=1}
\]

が得られる。`primary_iff_root_residue_one` は弱い gap 条件と非零剰余も型に残す。

根が非分岐なら、その剰余は非零である。その逆数を大域的円分単元 `t` で持ち上げ、

\[
 \gamma=t\beta,\qquad \delta=\delta_0t^{-7}
\]

と置く。持ち上げは環の評価の全射性だけでは足りない。
本実装では `ramifiedEval(T_i)=-i` を使い、任意の非零剰余を実際の円分単元で持ち上げる。
これが `exists_unit_lift_ramifiedEval` と `exists_root_residue_normalizer` である。

`exists_primary_root_gauge_iff_gap_divisible` は、この構成と必要性を束ねた冒頭の同値。

## 5. 現在の gap は必要条件を満たす

既存の `directOrbit_gap_axis_pow32_dvd` は、実三次軸 `axis` に対して

\[
 \operatorname{axis}^{32}\mid\operatorname{rotate}(\rho)-\rho
\]

を供給する。六次環では `ofReal(axis)=zetaInv*lambda^2` なので、

\[
 \boxed{\lambda^{64}\mid g}.
\]

これは少なくとも64という可除性であり、正確な付値64を主張していない。
一方 `7*ell_j` は `lambda^7` と同伴であるから、全非自明位相で

\[
 \boxed{7(\zeta^j-1)\mid g}
\]

が成立する。`current_gap_seven_phase_dvd` は一次合同を仮定しない証明である。
従ってこのテストから現在の source の排除や FLT7 の矛盾は得られない。

## 6. 現在の receiver から PrimaryPacket へ

`currentCarrier_primary_packet_receiver` は既存 receiver を実際に呼び出す。
返す情報は次のとおり。

- 元の `epsilon,beta` と `C_j=lambda*epsilon*beta^7`。
- 正規化に使う大域的単元 `t`。
- 元の実三次 gap、parameter `rho`、同じ位相を持つ `Q : PrimaryPacket`。
- `Q.source=C_j`、`Q.gamma=t*beta`、`Q.delta=(epsilon*T_j^-1)*t^-7`。
- `ramifiedEval Q.gamma=1`、元の根と同じ主イデアル。
- パケットのフィールドとしての一次合同・根の非分岐性・非零 source。
- 元の `Fermat7Equation`。これは `Q` の外側で、そのまま保持する。

この定理の仮定には既存の `CurrentCommonPrimeCyclotomicPacket` がある。
FLT 反例の存在や、任意の Case II からそのパケットを作ることを結論していない。
また根の単元倍による正規化なので、根の主イデアルを小さくする操作ではない。
前章の有限反復保存定理には、この `Q` を実際に渡せるようになった。

## 7. 任意の根の選択では成立しない

正規化した根の剰余が1なら、さらに単元 `t` 倍した根の剰余は `ramifiedEval(t)`。
従って `primary_after_root_gauge_iff` は

\[
 \operatorname{RealPrimary}(\delta t^{-7},-\rho)
 \iff\operatorname{ramifiedEval}(t)=1
\]

を証明する。特に `t=-1` では失敗する。
`beta→-beta` と `delta→-delta` は同じ七乗因子表示を保つが、一次合同は保たない。
FLT を仮定しない非零な局所 GN パケットでも、この反例を回帰検証した。

初期正規化の `t` は必ずしも前章の `AllowedGauge` ではない。
一次合同をまだ持たないデータから、新たに合同の証明を備えたパケットを構成している。
一度一次になった後の保存遷移は、ちょうど剰余1の単元に限られる。

今回埋まったのは現在の carrier への実三次一次合同の供給である。
新しい FLT 解を作る操作と、再入・厳密減少を持つ降下は別途構成が必要である。

## 実装・検証の入口

- [七乗合同と円分単元による正規化](../../../DkMath/FLT/Kummer/SevenRamifiedFrobenius.lean)
- [必要条件・十分条件・選択依存性](../../../DkMath/FLT/Kummer/SevenRealPrimaryGap.lean)
- [現在の receiver への接続](../../../DkMath/FLT/Kummer/SevenCurrentPrimary.lean)
- [回帰・公理・依存監査 suite](../../../DkMathTest/FLT/Kummer/SevenCurrentPrimarySuite.lean)
- [検証記録](evidence/validation-seven-current-primary.txt)

後続章：[回転固定性と現在の単元の七乗根](SEVEN-ROTATION-FIXED-UNIT-SEVENTH.md) で、
rho の mod 7 整数合同を回復し、本章の同じ一次単元の七乗性へ接続する。
