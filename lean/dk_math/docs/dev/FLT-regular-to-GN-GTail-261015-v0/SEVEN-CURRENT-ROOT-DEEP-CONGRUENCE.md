# 六根の七乗差と、共通 gap の深い補正項

同じ六因子族 `F : CurrentPhaseSeventhFamily p` について、提案された

\[
 \boxed{\lambda^{63}\mid\theta_j^7+u},\qquad
 \boxed{\lambda^{63}\mid\theta_i^7-\theta_j^7}
\]

を証明した。さらに、六つの補正項の来歴を一つの商 w で保持できる。

\[
 \boxed{g=\lambda^{64}w,\qquad
         \theta_j^7+u=\lambda^{63}T_j^{-1}w.}
\]

ここで `lambda=1-zeta`、`g=ofReal(rotate(rho)-rho)`、`u=ofReal(rho)`、
`T_j=-S_j` であり、`T_j*lambda=zeta^j-1` である。
63は可除性の下界である。正確な付値63や、新しい反例の降下は結論していない。

## 1. 三項式より前の一因子ごとの情報

六因子族の各表示は

\[
 g+(1-\zeta^j)u=(\zeta^j-1)\theta_j^7
\]

である。`phase_root_gap_identity F i` はこれを整理して

\[
 g=(\zeta^j-1)(\theta_j^7+u)
\]

を返す。Lean の添字 `i : Fin 6` と数学的な位相の対応は `j=i.val+1`。
元の同じ gap と parameter を保ち、三項関係を作る前の情報を公開する。

`phaseRootTwist i` は既存の `GNRamifierTwist` をこの添字へ適合させた単元である。
`phaseRootTwist_spec` は `T_j*lambda=zeta^j-1` を保証する。

## 2. 同じ剥離商を六根で共有する

既存の `current_gap_uniformizer_pow64 p` から、`g=lambda^64*w` と書ける。
各因子の等式に代入して、非零な lambda を一つ消すと

\[
 T_j(\theta_j^7+u)=\lambda^{63}w.
\]

T_j の逆単元を掛ければ冒頭の式となる。
`exists_common_phase_root_correction F` は、一つの w と、六位相すべてのこの等式を返す。
根ごとに独立した商を選んで可除性だけを残すことはしていない。

`phase_root_seventh_deep F i` はこの共通表示から依頼された型の定理を得る。

```lean
theorem phase_root_seventh_deep
    (F : CurrentPhaseSeventhFamily p) (i : Fin 6) :
    ramifiedUniformizer ^ 63 ∣ F.root i ^ 7 + ofReal p.rho
```

`phase_root_seventh_deep_of_le` は任意の `n≤63` への射影を与える。
同じ中心 u を消去すれば `phase_roots_seventh_sub_deep F i j` が得られる。
こちらにも任意の `n≤63` への射影がある。

これらは与えられた族 F に対する定理であり、族を新しく供給する単元補題や
イデアル七乗抽出をこの段階で再び呼んではいない。

## 3. 分岐剰余体での根の一致

lambda^63 可除性を一段へ落とし、`ramifiedEval` を適用すると

\[
 \overline{\theta_j}^{\,7}+\overline{\rho}=0.
\]

値域は `ZMod 7` なので、Frobenius `ZMod.pow_card` から

\[
 \boxed{\operatorname{ramifiedEval}(\theta_j)
       =-\operatorname{thetaResidue}(\rho)\ne0}
\]

となる。`phase_root_residue` と `phase_root_residue_ne_zero` がこの二つの結論を返す。
`phase_roots_same_residue` は任意の二位相の剰余の一致、
`phase_roots_sub_uniformizer_dvd` は根自身の差の一段可除性を与える。

ここでの `ZMod 7` は **C/(lambda)** という分岐剰余体である。
整数7を法とする **C/(7)** は、lambda の六乗を法とする厚い商であり、同じ商ではない。
七乗については整数7を法とする合同も得られるが、Frobenius から回復した根自身の合同は
lambda を法とするものである。

共通剰余は非零なので、どの根も分岐素イデアルには属さない。
根の差がその素イデアルに属することとは両立する。

## 4. 局所と大域で区別する二種類の主イデアル

`phase_roots_local_global_data F` は、同じ一つの族について次を保持する。

- 各七乗の lambda^63 合同。
- 各根の共通の非零な分岐剰余。
- 根自身の主イデアルの対ごとの互いに素性。

一方、**補正項**の主イデアルはすべて等しい。
共通商の表示から単元 T_j^-1 を取り除くと

\[
 (\theta_j^7+u)=(\lambda^{63}w)
\]

となるためである。`phase_root_correction_ideals_eq F i j` がこの等式を証明する。
互いに素なのは `(theta_j)`、等しいのは `(theta_j^7+u)` であり、対象が異なる。

また、互いに素性だけで根の主イデアルがすべて相異なると結論することはできない。
単元の主イデアルは全環であり、複数の単元は同じ主イデアルを持ち得る。
相異性や非単元性が必要になる段階では、追加の証明を用意する必要がある。

## 5. 同じ商による補正項のノルム式

既存の円分整数ノルムを N とする。
`N(lambda)=7` と単元の整数ノルムの絶対値が1であることから

\[
 \boxed{|N(\theta_j^7+u)|=7^{63}|N(w)|}
\]

が得られる。`exists_common_phase_root_correction_norm F` は、同じ一つの w について
gap の等式、各補正項の等式、この六つのノルム式を同時に返す。
従って補正項のノルムの絶対値も全位相で等しい。

これは加法を含む補正項を**一つの元として**取ったノルム式である。
`N(theta_j^7+u)=N(theta_j)^7+N(u)` という分配はしていない。
根そのもののノルム、既存の小さい実三次 gapRoot のノルム、反例状態の整礎測度の
厳密減少を、この等式から直接得たわけではない。

## 6. 重み付き式の合同は共通中心で説明できる

任意の C の元 x,y,z,u に対して

\[
 d\mid x+u,\quad d\mid y+u,\quad d\mid z+u
\]

なら、`d=lambda^n` のとき

\[
 d\mid x+\operatorname{ofReal}(\alpha)z
       -\operatorname{ofReal}(1+\alpha)y
\]

が成立する。`weighted_common_center_congruence` は、各差の線形結合だけでこれを証明する。
実際の六因子族も、既存の厳密な重み付き加法式も入力にしない。

`phase_roots_weighted_congruence_of_le F hn` は各七乗を代入し、任意の `n≤63` での合同を得る。
`phase_roots_weighted_congruence F` がその n=63 の場合である。
既存の厳密な式を使って単に `dvd_zero` にした証明ではないことを、依存監査でも確認する。

中心をそのまま代入すると

\[
 (-u)+\operatorname{ofReal}(\alpha)(-u)
       -\operatorname{ofReal}(1+\alpha)(-u)=0
\]

となる。`weighted_common_center_exact` がこの有限恒等式を証明する。
回帰例では全根1、parameter=-1の局所モデルが任意の深さの合同と重み付き式を満たし、
根1が非分岐であることも確認する。この局所モデルは current packet や FLT 反例ではない。

形式化した結論は、この重み付き合同が共通中心合同の帰結だということである。
他の大域的条件も含めたあらゆる合同論法が矛盾を生めない、という一般的不可能性の主張ではない。

## 7. 七乗が深く一致しても、根の枝は残る

zeta^7=1 なので

\[
 (\zeta\theta_j)^7=\theta_j^7.
\]

しかし根が非分岐なら

\[
 \boxed{\lambda^2\nmid\zeta\theta_j-\theta_j}.
\]

差が `-lambda*theta_j` であり、lambda を一つ消すと根の非分岐性に反するためである。
`phase_root_zeta_seventh_eq` と `phase_root_zeta_difference_not_dvd_sq` がこの境界を証明する。

回帰例では実際に六因子族の一つの根だけを zeta 倍した別の族 G を構成する。
七乗は変わらず、全位相の深い合同と共通剰余も成立するが、取り替えた根との差には
lambda² 可除性がない。
従って、七乗差の深さ63を、そのまま根の差の深さへ読み替えることはできない。

## 8. 正確な付値と降下へ残る接続

current common-prime packet c があると、`phase_root_correction_ne_zero F c i` は各補正項の非零性を返す。
零なら gap が零となり、既存の `rotate(rho)≠rho` に反するためである。
この場合は共通商 w も非零であることを回帰例で確認した。

それでも w がさらに lambda で何回割れるかは、この章では確定していない。
正確な付値、根の枝の正規化、大域的な非単元因子の配置は別の情報である。

新しい自然数反例に属する source、既存 API への再入、その**同じ証人**についての
整礎測度の厳密減少は引き続き未構成である。
今回の共通商と補正項のノルム式を、根の主イデアルや既存の小さいノルムへ接続するには、
それらが同じ算術的遷移に由来することを示す必要がある。

## 実装と検証

新規21定理と補正単元の定義1件を公理 whitelist で検査する。
回帰9例は、整数7への射影、七乗差と根の一段合同、同じ非零剰余と大域的互いに素性、
補正項のイデアルとノルムの等しさ、zeta による根の枝、任意深度の局所モデル、
current receiver の同じ根への供給を確認する。

七つの再帰的依存監査では、深い補正項に実際の lambda^64 gap が使われること、
剰余の回復に Frobenius が使われること、局所と大域の両情報が同じ F に由来すること、
重み付き合同が既存の厳密な加法式を使わないことを検査する。
族の生成や Kummer 単元 criterion の再実行は、これらの新規定理の証明グラフでは禁止する。

最終の通常ビルドは Kummer・DkMath 入口と新旧 suite を含めて10,540 jobs 成功。
テスト入口 `DkMathTest.lean` の直接型検査と、`DkMath` だけを import する smoke も成功した。
新規22宣言の公理は `propext`, `Classical.choice`, `Quot.sound` のみ。
全体で再表示する既存 sorry 警告5件は新規監査グラフに含まれず、新規ソースの警告はない。
全テスト glob の新規ビルドを主張する記録ではない。

- [深い補正項と剰余の定理群](../../../DkMath/FLT/Kummer/SevenCurrentRootDepth.lean)
- [回帰・公理・依存監査 suite](../../../DkMathTest/FLT/Kummer/SevenCurrentRootDepthSuite.lean)
- [検証記録](evidence/validation-seven-current-root-depth.txt)
