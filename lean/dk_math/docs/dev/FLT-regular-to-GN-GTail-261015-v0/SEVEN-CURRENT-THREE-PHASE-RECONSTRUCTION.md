# 同じ二端点の六因子から、三項の重み付き七乗方程式へ

次の反例を再構成する前に、三因子の七乗表示を同時に供給できるかを検査した。
結果として、既存の共通因子パケットのもとで、同じ二端点の**六因子すべて**について

\[
 A_j=\operatorname{ofReal}(\sigma_R(\rho))
       -\zeta^j\operatorname{ofReal}(\rho)
     =(\zeta^j-1)\theta_j^7,\qquad 1\le j\le6
\]

を一つの族として構成できた。既存 receiver が選んだ根も、その値のまま族へ含められる。
位相1,2,3を使うと、同じ族の根について

\[
 \boxed{\theta_1^7+\operatorname{ofReal}(\alpha)\theta_3^7
       =\operatorname{ofReal}(1+\alpha)\theta_2^7}
\]

を得た。この式の根は六次環の元である。
原始性と非分岐性も同じ族について保持できる。
新しい自然数 FLT7 反例と、その同じ反例についての再入・厳密減少は未構成である。

## 1. 六因子の同時構成を可能にした既存 API

前章の `currentCarrier_unit_free_factor_receiver` は一つの選択位相の表示を返す。
これを Galois 回転しても、実三次係数まで回転するため、同じ二端点の別位相にはならない。

今回使ったのは `CurrentCarrierNormalizedPower.lean` に既にある全六位相の API である。

- `normalizedPhaseIdeals_pairwise`：分岐因子を一段剥離した六イデアルは対ごとに互いに素。
- `normalizedPhaseIdealProduct_seventh_power`：六イデアルの積は七乗。
- `normalizedPhaseIdeal_seventh_power`：任意の `1≤j<7` について、同じ位相の剥離イデアルは七乗。

`p : DirectRealCubicRootPacket source r` と
`h : DirectOrbitCanonicalCommonFactorPacket p` を固定する。
これらは今回の定理にも明示的な入力として残す。
`phase_ramified_element_receiver h hj` は各位相のイデアル七乗性を具体的な PID で主イデアル化し、

\[
 A_j=\lambda\varepsilon_j\beta_j^7,\qquad\lambda=1-\zeta
\]

を返す。選択素数の剰余アドレスは、この全位相の供給には使わない。

## 2. 各位相の単元を除く

各位相について、次の同じ経路を適用する。

1. `A_j` が分岐素イデアルの二乗に属さないことから `lambda∤beta_j` を得る。
2. `T_j=-S_j` を使い、分岐因子を `zeta^j-1` に合わせる。
3. 根を単元倍して分岐剰余1にし、補正単元の一次合同を供給する。
4. 深い gap からの `rho≡n mod 7` を、同じ一次単元の整数合同へ輸送する。
5. 証明済みの整数合同版 Kummer 単元補題を適用し、単元を根へ吸収する。

これが `exists_phase_unit_free_root h hj` である。
追加の単元 criterion や他位相の七乗表示を仮定していない。
分岐因子、パラメータ、両端点は各位相で固定する。

`CurrentPhaseSeventhFamily p` は

```lean
root : Fin 6 → C
factor : ∀ i, phaseCarrier p (i.val + 1) =
  (zeta ^ (i.val + 1) - 1) * root i ^ 7
root_away : ∀ i, ¬ ramifiedUniformizer ∣ root i
```

を保持する。`Fin 6` の添字0,1,2は数学的な位相1,2,3を意味する。
`exists_current_phase_seventh_family h` がこの族を実際に構成する。
六つの個別の存在命題を、一つの関数 `root` とその全位相の証明へ束ねている。

## 3. 既存 receiver の選択根を同じ族へ含める

現在の選択位相は `phaseInverseExponent c.phase`、値は1,4,5のいずれかである。
`currentPhaseSlot` はこれを族の添字0,3,4へ戻す。

既に根 theta とその正確な表示があれば、
`current_phase_family_extending_root` により、

\[
 F.\operatorname{root}(\operatorname{currentPhaseSlot}(c.\operatorname{phase}))
   =\theta
\]

を満たす同じ二端点の族を構成できる。
`replaceRoot` は指定位置だけを置き換え、他の五つの根は保つ。

`current_phase_family_receiver` は、前章の実 receiver が返した同じ `Q,kappa,theta` を使う。
`current_three_phase_data_receiver` はさらに、同じ一つの `F` のもとで次を返す。

- `Q` の gap、parameter、位相、source の来歴。
- `Q.delta=kappa^7` と、選択位置の根が厳密に `kappa*Q.gamma` であること。
- その選択根と元の `Q.gamma` の主イデアルの等式。
- 三項の重み付き七乗方程式、根の原始性と非分岐性。
- **元の** `Fermat7Equation a b d`。

最後の方程式は、新しく構成した反例の方程式ではない。
選択根と別の族から加法関係だけを取って合成することもしていない。

## 4. 同じ根について原始性を保持する

`F.root_ideal_power i` は

\[
 (\operatorname{phaseCarrierQuotient}(p,i+1))=(F.\operatorname{root}(i))^7
\]

という主イデアル等式を返す。
元の剥離イデアルには分岐補正単元 `T_j` が残るが、主イデアルでは単元を除けるためである。

これを全位相の既存の互いに素性へ代入し、イデアル冪の互いに素性から根の互いに素性を回復する。
`F.root_ideals_pairwise` がその結論である。
`F.root_ne_zero` と `F.root_away` も同じ根について成立する。

これは六次環の根の主イデアルについての原始性であり、自然数三つ組の `Nat.Coprime` を
新しく供給したことにはならない。

## 5. 三つの位相因子の加法関係

一般的な有限恒等式は `Lib/Cosmic/GNPhaseThreeTerm.lean` に分離した。
任意の可換環で、同じ `x,u` に対して

\[
 (\eta-\chi)\operatorname{phaseSource}(\xi,x,u)
 +(\chi-\xi)\operatorname{phaseSource}(\eta,x,u)
 +(\xi-\eta)\operatorname{phaseSource}(\chi,x,u)=0
\]

が成立する。`phaseSource_three_term_relation` がこの環恒等式を証明する。
位相の相異性や素数性は、この恒等式自体には不要である。

各 source が `(xi-1)*root^n` であるという三つの正確な表示を同時に代入するのが
`phaseSource_pow_three_term_relation` である。
`F.three_term_relation` は、この一般原理を同じ六因子族の任意の三位相へ適用する。

位相1,2,3では

\[
 (\zeta^2-\zeta^3)(\zeta-1)\theta_1^7
 +(\zeta^3-\zeta)(\zeta^2-1)\theta_2^7
 +(\zeta-\zeta^2)(\zeta^3-1)\theta_3^7=0.
\]

共通の非零因子 `zeta*(zeta-1)^2` を消すと、

\[
 \zeta\theta_1^7+(1+\zeta+\zeta^2)\theta_3^7=(1+\zeta)^2\theta_2^7.
\]

さらに既存の `ofReal_alpha` と `zeta*zetaInv=1` から

\[
 1+\zeta+\zeta^2=\zeta\operatorname{ofReal}(\alpha),\qquad
 (1+\zeta)^2=\zeta\operatorname{ofReal}(1+\alpha)
\]

を使い、共通位相単元 zeta を除く。
`F.real_weighted_seventh_equation` が冒頭の式を返す。

## 6. 加法変換の係数に現れる単元障害

係数 `1,alpha,1+alpha` はすべて単元である。
一方、既存の `alphaEmbeddedUnit_not_seventh` は、埋め込んだ alpha が七乗単元ではないことを証明する。
その実ノルム障害座標は `(3,3)` であり、零ではない。

今回の `no_common_unit_clears_three_phase_coefficients` は、共通単元を掛けてから
三係数を七乗へ吸収する操作も排除する。
もし単元 s,u,v,w に対して

\[
 s=u^7,\qquad s\alpha=v^7,\qquad s(1+\alpha)=w^7
\]

なら、最初の二式から `alpha=(u^-1*v)^7` となり矛盾する。

各因子の単元 delta_j と、この加法関係の係数 alpha は、来歴の異なる単元である。
delta_j の七乗性を確定しても、加法変換で生じる係数の七乗性は保証されない。
この結果が排除するのは三係数の共通単元倍と七乗単元による吸収である。
別の加法変換、別の位相三つ組、非単元を使うイデアル抽出の不可能性までは結論していない。

## 7. 再入と厳密減少の四条件に対する現在地

| 条件 | 今回供給したこと | 残ること |
| --- | --- | --- |
| 六次根から新しい source を作る | 同じ根の三項加法関係と重み付き七乗式 | 新しい反例に属する source の算術構成と来歴 |
| 七乗方程式・原始性・分岐条件 | 六次環の重み付き式、根の主イデアルの互いに素性、非分岐性 | 新しい自然数 FLT7 方程式と原始性、既存ルートが要求する分岐条件 |
| 既存 API への再入 | 同じ F と既存選択根の厳密な対応 | 新しい許容入力の構成 |
| 同じ新状態での厳密減少 | 今回の族について新しい減少評価は未供給 | 再入する同じ証人に対する整礎測度の厳密減少 |

current common-prime packet のもとでは、`F.root_not_real c i` により、
六つの根のどれも `ofReal v` としてそのまま実三次部分環へ戻すことはできない。
これは端点の一意性と `rotate(rho)≠rho` からの結論である。

既存の `DirectOrbitSmallerNormPacket` は別の gapRoot の小さい正のノルムを与える。
深度5から4への内部座標も、既存の抽出過程に属する。
今回の六因子族の根や、新しい反例の carrier との一致は証明していない。
したがって、それらの減少と今回の加法式を独立の存在証人のまま合わせて降下とは呼べない。

次に必要な仕様の形は、同じ next に関する

```text
exists next,
  ArithmeticSourceFromFamily F next
  and ReentryIntoExistingAPI next
  and measure next < measure old
```

である。これは今後の証明目標の説明であり、今回実装した定理や新しい公理ではない。
特に、反復する状態とその測度を統一し、今回の六次環の根、既存の小さいノルム、
新しい自然数反例の carrier の間を同じ証人の等式で結ぶ必要がある。

重み付き等式には全根1の局所例もある。回帰例でこの等式を確認したが、
この局所例を current packet や FLT 反例として構成したわけではない。
反復可能な状態には、等式だけでなく、その来歴や非自明性を保持する条件が必要である。
また、ノルムは乗法的であって加法的ではないため、三項式のノルムから
三つの整数ノルムの Fermat 方程式を直接得ることもできない。

## 実装と検証

新規の公開24定理、2定義、構造体と生成宣言を公理 whitelist で検査する。
回帰9例では、有限恒等式の局所例、六因子の同時供給、根の非自明な取り替え、
既存の選択根の保存、同じ族の加法式と原始性、係数単元の障害を確認する。

六つの再帰的依存監査では、全位相の供給に実際の全位相イデアル API と整数合同版 criterion が
使われ、選択因子の receiver や係数を動かす `rotate_realGNSource` から全位相を推測していないことを検査する。
実 receiver からの橋では、元の receiver と同じ根を族へ保存する処理が必須である。
加法恒等式と係数障害の証明は、族の供給や単元 criterion と独立に監査する。

Kummer・Lib・DkMath 入口と新旧 suite を含む通常ビルドは10,539 jobs で成功。
テスト入口 `DkMathTest.lean` の直接型検査と、`DkMath` だけを import する smoke も成功した。
監査した新規宣言の公理は `propext`, `Classical.choice`, `Quot.sound` のみ。
全体で再表示する既存 sorry 警告5件は、新規証明グラフの依存には含まれない。
全テスト glob を新規ビルドしたという主張はしない。

- [一般の三項関係](../../../DkMath/Lib/Cosmic/GNPhaseThreeTerm.lean)
- [六因子の同時七乗表示](../../../DkMath/FLT/Kummer/SevenCurrentPhaseFamily.lean)
- [三項方程式と係数障害](../../../DkMath/FLT/Kummer/SevenCurrentThreePhase.lean)
- [回帰・公理・依存監査 suite](../../../DkMathTest/FLT/Kummer/SevenCurrentThreePhaseSuite.lean)
- [検証記録](evidence/validation-seven-current-three-phase.txt)
