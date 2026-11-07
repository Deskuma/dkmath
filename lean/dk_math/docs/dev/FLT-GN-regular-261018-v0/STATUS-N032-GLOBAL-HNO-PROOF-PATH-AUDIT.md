# NOTE-032: 一般 `hno` の証明経路監査

更新日: 2026-11-07。`__REVIEW.md` を参考に実ソースを照合し、局所入力を形式化した。

## 現在の証明境界

2026-11-07 時点で、同じ円分単元 ω² 空間の次元1と primary 単元空間の消滅は証明済み。
新しい Frey 分裂入口は単元側の hrank/htrace/hunit/hdetect を要求せず、
hbad・実際の hclass・同じ巡回段の全条件を保持する。一般 hno は未完成。
同じ hclass と各段の hbad の明示入力のもとで、実際の巡回次段・互換な塔・
無限で安定な p-primary/p-divisible 合併まで構成済み。各段の入力の算術的証明と、
高位捩れ全体の慣性吸収・良還元矛盾への接続は未完成。
同じ算術条件下で、標準 Tate p U の階数1同型と同じ直線への還元を接続し、
元の生成元を第一ベクトルに持つ全 Frey Tate 加群の Fin 2 基底も構成済み。
実際の Galois 作用行列の第一列は以前の同じ p 進指標と0である。
第二対角成分は同じ連続単元値指標として構成済みで、元の Cofixed 条件から mod p で1となる。
同じ算術入力のもとで、全 p 進円分行列式の一致と d=cyclo∞・χ∞⁻¹ も証明済み。
各正冪段の実際の Weil 対と、同じ有限基底・全基底の行列成分比較を使用する。
同じ実際の Frobenius 元に対する円分値=q、行列式=q、trace=χ∞+qχ∞⁻¹、
その係数による特性多項式と全・有限捩れ上の二次関係も証明済み。
有限体点数 q+1-#E(Fq) とこの trace の一致、第二指標の高位算術、
hclass・全段 hbad の算術的供給は未完成。
同じ有限商の第二座標の核=元の巡回段、高位吸収↔第二指標の同じ剰余=1 も証明済み。
良還元点数上界から同じ Frobenius の第二指標は非自明であり、さらに同じ条件付き塔のもとで、
共鳴する悪い素点の慣性に第二指標が非自明となる具体的証人を構成済み。
失敗点は p•y∉K を満たし、保持した狭い hbad の仮定領域の外にある。
その後、同じ節点幾何から有限・全 Tate 慣性差分の二次冪零性を証明し、
同じ第二指標が q≠p の悪い住所の慣性上で1であることを証明した。
前述の条件付き非自明証人と衝突させ、hclass・全段の狭い hbad のもとで Cofixed 排除を閉じた。
全直線の狭い hbadAll を入力とする既存 hno 形の定理も実装済み。
さらに hclass と Cofixed のみから、狭い hbad が失敗する実際の段・素点・慣性元・点を出力する。
この新しい失敗点は p•y∈K を満たす。算術入力を除去した一般 hno は未完成。
さらに同じ失敗点について、y と慣性差の p 冪零化上界、差の滑らかな還元・全慣性固定性、
元の段生成元の非滑らかさと臨界中心への付値不等式を証明済み。
同じ hclass と Cofixed から、この局所幾何を保持する証明書を全段 hbad なしで出力する。
hno の吸収入力は全直線から Cofixed 候補直線だけへ弱化済み。
候補生成元の滑らかな配置は十分条件として公開したが、その配置の算術的供給は未証明。
同じ失敗段と滑らかな部分群の交叉・局所商像は濃度 p^r と p^(n+1−r)、r≤n に分解済み。
同じ差点は滑らかな部分群による局所商では零だが、元の段による E[p^(n+2)] の有限商では
厳密位数 p の全慣性固定元となる。同じ有限商の実際の Galois 作用も構成済み。
この二つの商は異なる核を持ち、零・非零の違い自体は矛盾ではない。
同じ交叉は生成元 g の p^(n+1−r) 倍が生成し、局所商生成元の位数も厳密に p^(n+1−r)。
p^k•g が滑らかになることと n+1−r≤k の同値を証明済み。
局所慣性差分は通常の加法的準同型になり、その商への合成は前回の証人で非自明・厳密位数 p。
値は全て同じ慣性群に固定される。Frobenius q倍関係・野生誤差の作用消滅は未証明。
同じ有限商の濃度 p^(n+3)、実際の商作用・慣性差分準同型の連続性も証明済み。
同じ障害証明書から、像濃度・核商濃度・核指数が p^s（1≤s≤n+3）である開閉核を出力する。
開性は同じ慣性群の中での相対位相についての結論。c_x は同じ商元の作用差である。

**位数 `p` の Galois 固定幾何点と、同じ点についての2進・3進の全延長付値環での
零成分外性は実装済み。一般 `hno` は未完成である。**

```text
Cofixed line, p ≥ 5, Even S.b
  → integer quotient W, W.Δ ≠ 0
  → rational Q with addOrderOf Q = 2*p
  → P = baseChangePoint (2 • Q), addOrderOf P = p, Galois fixed
  → 2 ∣ W.Δ, 2 ∤ W.c₄; 3 ∣ W.Δ, 3 ∤ W.c₄
  → for every A above 2 or 3, P is outside the smooth zero component
                                                               [今回までで実装済み]
  → Mazur Step Three: other bad primes ℓ ≠ p                  [大域本体が未移植]
  → later cofixed torsion-tower/global argument                [未接続]
  → general hno                                              [未完成]
```

## 外部公開定理の正確な入力と出力

ローカルの `fermats-last-theorem` ソースを確認した。参照コミットとファイルの
SHA-256 は `evidence/note032-mazur-global-dependencies.json` に保存した。

`WeierstrassCurve.mazurStepThree_not_inZeroComponentAt` は以下を受け取る。

- 素数 `p`、`p ∉ {2, 3, 5, 7, 13}`。
- 整数モデル `W` と `W.Δ ≠ 0`。
- 幾何点 `P`、Galois 固定性、`addOrderOf P = p`。
- `2 ∣ Δ`, `2 ∤ c₄`、2上の任意の `LiesOverPrime` 付値環での零成分外性。
- `3 ∣ Δ`, `3 ∤ c₄`、3上の任意の `LiesOverPrime` 付値環での零成分外性。
- 対象の素数 `ℓ` ごとの `ℓ ≠ p`, `ℓ ∣ Δ`, `ℓ ∤ c₄` と付値環 `A`。

その結論が **対象の `A` における零成分外性** である。全 bad prime の零成分外性を
事前入力にしてはいけない。`Definitions/Def_ModularCurve_MazurStepThree.lean` の
命題仕様は全素数での半安定性を要求するが、上記の公開定理は対象 `ℓ` の局所条件を
個別に要求する。今回の局所終点は `p ≥ 5` で成立し、外部定理の例外素数条件を
消去したことにはならない。

## 実装済みの接続

| モジュール / 定理 | 内容 |
| --- | --- |
| `FiniteAdditiveTorsionQuotient.addOrderOf_two_nsmul_eq_prime_of_addOrder_eq_two_mul_prime'` | `ord Q = 2*p` だけから `ord (2 • Q) = p`。倍の非零性を内部供給 |
| `FreyRationalTwoPTorsion.residual_cofixed_implies_geometric_rational_prime_torsion` | 同じ有理 `Q` の倍を base-change し、厳密位数と固定性を公開 |
| `WeierstrassNodalCenterCharThree.candidate_defect_identity` | 任意の標数3の体で `b₂³ * equationDefect = Δ` |
| `WeierstrassNodalCenterCharThree.singularCentre_of_char_three_of_delta_zero_of_c4_ne_zero` | `Δ = 0`, `c₄ ≠ 0` から有理特異中心を構成 |
| `EllipticLocalComponentObstruction.localValuationSubring_double_not_mem_zeroComponent_of_singularCentre` | 実際の有理局所住所で `#E_sm ≤ q+1 < p` を使い倍の零成分所属を排除 |
| `FreyTriadicComponentObstruction` | Cofixed → `3 ∣ abc` → 3進剰余不変量 → 倍の零成分外性 |
| `EllipticRationalLocalTransport.hasSmoothReduction_integer_baseChange_iff` | 同じ素数上の任意の延長付値環へ滑らかな還元を保存・反映 |
| `EllipticRationalLocalTransport.hasSmoothReduction_iff_zero_or_exists` | 外部 `InZeroComponentAt` の零点または有限座標という仕様との同値 |
| `FreyMazurLocalInputs.residual_cofixed_mazur_integer_invariants` | `Δ ≠ 0` と2・3での整数不変量の可除性 |
| `FreyMazurLocalInputs.residual_cofixed_implies_geometric_prime_torsion_local_inputs` | **同じ一つの位数 `p` 固定幾何点**に2・3上の全局所条件を合成 |

固定性は既存 `pointAction_baseChange` を再利用した。新たな Galois 固定性理論は不要。
輸送では有理数とその逆数の付値環所属、および偏微分の非単元性を比較する。
代数閉包上の剰余体を有限体と同一視せず、有限濃度を輸送の仮定にもしていない。

## 残る大域本体の依存

外部 `P2M/Sol/S_WeierstrassCurve_mazurStepThree_not_inZeroComponentAt.lean` の
`solution` は次を具体的に消費する。

1. `ModularCurve.heckeOperatorsCommuteBar` と実際の `heckeModuleBar`。
2. `eisensteinQuotientInvariantsFiniteAt_heckeModuleBar`。
3. `cuspidalClassSurvives_heckeModuleBar`。
4. `mazurQuotientSpecialization_heckeModuleBar`。
5. `moduliPointExists_jQuotVelu_of_mult_two`。
6. `tateCuspCriterion_jQuotVelu`。
7. cusp の次数と Galois 作用、Jacobian の divisor-class 計算。

特に、局所入力を受け取るだけでは 1–7 の数学は供給されない。現在の DkMath には
これらのモジュラー曲線用終点がない。Eisenstein 整数のノルム API はこの Hecke 商と
別の対象であり、代用できない。

外部 `Definitions.*`, `Theorems.*`, `P2M.*` を構文的に辿った輸入閉包は 11,111
モジュールだった。これは wrapper と utility を含み、最小移植量の主張ではない。
必要な接続の入口は上記 1–7 である。

さらに `S_FreyPackage_frey_no_cofixed_large` は、Step Three 後にも、慣性での局所
filtration、torsion tower、連続 extension 消滅、Frobenius の Cayley–Hamilton と
有限還元点群の計数を使う。この後半も `hno` 閉包から省略できない。

## 検証

実行した検証と結果は `evidence/validation-note032-mazur-local-inputs.txt` に記録する。
新しい定理の `#print axioms` と禁止構文走査は、今回の局所結果の検証であり、
未移植の大域定理や一般 `hno` の検証を意味しない。


## 2026-11-01 追補: 残存分岐と大域証明の群論

`TEXTBOOK-N032-HNO-GLOBAL-CORE-261101.md` に教科書コードの証明順序を記録した。

- `FreyHnoSmallIndex` は既存 FLT5/7/11/13 を用いて対応する Source と Cofixed 枝を排除する。
- `FreyHnoRegularPrime` は既存一般 GN–Kummer FLT から正則素数の hno を得る。
  従って残存 Source は `p ∣ #ClassGroup(𝓞(CyclotomicField p ℚ))` を満たす。
- `FreyHnoHardCase` は同じ直線・同じ原始化と向き付けの証拠を保ち、非正則側・
  `p ≥ 17`・7側・primorial 支持ありの残存分岐へ一般 hno を正確に縮約する。
- `MazurStepThreeTwoAnchor` は finite subgroup と実 specialization の仮定から、
  prime-power 消滅、二アンカー消滅、非零 cusp 類の反証を証明する。
- `TorsionTowerFrobenius`、`EllipticTorsionTowerObstruction`、`FreyTorsionTowerObstruction`
  は、Frobenius 関係式と塔の仮定から、同じ実際の点群で最後の `p² ≤ p` の矛盾を証明する。

小指数・正則素数の結果は既存 FLT を使用する上位層であり、その FLT 証明へ戻さない。
二アンカーの実際の Eisenstein 商への適用と、Frey の Cofixed 枝からの Galois 捩れ塔の
構成は残る。**一般 hno は引き続き未完成である。**


## 2026-11-01 追補: 具体的な捩れ extension と慣性吸収の大域化

`TEXTBOOK-N032-TORSION-EXTENSION-INERTIA-261101.md` に今回の教科書コードを記録した。

- `EllipticTorsionInertiaAbsorption` と `FreyTorsionInertiaAbsorption` は、既存の
  絶対慣性生成を再利用し、悪い住所の局所吸収から全 Galois 元の差の吸収を証明する。
  最終矛盾の大域固定性 `hfixed` は局所条件から供給される。
- `TorsionPreimageQuotient` は実際の商 `(p⁻¹K)/K`、作用、捩れ像、補部分加群の持ち上げを構成する。
- `EllipticTorsionPreimageExtension` と `FreyCofixedTorsionExtension` は、Cofixed 直線から
  実際の二次元 extension の固定直線・円分商・開核を供給する。
- 安定な補直線が得られれば、次段の包含・位数・巡回性・捩れ指数・安定性・底への降下を証明する。
  巡回性は `PrimePowerCyclicCriterion` によって捩れ濃度から確認する。

安定な補直線の存在は未証明であり、必要な局所条件と大域 extension 消滅を構成する必要がある。
高位捩れの悪い住所での吸収と、実際の Frobenius 関係式も明示入力として残る。
Mazur Step Three の実際の大域幾何への適用と一般 hno は、引き続き未完成である。


## 2026-11-01 追補: 巡回塔の全段の円分商と局所補直線

教科書: `TEXTBOOK-N032-CYCLIC-TOWER-QUOTIENT-261101.md`。
実装: `CyclicPrimePowerScalar`、`TorsionPreimageScalar`、
`TorsionPreimageLocalComplement`、`FreyCofixedTorsionTower`。

- 第一段の `pK=0` を外し、実際の `V → K/pK` を構成。核が同じ捩れ像 `C` であることと、
  `V/C ≃ K/pK` を証明した。
- 巡回 `p^m` 群で `pK=K[p^(m-1)]` を証明し、底のスカラー作用を最上商へ輸送した。
- 同じ Cofixed 直線の底を含む全巡回段で `K[p]=B` を証明し、円分商公式を全段に拡張した。
  二次元性・固定像の一次元性・点ごとの固定性・開核も、同じ実際の段から供給する。
- 局所部分群 `K≤F≤p^-1 K` の実像から補直線を作り、指定した分解群安定性を輸送する。
  像の持ち上げが `F` 自体に戻ることも証明した。
- 商表現の `p` 外の不分岐性で良還元素数を内部供給し、`2` と `abc` の住所での逆像上の吸収を残す。
- 最終の局所慣性・Frobenius 矛盾から `hdown` を除去し、巡回性と底への包含から内部供給する。

一般 `hno` は未完成。局所部分群 `F` の幾何学的構成、悪い素点の高次捩れの吸収、
円分体の omega 二乗類群・単数固有成分による大域分裂、塔の反復、
実際の Frobenius 関係と Eisenstein specialization の入力は残る。
各分解群に安定な局所補直線を、一つの大域安定な補直線と同一視していない。
模範解答の大域 extension 消滅を未証明の `hEXT` として導入していない。


## 2026-11-01 追補: `p` 上の局所部分群と局所分裂の存在を実装

教科書: `TEXTBOOK-N032-AT-P-LOCAL-SPLITTING-261101.md`。

- `CyclotomicInertia.exists_inertia_cyclotomic_eq` により、任意の指定された `p` 上の
  付値環で円分指標の慣性への制限が全射。有限円分体の完全分岐と既存の有限慣性
  持ち上げ・付値環の共役を使い、別の存在 provider を置いていない。
- 節点還元の `p` 捩れ消滅を実際の剰余点群で `p^m` へ反復し、同じ臨界中心と
  還元準同型を使って高次捩れの慣性差も還元核に入ることを証明した。
- `F_m=E[p^m]∩H_A` を同じ還元核との実際の交わりで定義した。
  底の真部分空間性から上界を、倍写像の全射性・吸収・非自明な底の作用から下界を得て、
  全正指数で `#F_m=p^m` と巡回性を証明した。
- 元の Cofixed 直線を含む大域安定な巡回段 `K` は `F_m` そのものと証明した。
- 実際の次段 `F_(m+1)` の像から、同じ商の分解群安定な補直線を構成した。
  `residual_cofixed_cyclic_extension_locally_split_at_p` の入力に、局所部分群・局所濃度・
  局所降下・局所安定性・補直線の存在は残っていない。`p≥5`, `m≥1`、元の Cofixed 直線、
  同じ大域巡回段の不変量、指定した `A` の `p` 上の条件は明示している。

一般 `hno` は未完成。今回の局所分裂は大域安定な補直線の存在ではない。
悪い `q≠p` での必要な吸収、円分体の類群・単数の固有成分からの大域 extension 消滅、
巡回塔の反復構成、実際の Frobenius 関係と Eisenstein specialization は引き続き残る。

同じ指数 `N` の巡回段については `p` 上の高次捩れの吸収も `K=F_N` から供給した。
新しい最終終点 `residual_cofixed_cyclic_tower_inertia_frobenius_impossible` の `hbad` は、
`q≠p` で `q=2` または `q∣abc` の住所だけに限定された。


## 2026-11-01 追補: 非共鳴の悪い素点と2・3の吸収を実装

教科書: `TEXTBOOK-N032-NONRESONANT-INERTIA-261101.md`。
実装: `FreyNonresonantInertia`、`CyclicSignSeparation`、`CyclotomicFrobenius`、
`EllipticNodalDecomposition`。

- 同じ付値環の実際の Frobenius から円分指標 `q mod p` を導いた。
- `864F=c₆+c₄(b₂+12C.x)` と付値の比較により、臨界中心の分解群固定性を全素点で証明した。
  432を付値の単元とは仮定しないので2・3も扱える。
- 奇数単元次数の高次捩れに対する、同じ深さでの二枝比較から和差の滑らかさを供給した。
- `q mod p≠±1` の底の作用を用い、巡回段全体の滑らかな部分群への包含を証明した。
  実際の滑らかな捩れの濃度上界と `#K=p^m` より `K=E[p^m]∩H_A` を得た。
- 同じ指数の捩れ点、および `p⁻¹K` 上の慣性差が同じ `K` に入ることを証明した。
  逆像の場合は滑らかな底の慣性固定性で、差の指数を一段下げる。
- `p≥5` の2・3は非共鳴。良還元の住所と前章の `p` 上の吸収も内部供給される。

新しい公開終点
`residual_preimage_unramified_away_of_resonant_inertia` と
`residual_cofixed_tower_resonant_inertia_frobenius_impossible` に残る局所入力は、
`q≥5`、`q≠p`、`q∣abc`、`q mod p=±1` の住所のみ。
この条件を持たない吸収 provider に置き換えていない。

一般 `hno` は未完成。共鳴する悪い住所の吸収・実際の Mazur/Eisenstein 幾何、
円分体の omega 二乗類群・単数固有成分からの大域 extension 消滅、
必要な長さの巡回塔と実際の Frobenius 関係の構成は残る。
符号反転の有限群反例と `p=5,q=11,19` の合同例により、今回の符号条件を外す誤った一般化を避ける。
再帰依存監査は実際の還元・点群・濃度評価への到達と、既存 FLT 終点への非依存を要求する。


## 2026-11-02 追補: 円分指標核上の実際の有限加法指標

教科書: `TEXTBOOK-N032-CYCLOTOMIC-EXTENSION-CHARACTER-261102.md`。
実装: `FixedLineExtension`、`FreyCyclotomicExtensionCharacter`。

- 固定部分加群と指標商を持つ表現で、指標核上の作用差 `ρ(u)-1` が加法的であることを証明した。
- 同じ商ベクトルで評価し、同じ固定直線 `C` に値を取る実際の準同型 `a_v` を構成した。
- 共役則は `a_v(gug⁻¹)=χ(g)⁻¹ a_v(u)`。根の空間への同定・Kummer 双対化はまだ別工程である。
- 非自明な指標値の固有空間を構成し、大域安定な補直線の存在と指標族の消滅の同値を証明した。
  非自明な円分値は実際の `p` 上の慣性から供給する。
- 値域の濃度 `p`、像の濃度上界、開核を内部供給した。
- `p` 上では指標核と分解群の交わりで消滅。`p` 外では指標核と慣性群の交わりで消滅する。
  後者には共鳴する悪い住所の `hbad` が明示入力として残る。
- 大域分裂しないなら、構成した指標族の一つが位数 `p` の値域全体へ全射する。
- 指標族の消滅 `hzero` を明示すれば、同じ点群内で巡回塔の次段の全不変量を構成できる。

今回の結果は具体的な算術障害の構成・局所条件・分裂との同値であり、その消滅証明ではない。
共鳴する悪い住所、類群・単数との接続と消滅、巡回塔の反復、実際の Frobenius 関係と
Mazur/Eisenstein specialization の幾何は残る。**一般 `hno` は未完成である。**
位数20のアフィン群による局所補直線・大域非分裂・全射指標・逆指標の共役の回帰例を追加した。


## 2026-11-02 追補: 実際の良還元による固定点計数で `hCH` を除去

教科書: `TEXTBOOK-N032-FROBENIUS-FIXED-COUNT-261102.md`。
実装: `FiniteFixedQuotient`、`FiniteFieldFrobeniusFixed`、
`EllipticFrobeniusFixedReduction`、`FreyGoodReductionTowerObstruction`。

- 有限群上で `φ-id` の像を吸収先へ入れ、核・像の濃度公式から固定点の下界を得た。
- 任意の拡大体で `x^#F=x` を満たす元が実際の有限体 `F` の像に入ることを、多項式の次数で証明した。
- 同じ整数モデルの実際の還元を構成し、prime-to-`q` 捩れ上の単射性を既存の滑らかな還元から供給した。
- 実際の Frobenius 固定捩れ点の二座標を `ZMod q` に降ろし、`#E[n]^σ≤#E(F_q)` を証明した。
  延長付値環の剰余体全体を有限体と仮定していない。
- 一般の曲線で、位数 `n` の吸収先から `n≤#E(F_q)` を得た。特性方程式は不要である。
- `ell≠p` の良還元素数の存在と、その実際の点数 `N>0` を証明した。
- 新しい Frey 終点は `#K=p^(goodReductionPointCount ell)` と同じ指数の局所吸収を明示し、
  内部で選ぶ実際の Frobenius によって `p^N≤N<p^N` の矛盾を得る。

`residual_cofixed_point_count_tower_resonant_inertia_impossible` は `hCH`、`hfixed`、
独立の指数 `N`、Frobenius 元や付値環の存在 provider を要求しない。
旧 `TorsionTowerFrobenius` 経路と旧条件付き Frobenius 終点を再帰依存監査で拒否する。

一般の Frobenius 特性方程式そのものは未実装だが、新経路の不足入力からは外れた。
残るのは共鳴する悪い住所での吸収、円分体の類群・単数による具体的な指標の消滅、
必要な長さの大域巡回塔の反復構成、およびそれらを供給する Mazur/Eisenstein の幾何。
**一般 `hno` は引き続き未完成である。**


## 2026-11-02 追補: 指標の核の固定体と実際の円分巡回拡大

教科書: `TEXTBOOK-N032-CYCLOTOMIC-CHARACTER-FIELD-261102.md`。
実装: `CyclotomicKernelField`、`CyclotomicCharacterField`、`FreyCyclotomicCharacterField`。

- `ker χ_p` を同じ代数閉包内の `F=ℚ(ζ_p)` の fixing subgroup と同定し、
  `Gal(ℚ̄/F)` との同じ作用を保つ群同型を構成した。円分拡大性、数体構造、次数 `p-1` も供給する。
- 同じ付値環の分解群・慣性群への所属を、この群同型で双方向に輸送した。
- 同じ有限加法指標の核を絶対 Galois 群へ埋め、その固定体 `M` を実際に定義した。
  開核から有限性・数体構造・fixing subgroup との正確な往復を証明した。
- 逆指標の共役則から `M/ℚ` の Galois 性を、全射性から次数 `|C|(p-1)` を得た。
  同じ包含による `M/F` の次数 `|C|`、Galois 性、相対 Galois 群の位数も証明した。
- Frey の非分裂から全射指標を一つ選び、相対次数 `p` の実際の巡回拡大を構成する。
  拡大体・有限性・Galois 性・次数・共役則・開核の provider は残していない。
- `p` 上の分解群、`p` 外の慣性群が構成体 `M` の全元を固定することを接続した。
  後者には共鳴する悪い住所の `hbad` が引き続き明示入力として残る。

零指標では構成体が元の円分体に戻ることと、自明な値域への全射では相対次数1となることを回帰検証する。
次数 `p` の拡大を得たことは、その排除ではない。整数環の素イデアルの不分岐条件、
類群・単数の該当固有成分、根の空間への捩りと Kummer 双対化、その消滅、
巡回塔の反復および共鳴住所を供給する幾何は残る。
一般 `hno` は未完成であり、最終計数経路の `hCH` 除去は保たれている。


## 2026-11-02 追補: 同じ構成体の Kummer 根と元の指標核の検出

教科書: `TEXTBOOK-N032-CYCLOTOMIC-KUMMER-261102.md`。
実装: `CyclicKummer`、`CyclotomicCharacterKummer`、`FreyCyclotomicKummer`。

- 同じ有限巡回拡大から、Mathlib の逆 Kummer 定理で `α∈M` と `b∈F` を構成した。
  `α^p=b`、`F(α)=M`、`X^p-b` の既約性を束ねた表示を返す。
- 既約性から `b` が底体の `p` 乗でないこと、根・定数の非零性を証明した。
- 同じ体がその多項式の分解体であること、相対 Galois 群と `μ_p(F)` の同型、
  同じ根への作用と比 `σ(α)/α` の公式を実装した。
- 生成性と開核の正確な Galois 対応から、元の `ψ_v` の核と同じ根の固定群の一致を証明した。
- Frey の非分裂から同じ指標・同じ固定体の Kummer 表示を供給する公開終点を追加した。
  根・定数・多項式・生成性・拡大次数の provider は追加していない。
- 同じ付値環で `p` 上の分解群、`p` 外の慣性が同じ根を固定する。
  後者の元の共鳴住所の `hbad` は保持する。

実際の `𝔽₉/𝔽₃` での根・非平方定数・非自明作用と、
自明な拡大および次数1の境界を回帰検証する。
相対 Galois 群の根の群との同定は実装したが、円分共役の `ω²` の計算、
整数化、素イデアルの付値・不分岐条件、類群・単数との接続と消滅は未実装である。
大域巡回塔の反復と共鳴住所を供給する幾何も残り、**一般 `hno` は未完成である。**
最終固定点計数の `hCH` 除去は保たれている。


## 2026-11-02 追補: 同じ非零 Kummer 類の `ω²` 作用を実装

教科書: `TEXTBOOK-N032-CYCLOTOMIC-KUMMER-WEIGHT-261102.md`。
実装: `KummerRadicalCharacter`、`CyclotomicKummerWeight`、`FreyCyclotomicKummerWeight`。

- 同じ根の比 `κ_α(u)=u(α)/α` を実際の `μ_p` 値の群準同型として構成した。
  元の `ψ_v` とその核が一致することを、前章の固定群の判定から証明した。
- 元の全射指標への因子化を構成し、`ZMod p` 線形性によって共役のスカラーを同じ比へ輸送した。
- `w=σ⁻¹uσ` に対する元の共役則と根自身の円分作用から、二つの因子を保って `χ_p(σ)^2` を得た。
- `σ(α)/α^r` が円分核に固定されることを示し、同じ `F=ℚ(ζ_p)` へ降ろした。
  同じ底体の実際の非零元 `c` を得て `σ(b)=b^r c^p` を証明した。
- 底体の任意の自己同型の絶対持ち上げと円分指標の一致を内部供給した。
- 実際の商群 `Fˣ/(Fˣ)^p` と底体自己同型による写像を構成した。
  同じ定数の類が非自明で、`γ[b]=[b]^(ω(γ)^2)` を満たすことを証明した。
- 同じ商を加法的な `F_p` 加群に読み、同じ非零ベクトルへの線形な二乗固有条件も証明した。
- Frey の非分裂から、同じ指標・同じ固定体・同じ表示による非零 `ω²` 類とベクトルを供給する。
  類・固有性・持ち上げ・表示・開核・共役則・全射性の provider は追加していない。

今回の `KummerClass` は体の乗法群の冪による商であり、円分類群 `Cl(F)` ではない。
`b` そのものの固有等式とはせず、補正因子 `c^p` を保持する。
整数化、素イデアルの付値と不分岐条件、類群・単数の該当成分への接続と消滅は残る。
元の共鳴住所の吸収を供給する幾何と巡回塔の反復も未実装である。
**一般 `hno` は未完成。** 最終計数経路の `hCH` 除去は保たれている。


## 2026-11-02 追補: 同じベクトルの整数化、Selmer 付値と条件付き類群捩れ

教科書: `TEXTBOOK-N032-CYCLOTOMIC-KUMMER-ARITHMETIC-261102.md`。
実装: `CyclicKummerIntegral`、`KummerSelmer`、`CyclotomicKummerArithmetic`、
`FreyCyclotomicKummerArithmetic`。

- 同じ表示を `α'=cα,b'=c^p b` に変え、生成する体と既約性を保った。
- 数体の非零整数による分母払いを内部構成し、根・定数を実際の両整数環の非零元にした。
- 同じ Kummer 類・ベクトルとの等式を証明し、元の非零 `ω²` ベクトルを保った。
  Frey の非分裂から整数モデルとこの一致・非零性・固有性・全素点の付値剰余の一致を供給する。
- 同じ商上の付値の線形写像と共通核を構成し、Mathlib の `S=∅` Selmer 群との一致を証明した。
- 同じ主分数イデアルの指数と付値の符号を明示し、所属と全指数の `p` 可除性との同値を証明した。
- その可除性が満たされる場合、有限支持の指数を `p` で割って、同じ主分数イデアルの実際の
  非零冪根 `J` を構成した。正の指数では非零冪根が一意であることも証明した。
- Selmer 所属を明示入力に残す一般定理で `J^p=(x)` と、実際の `ClassGroup R` における
  `[J]^p=1` を得た。所属を元の Frey ベクトルに対して内部供給したわけではない。
- 整数環の実際の単元由来の類が付値部分加群へ入ることを、Mathlib の単元写像から供給した。

`ℚ(i)` の分数根 `i/2` の整数化を回帰検証する。
整数 `2` の主分数イデアルの `(2)` での指数は1であり、`p=5` の付値条件を満たさないことも検証する。
整数化は Selmer 所属や単元性を意味しない。整数化の前後で付値剰余と所属は変わらない。

元の同じ非零 Frey ベクトルの Selmer 所属、局所固定性から全素点の付値条件への接続、
共鳴住所の吸収と `p` 上の局所 `p` 乗条件は残る。
類群への商上の写像の代表元独立性・同変性・完全列と、類群・単数の該当成分の消滅、
巡回塔の反復も未完成である。新たな所属・消滅 provider は Frey 終点へ追加していない。
**一般 `hno` は未完成。** 最終固定点計数は引き続き `hCH` を必要としない。


## 2026-11-02 追補: Selmer 類群写像、群の短完全列、同じ単元への復帰

教科書: `TEXTBOOK-N032-CYCLOTOMIC-KUMMER-CLASS-MAP-261102.md`。
実装: `KummerSelmerClassMap`、`KummerSelmerExact`、`CyclotomicKummerClassMap`、
`FreyCyclotomicKummerClassMap`。

- 非零分数イデアルの冪根の一意性から、代表元を `x=c^p y` と変えると根が `(c)` 倍だけ変わることを証明した。
- 根の類群像の代表元独立性、積と1の保存を証明し、実際の準同型
  `Selmer(∅,p) → ClassGroup R` と `Cl(R)[p]` への値域制限を構成した。
- 同じ付値部分加群からの `ZMod p` 線形写像も構成した。
- 類群像が零なら同じ代表元が `x=ι(ε)c^p` と書けることを、実際の `ε∈Rˣ,c∈Fˣ` で証明した。
- Mathlib の実際の単元写像の核を使い、単元冪商の単射性を証明した。
  その像と類群写像の核の一致、類群 `p` 捩れへの全射性も証明した。
- `short_exact` は、この実際の二つの群準同型の単射性・核と像の一致・全射性を返す。
  一般の Dedekind 整域と分数体、正の指数で成立し、完全性の provider は要求しない。
- 元の同じ円分 Kummer 類の `classImage` と整数化前後の像の一致を構成した。
  その像が零なら、同じ非零ベクトルを非自明な単元冪商の類として表す。
- Frey には条件付きの受け口を追加した。`hval` と `hzero` は別々の明示入力として残り、
  以前の非分裂から表示・整数モデルを構成する定理の仮定は変更していない。

実際の整数単元 `-1` が非自明な Selmer 類を与えながら類群像が零となることを回帰検証する。
`-4` を同じ単元類の単元倍平方へ戻す例、指数1と指数0の境界も検証する。
類群像の零化は Kummer 類の零化ではない。

Galois 同変性は未実装である。類群像の `ω²` 固有性を線形性だけから結論しない。
元の同じ Frey ベクトルの Selmer 所属、類群・単数成分の消滅、局所 `p` 乗、
共鳴住所の吸収と巡回塔の反復も残る。**一般 `hno` は未完成。**
最終固定点計数の `hCH` 除去は保たれている。


## 2026-11-02 追補: 同じ Selmer 類の同変性と実際の類群の ω² 条件

教科書: `TEXTBOOK-N032-CYCLOTOMIC-KUMMER-EQUIVARIANCE-261102.md`。
実装: `KummerSelmerEquivariance`、`CyclotomicKummerEquivariance`、
`FreyCyclotomicKummerEquivariance`。

- 整域と分数体の埋め込みを保つ自己同型の組を明示し、半線形な分数イデアル移送を構成した。
  主イデアル `(x)` を同じ `(γx)` へ移すことを、局所化写像の一意性から証明した。
- 同じ主イデアルの根を移して全素点の指数の可除性を得ることで、Selmer 所属の保存を証明した。
  元の Frey ベクトルが所属することを供給する定理ではない。
- 正の指数での非零冪根の一意性から、選んだ根そのものの等式 `J_(γx)=γJ_x` を証明した。
- 商上の実際の類群写像、恒等・合成法則、実際の逆写像を構成した。
  数体では実際の整数環の制限を用いた Galois 群から類群自己同型群への準同型を構成した。
- 元の同じ `Φ` について `Φ(γz)=γΦ(z)` を証明し、類群 `p` 捩れへの制限と
  `ZMod p` 線形化、その恒等・合成法則を構成した。
- 元の円分 Kummer 類の二乗則をこの同変性で移し、同じ `classImage` の `ω²` 固有条件を証明した。
- Frey の受け口は同じ `S,L,K,m,v,P` を保ち、開核と共役則を同じ既存の指標から内部供給する。
  `hsurj` と元のベクトルの `hval` は明示する。同変性や類群像の零化の provider は追加していない。

実際の `ℚ(i)` の非恒等共役、`(2+i)` から `(2−i)` への移送と、実際の三乗の
Selmer 条件・選んだ根の移送を回帰検証する。類群作用の恒等・合成も検証する。
10入口の証明・型・コンストラクタの再帰監査と7入口の入力監査を追加した。

元の同じ Frey ベクトルの Selmer 所属、局所固定性からの全素点の付値条件への接続、
`p` 上の局所 `p` 乗、共鳴住所の吸収、単元側への固有条件の移送と算術的消滅、
類群成分の消滅と巡回塔の反復は残る。類群像は零でもよく、非零性や無条件の消滅を結論しない。
**一般 `hno` は未完成。** 最終固定点計数の `hCH` 除去は保たれている。


## 2026-11-02 追補: 同変な短完全列と同じ非零 ω² 単元類への還元

教科書: `TEXTBOOK-N032-CYCLOTOMIC-KUMMER-UNIT-EQUIVARIANCE-261102.md`。
実装: `KummerSelmerUnitEquivariance`、`CyclotomicKummerUnitEquivariance`、
`FreyCyclotomicKummerUnitEquivariance`。

- 整数側の実際の自己同型を単元冪商へ下ろし、恒等・合成・逆写像を証明した。
  同じ Selmer 群と類群捩れにも実際の自己同型を備えた。
- 同じ `unitInclusion` の同変性を、実際の整数環埋め込みの可換性から証明した。
  同変性の provider は要求しない。
- 数体の実際の Galois 群から単元冪商・Selmer 群・類群捩れの各自己同型群への
  準同型を構成した。同じ二つの写像の同変性と、既存の短完全列の三つの完全性条件をまとめた。
- 同じ Selmer 類の類群像が零なら、単元冪商での逆像が存在し一意であることを証明した。
  その一意な逆像の同変性と、元の類が非自明なら逆像も非自明であることを証明した。
- 元の Selmer 固有条件を、同じ単元埋め込みの単射性で同じ単元類へ戻した。
  `ZMod p` 線形化を構成し、元の二乗則から `unitImage` の `ω²` 固有性を証明した。
- 元の定数の同じ単元倍冪表示と元のベクトルとの一致を保ち、単元冪商の非自明性・
  一意な `unitImage` との一致・すべての底体 Galois 自己同型に対する固有性を返した。
  自己同型ごとに異なる単元を選ぶ結論ではない。
- Frey では同じ `S,L,K,m,v,P` を保ち、開核と共役則を同じ既存指標から内部供給する。
  `hsurj`、元の `hval`、同じ類群像の `hzero` は明示した。単元の存在・同変性・固有性を入力にしていない。

実際の `ℚ(i)` の共役による単元 `i` の作用と単元埋め込みの同変性、
実際の非自明な `−1` の単元類が同じ一意な逆像として残ることを回帰検証する。
`Z/9Z` の非零3捩れが3倍商では零となる例により、捩れと冪商の型の差も検証する。
12入口の証明・型・コンストラクタ再帰監査と9入口の入力監査を追加した。

元の Frey ベクトルの Selmer 所属、局所固定性から付値可除性への接続、`p` 上の局所 `p` 乗、
共鳴住所の吸収、類群・単元の算術的消滅と巡回塔の反復は残る。
`Cl(R)/pCl(R)` の消滅を `Cl(R)[p]` へ移す有限群の橋も未実装であり、直接同一視していない。
**一般 `hno` は未完成。** 最終固定点計数の `hCH` 除去は保たれている。


## 2026-11-03 追補: 類群の冪商から捩れへの固有成分消滅移送

教科書: `TEXTBOOK-N032-FINITE-EIGEN-TORSION-BRIDGE-261103.md`。
実装: `FiniteEigenTorsionBridge`、`CyclotomicClassVanishing`、`FreyCyclotomicClassVanishing`。

- 有限アーベル群の自己準同型に Fitting 分解を適用し、商上の核が零なら元の核の
  p 捩れが零であることを証明した。自然な `A[p] → A/pA` の単射性は要求しない。
- 標数 p の加群上の重み付き和が実際に指標 χ の固有条件を満たすことを証明した。
  元の同じ群上へ整数係数で持ち上げ、商での和との両立と、元の捩れ固有元での位数倍を証明した。
- 欠損準同型 `|Γ| id − S` に核補題を適用し、有限群・群の位数の標数での可逆性の下で
  商の固有成分消滅を捩れへ移した。汎用定理は正指数と可逆性を使い、素数性は要求しない。
- 同じ実際の数体の類群に適用した。類群の有限性は Mathlib の実際の構成から供給した。
  円分体の Galois 群の位数 p−1 と標数 p での可逆性も既存の同じ原始根から内部供給した。
- 元の同じ `classImage` の ω² 条件を使い、実際の商側の ω² 消滅を条件に同じ像の零化を導いた。
- Frey には同じ `S,L,K,m,v,P` を保つ入口を追加した。`hsurj`、元の `hval`、商の消滅 `hvanish` は
  明示入力であり、同じ類群像の `hzero` は内部で導く。そのまま以前の同じ非零単元類への還元へ接続した。

実際の `Z/9Z` の非零3捩れが商では零となる例、非自明な指標の商から捩れへの消滅移送、
整数持ち上げが元の群では `S(1)=3≠0` となる例を回帰検証する。
実際の3円分体の Galois 位数・可逆性、類群商の有限性と同じ作用との両立も検証する。
11入口の型・証明・コンストラクタ再帰監査、7入口の公開入力監査、2入口の有限性・係数条件監査を追加した。

商側の算術的類群消滅そのもの、上流の別の作用・商表示との比較、元の Frey ベクトルの Selmer 所属、
`p` 上の局所 p 乗、共鳴住所の吸収、局所条件付き単元消滅と巡回塔の反復は残る。
**一般 `hno` は未完成。** 最終固定点計数の `hCH` 除去は保たれている。


## 2026-11-03 追補: 元の Frey Kummer ベクトルの条件付き Selmer 所属

教科書: `TEXTBOOK-N032-CYCLOTOMIC-KUMMER-SELMER-261103.md`。
実装: `KummerLocalValuation`、`CyclotomicKummerSelmer`、`FreyCyclotomicKummerSelmer`。

- 同じ `α^p=b` に正規化付値を取り、実際の分岐指数を含む `p log v_w(α)=e log v_v(b)` を証明した。
  e=1 なら、元の同じ非零分数定数の主分数イデアルの指数が p 可除となる。
- 実際の有限相対慣性群が同じ生成根を固定すれば、生成性により慣性群が自明になることを証明した。
  慣性位数と分岐指数の比較から e=1 を内部で導いた。
- 有限整数環の相対慣性元を既存の絶対慣性持ち上げへ接続した。
  同じ M への制限と同じ ζ の固定性を保ち、元の円分指標核の元と同じ根の固定性へ戻した。
- 各有限素点の上の実際の素点を lying-over で供給し、全素点の指数の可除性を得た。
  既存の同じ `mem_valuationSpace_mk_iff` により、元の同じベクトルの hval を証明した。
- Frey では p 上の分解群固定性と p 外の慣性固定性を合わせた。
  hp5 と元の共鳴住所の hbad は変更せず明示し、同じ `S,L,K,m,v,P` の所属を内部供給する。
  実際の空集合支持 Selmer 群の所属も返す。
- 新しい単元還元の入口では hval と hzero を内部で導く。
  hp5、hbad、hsurj、実際の類群商の算術的消滅 hvanish は入力に残す。

実際の `ℚ(√2)` の整数環に `(2)` 上の素点を選び、分岐指数が1ではないことを回帰検証する。
同じ分数定数 `1/4` の指数が `−2` であることと、その平方根からの可除性も確認する。
9入口の型・証明・コンストラクタ再帰監査と8入口の公開入力監査を追加した。
新規全6 Lean ファイルには import 群直後の正確な `#print "file: モジュール名"` を置く。
教科書の各 Lean ブロックも import と同じモジュール表示を含む。

hbad の幾何学的解決、類群商の算術的消滅、p 上の局所 p 乗性、局所条件付き単元消滅と
巡回塔の反復は残る。p 上の固定性は今回は慣性・付値可除性に使い、局所 p 乗性とは同一視していない。
**一般 `hno` は未完成。** 最終固定点計数の `hCH` 除去は保たれている。


## 2026-11-03 追補: p 上の同じ有限分解群と e=f=1

教科書: `TEXTBOOK-N032-CYCLOTOMIC-KUMMER-DECOMPOSITION-261103.md`。
実装: `AbsoluteDecompositionLift`、`KummerDecomposition`、
`CyclotomicKummerDecomposition`、`FreyCyclotomicKummerDecomposition`。

- 有限整数環の素点の安定化元を絶対分解群へ持ち上げる存在定理を証明した。
  同じ有限正規体への制限と、同じ有理素数 p 上の住所を保つ。
  整数閉包の素点の推移性で延長を補正し、分数表示で付値環の保存を証明する。
  慣性持ち上げを分解群持ち上げと同一視せず、剰余体作用を打ち消さない。
- 同じ相対元が ζ を固定することを制限の等式で追い、元の円分指標核へ戻す。
  p 上の絶対分解群固定性から、同じ有限根の固定性を得た。
- 同じ生成根を固定する部分群が自明であることを証明し、実際の有限分解群 D_w=1 を得た。
  慣性位数と分岐指数、および |D_w|=|I_w|f の公式から同じ v,w で e=f=1 を証明した。
- Frey の3公開入口では、同じ S,L,K,m,v,P を保持し、数体構造は既存の開核定理から供給する。
  hbad、hval、hzero、hvanish、hsurj、有限分解群・局所次数の provider は要求しない。
  指定された P の存在と hp5 は保持する。非分裂から P を作る上流はそのままである。
- 実際の ℚ(√2) の整数環の (2) 上に素点を選び、D≠1 と e≠1 を回帰検証する。
  恒等拡大の同じ (2) では e=f=1 を確認する。
  11宣言の公理報告、11入口の再帰依存監査と11入口の公開入力監査を含む。
- 新規7 Lean ファイルと、ソースからそのまま掲載した教科書の2ブロックに、
  import 直後の正確な `#print "file: モジュール名"` を置く。

**完備化の局所次数と |D_w| の比較、同じ根の完備体への降下、同じ b の局所 p 乗根 t は未実装。**
e=f=1 を完備化の比較の代用品にせず、次は実際の埋め込みを保つ橋を実装する。
同じ単元 ε への局所冪の移送、hbad、類群商の算術的消滅、局所条件付き単元消滅と
巡回塔の反復も残る。**一般 hno は未完成。** 最終固定点計数の hCH 除去は保たれている。


## 2026-11-03 追補: 同じ根の完備体への降下と局所 p 乗性

教科書: `TEXTBOOK-N032-CYCLOTOMIC-KUMMER-LOCAL-POWER-261103.md`。
実装: `NumberFieldCompletionComparison`、`KummerLocalPower`、`FreyCyclotomicKummerLocalPower`。

- 同じ数体拡大 F→M、同じ整数環素点 v,w と lying-over から自然な完備化写像を構成した。
  元の包含と二つの完備化の埋め込みとの可換性を独立に証明した。
- f=1 から実際の剰余体写像の全射性を得て、局所整数の先頭の桁を底体の大域整数で合わせる。
  e=1 なら底体の一様化元は上の付値でも同じ正規化値を持つので、桁近似を反復できる。
  底体の一様化元の冪による拡縮で、上の体の任意の元を任意の非零半径まで近似した。
- この稠密性と、完備化写像の一様構造の誘導から得られる完備な閉像により、
  e=f=1 の場合の自然な完備化写像の全単射を証明した。
  同じ写像による拡大構造で局所次数1を導いた。一般の全ての e,f に対する次数公式は主張しない。
- 同じ P.radical の完備体への像を、同じ底体の完備体の非零元 t へ降ろした。
  上の根との一致と、元の同じ定数について t^p=b を同時に返す。
- Frey では既存の p 上の同じ有限分解群からの e=f=1 を適用した。
  底体の各 p 上の素点を入力とする入口は、上の素点を lying-over で内部選択する。
  指定された P、同じ S,L,K,m,v、hp5 は保持し、hbad・hvanish・hsurj・he・hf・
  局所次数・完備化の全射性・局所根の provider は入力に加えない。
- 同じ b=uc^p に対して同じ u の局所根 t/c を構成した。
  元の条件付き単元還元との合流では、同じ u,c、同じ非零単元類、同じ Kummer ベクトルとの一致、
  同じ ω² 固有条件を保持したまま、全 p 上の局所 p 乗条件を付けた。
  この合流では従来の hbad・hsurj・hvanish を明示し、hval・hzero は追加しない。
- 回帰検証は実際の2進完備体を使う。自然な恒等拡大の写像の一致と局所次数1、
  局所整数 1/3 の大域整数による桁近似、2 の平方根の不存在を確認する。
  b=1/4、ε=9、c=1/6、t=1/2 の移送では同じ t/c=3 を追跡する。
- 15宣言の公理報告、15入口の再帰依存監査・公開入力監査を追加した。
  新規6 Lean ファイルと、ソースをそのまま掲載した教科書の2ブロックに、
  import 直後の正確な `#print "file: モジュール名"` を保持する。

**同じ b の p 上の局所 p 乗性と、同じ単元への移送は今回接続済み。**
前節までに未実装と記録した完備化比較と根の降下は、上の e=f=1 の場合について閉じた。
共鳴住所の hbad、実際の類群商の算術的 ω² 消滅 hvanish、今回の局所条件を備える
実際の ω² 単元類の消滅、巡回塔の反復と最終接続は残る。
**一般 hno は未完成。** 最終固定点計数の hCH 除去は保たれている。


## 2026-11-04 追補: 実際の局所条件付き単元空間と条件付き非分裂排除

教科書: `TEXTBOOK-N032-CYCLOTOMIC-CONDITIONAL-SPLIT-261104.md`。
実装: `KummerLocalPrimaryUnit`、`CyclotomicPrimaryUnitSpace`、
`CyclotomicPrimaryCongruence`、`FreyCyclotomicConditionalSplit`。

- 外部の局所条件付き ω² 単元消滅の公開声明、局所3次合同の証明本体、最終証明接続を照合した。
  コミット・blob・ハッシュと確認範囲は `evidence/note032-primary-unit-external-proof-path.json` に保存した。
  外部の ω² 空間の次元1、Λ の構成・非零評価は、DkMath の型で証明すべき算術として残る。
- 同じ Dedekind 環の素点、同じ整数環単元 u、同じ実際の局所 p 乗根から、
  u^(p−1)−1∈v と p∈v² を保って u^(p−1)−1∈v³ を証明した。
  適応した一般証明と分岐素点の議論には Apache 通知と上流 blob を保持する。
- 同じ原始根 ζ のイデアル (ζ−1) で、p の分岐による所属と剰余体の濃度 p を内部供給する。
  同じ u の全 p 上の局所冪条件から、同じ原始根の素点で3次合同を得た。
- 同じ実際の整数環単元商から各完備体の Kummer 商への写像を構成した。
  局所条件をその核の共通部分として定義し、既存の同じ Galois 作用の ω² 空間と交差した。
  この部分空間の消滅と、同じ条件を持つ代表元が大域の単元 p 乗になる命題の同値も証明した。
  これは算術的消滅そのものの証明ではない。
- 同じ Frey の単元 u,c、元の Kummer ベクトルとの一致、同じ非零類を保持して、
  新しい部分空間への所属と同じ ζ の素点での3次合同を同時に返す。
  この証人の構成には、部分空間の消滅 hunit は不要である。
- hunit を明示入力とすると、同じ非零単元類から矛盾を得る。
  元の非分裂から v,P,hsurj を内部構成し、元の商表現の非分裂排除と大域安定な補空間を証明した。
  最終公開定理には v,P,hsurj,hns,hval,hzero を追加せず、hp5 と従来の巡回段の条件、
  共鳴住所の hbad、実際の類群商の hclass、実際の局所条件付き単元空間の hunit を保持する。
- 回帰例は F₇ の立方根の有無と商類・代表元の区別、および実際の5次円分体の
  剰余体濃度5、5∈(ζ−1)^4、(ζ−1)^2∉(ζ−1)^3 を確認する。
  実際の円分単元 c=1+ζ の5乗について、局所冪核の所属と3次合同も確認する。
- 13宣言の公理報告、13入口の再帰依存監査・公開入力監査を追加した。
  新規7 Lean ファイルと教科書の3ブロックは、import 直後の正確なモジュール表示を保持する。

**具体的な3次合同と、明示した算術仮定から元の非分裂排除・安定補空間までの接続は実装済み。**
hbad、実際の類群商の算術的消滅 hclass、実際の単元空間の算術的消滅 hunit、
巡回塔の反復と最終接続は残る。**一般 hno は未完成。**


## 2026-11-04: 実際の単元商上の切断対数と hunit への明示的二条件

- `CyclotomicTruncatedLog` は可換環の3次冪零イデアル上で
  ℓ(z)=(z−1)−h(z−1)², 2h=1 の加法性を証明する。
- `CyclotomicPrimaryLog` は同じ原始根の Q=𝓞 F/(ζ−1)³ を用いる。
  p の分岐から char Q=p を導き、λ³=0 と λ²≠0 を証明する。
  実際の単元群からの対数が p 乗を零に送ることを証明して、
  DkMath の実際の UnitClass に Λ を降ろした。
- 同じ単元の3次合同から Λ([u])=0、実際の局所冪空間の全元について Λ(x)=0 を証明した。
  𝔽p の実際の環写像 ι に関して Λ(a•x)=ι(a)Λ(x) を証明した。
- `CyclotomicPrimaryLogCriterion` は同じ `weightSquareSpace hζ` の
  次元1と、その空間内の g に対する同じ Λ(g)≠0 を明示入力として、
  `primaryWeightSquareSpace hζ = ⊥` を証明する。
  これが既存条件付き分裂の hunit に入る。次元計算と非零評価自体は未実装。
- 実際の5次円分体で、未補正対数の非加法性と補正後の加法性、ℓ(1+λ²)=λ²、
  同じ円分単元の5乗に対する Λ の零化と5乗による代表元変更の不変性を確認する。
  Q 内の非零値の検証と、大域 ω² 単元の非零評価は区別する。
- 新規3 production はすべて Lib 配下。外部消滅定理・FLT 末端を import しない。
  上流を参考にした2ファイルには Apache 著作権・通知・blob を保持する。
- 教科書 `TEXTBOOK-N032-CYCLOTOMIC-PRIMARY-LOG-261104.md` の3コードブロックは
  production 全文に一致し、各々 import 直後に正確な `#print "file: …"` を含む。

**今回閉じたのは「実際の局所冪条件 → 同じ単元商の Λ の零化」と、二条件から hunit への合成。**
ω² 空間の次元1・円分単元の射影の非零評価を供給していないため、hunit の算術的消滅は未完成。
hbad、hclass、巡回塔の反復も引き続き残る。**一般 hno は未完成。**
検証の詳細は `evidence/validation-note032-cyclotomic-primary-log.txt` を参照する。


## 2026-11-04: 2ステップ — 同じ ω² 射影子と同じ大域円分単元の非零評価

1. `CyclotomicOmegaSquareProjector` を実装した。
   実際の `unitClassLinearMap p (integerAut γ)` を表現としてまとめ、
   同じ `baseCharacter hζ` の ω² 平均射影 e₂ を `Module.End` として定義する。
   実際の群の位数 p−1 と可逆性を内部供給し、像が `weightSquareSpace hζ` と一致すること、
   固有空間上の恒等性・冪等性を証明した。同じ指定根の指標同型も構成した。
2. `CyclotomicPrimaryLogNonzero` を実装した。
   同じ大域円分単元 c=1+ζ とその射影 g=e₂[c] を実際に構成する。
   同じ根・同じ整数環作用による共役の式を証明し、有限体上の重み付き和を計算した。
   DkMath の同じ Λ について Λ(g)=−h³λ²≠0 を証明した。
   可逆な h の逆元のみを使用し、3次商を整域と仮定していない。
   g≠0 と同じ固有空間が零でないことも、次元1を仮定せず証明した。

- 前段の「商環内の 1+λ²」の計算と違い、今回は実際の大域単元の ω² 射影の非零評価である。
- `primaryWeightSquareSpace_eq_bot_of_rank_one` は具体的な g と hdetect を内部供給する。
  以前の二条件のうち非零検出は閉じ、残る単元側の算術入力は同じ空間の次元1である。
- `FreyCyclotomicPrimaryLogSplit.lean` 内の
  `DkMath.FLT.Frey.Source.residual_cyclic_extension_has_stable_complement_of_unit_rank_one` で
  同じ大域分裂へ接続した。
  公開入力には hunit・g・hdetect・v・P・hsurj・hns を残さず、hrank を明示する。
  hbad・hclass・巡回段の全安定性・位数・底の包含条件は従来どおり保持する。
- 回帰例は実際の原始5乗根・原始7乗根の同じ rootField を使う。
  p=5 では Λ(g)=3λ² の符号・正規化と、元の円分単元が整数環単元の5乗でないことも確認する。
- 教科書 `TEXTBOOK-N032-CYCLOTOMIC-OMEGA-SQUARE-DETECTION-261104.md` の3ブロックは
  新規 production 全文に一致し、すべて import 直後の正確な `#print "file: …"` を保持する。
- 14宣言の公理・再帰依存監査と6件の公開入力監査を追加した。
  検証記録は `evidence/validation-note032-cyclotomic-omega-square-detection.txt`。

**射影子と実際の大域円分単元の非零検出という、今回の2ステップは完成。**
同じ ω² 単元空間の次元1 hrank、hclass、hbad、巡回塔の反復は未完成である。
非零元の存在と finrank の正値は有限次元性なしに同一視しない。**一般 hno は引き続き未完成。**


## 2026-11-05: 2ステップ — 単元商の有限次元性と正確な次元

1. `NumberFieldUnitPowerDimension.unitClassFinite` で、Dirichlet の有限生成性の
   全射像として同じ実際の UnitClass の有限生成性を証明した。
   一般の数体と任意の指数で成立し、素数指数では有限次元性を供給する。
   別の ModP 商への取り替えや新しい有限性 provider は使わない。
2. 同じ単元商に、捩れ群の巡回生成元と Dirichlet の基本単元からなる実際の基底を構成した。
   p が実際の捩れ位数を割る場合の次元 rank(F)+1 を証明する。
   円分体では同じ原始根がその割り切りを内部供給する。
   無限素点の個数と合わせ、同じ rootField の単元商の次元 (p−1)/2 を無条件に証明した。

- 有限次元性を確立した後、前段の同じ非零固有元から
  0<finrank(weightSquareSpace hζ)≤(p−1)/2<p を証明した。
- 同じ既存 omegaSquareProjector の冪等性と像の一致により、
  trace(e₂)=(finrank(weightSquareSpace hζ):ZMod p) を証明した。
- 厳密な次元上界を使い、同じ射影子の trace=1 と同じ空間の自然数次元1の同値を証明した。
  `primaryWeightSquareSpace_eq_bot_of_trace` は trace=1 を htrace 入力に保持する。
  **この同値は残条件の整理であり、trace=1 の算術的証明ではない。**
- 実際の原始5乗根・7乗根の同じ rootField で単元商の次元2・3を確認する。
  同じ固有空間の正の次元と上界、射影子の実際の trace 等式、
  6=1 mod 5 と 6≠1 in ℕ の例で自然数上界の必要性も確認する。
- 2 production を Lib/root、2 test を通常の DkMathTest 入口へ公開した。
  既存の Frey 分裂定理の公開入力は変更せず、hrank・hbad・hclass が必要なままである。
- 教科書 `TEXTBOOK-N032-CYCLOTOMIC-UNIT-DIMENSION-261105.md` の2ブロックは
  production 全文に一致し、import 直後の正確な `#print "file: …"` を保持する。
- 13宣言の公理・再帰依存監査と8件の公開入力監査を追加した。
  記録は `evidence/validation-note032-cyclotomic-unit-dimension.txt`。

**今回の2ステップ（有限次元性と単元商全体の次元公式）は完成。**
同じ unitAction のトレースの捩れ・自由部分への分解、対数埋め込みと無限素点の置換作用の比較、
同じ射影子の trace=1 の算術的証明は未実装である。一般の hrank は未完成。
hclass・hbad・巡回塔の反復も残り、**一般 hno は引き続き未完成。**


## 2026-11-05: 2ステップ — 単元作用の捩れ／自由トレースと対数置換表現

1. `NumberFieldUnitGaloisTrace` で既存の同じ integerAut から単元作用を取り、
   捩れ群の安定性と実際の自由商への作用を構成した。
   同じ自由商上の `freeUnitAction` は合成・単位元を保つ群準同型である。
   前段の同じ UnitClass の捩れ・基本単元基底の対角成分を計算し、
   mod p の全トレースが捩れ成分 n と自由商の整数 trace の mod p 像の和であることを証明した。
   一般形には実際の hdiv と全 p 乗根への作用 hσ が必要であり、明示入力として保持する。
2. `NumberFieldUnitLogTrace` で全無限素点への重み付き対数を構成した。
   核が同じ捩れ単元群であることを証明して同じ自由商へ降ろし、
   実際の素点置換表現との同変性を証明する。
   Dirichlet 基底の対数像と定数関数直線との補空間分解を証明した。
   同じ整数自由作用行列の係数を実数へ写して trace を比較し、
   自由商の整数 trace = 同じ Galois 元が固定する無限素点数−1 を証明した。

- 最終的に、同じ rootField・characterEquiv・既存 unitAction について
  trace(ρ_d)=d+(#Fix(d):ZMod p)−1 を証明した。
  同じ原始根から整数環のすべての p 乗根への d.val 乗作用を導くことで、
  hdiv/hσ を内部供給する。最終の公開入力にトレース・固定点数 provider はない。
- 基本単元が Galois 不変であるとは仮定せず、混ざった捩れ因子を保ったまま対角成分を比較した。
  整数と実数のトレースは同じ作用行列の Int.cast を介して比較し、
  さらにその整数 trace を明示的に ZMod p に写した。
- 回帰例は3座標の2点交換の trace=1 と、実際の5次円分体の非自明な d=2 を使う。
  同じ全5乗根への2乗作用・対数の同変性・整数／mod 5 trace の接続を確認し、
  恒等 Galois 元の全トレースは前段の次元公式から2と確認する。
- 新規2 production は Lib/root、2 test は通常の DkMathTest 入口へ接続した。
  教科書 `TEXTBOOK-N032-NUMBER-FIELD-UNIT-TRACE-261105.md` の2ブロックは全文一致し、
  import 直後の正確な `#print "file: …"` を保持する。
- 主要11宣言の公理・再帰依存監査、8件の公開入力監査を追加した。
  詳細は `evidence/validation-note032-number-field-unit-trace.txt`。

**今回の2ステップは完成。**
同じ円分体の #Fix(d) の d=±1 による分類と、同じ射影子の重み付きトレース和は未実装。
従って trace(e₂)=1・一般 hrank はまだ未完成である。
hclass・hbad・巡回塔の反復も残り、**一般 hno は引き続き未完成。**


## 2026-11-06: 2ステップ — 固定無限素点と同じ射影子の trace=1、単元側算術の完成

1. `CyclotomicInfinitePlaceFixed` を実装した。
   同じ rootField・原始根・characterEquiv を保持し、逆自己同型の指数 d⁻¹ を明示する。
   同じ複素埋め込みが一致する場合と複素共役で一致する場合を分け、
   任意の無限素点 w について σd•w=w ↔ d=1∨d=−1 を証明した。
   同じ円分体の無限素点数により、固定点数が (p−1)/2 または0となることを証明した。
2. `CyclotomicOmegaSquareTrace` を実装した。
   既存の同じ unitAction の実際のトレースに固定点数を代入する。
   既存の同じ omegaSquareProjector の有限和表示にトレースを適用し、
   有限体の逆冪和と d=±1 の指示関数和を計算して trace(e₂)=1 を証明した。
   その結果、同じ weightSquareSpace の自然数次元1と同じ primary 単元空間の零化を
   hrank/htrace/hdetect/hunit の provider なしで証明した（素数 p≥5）。

- `exists_global_unit_pow_of_primary` は同じ整数環単元 u の実際の固有・局所条件から、
  同じ整数環の大域単元 a の存在 a^p=u を返す。
- `FreyCyclotomicUnitSplit.lean` の
  `DkMath.FLT.Frey.Source.residual_cyclic_extension_has_stable_complement_of_class_vanishing`
  は、単元側の算術入力をすべて内部供給して同じ Frey 分裂へ接続した。
  公開入口に hrank/htrace/hunit/hdetect/g/v/P/hsurj/hns を残さない。
  **hbad・実際の hclass・同じ巡回段の全安定性・位数・底の包含条件は保持する。**
- 回帰例は実際の5次・7次円分 rootField を使用する。
  5次では d=2 の逆作用の指数3、固定点数2/0、d=−1 の全トレース0と d=2 の全トレース1、
  同じ射影子の trace=1・同じ空間の次元1・primary 単元消滅を確認する。
  同じ固有・局所条件の整数環単元の大域5乗根の存在も確認する。
  7次では d=−1 の固定点数3と、同じ trace/次元/消滅を確認する。
- 新規3 production を Lib/FLT/root、2 test を通常の DkMathTest 入口へ公開した。
  教科書 `TEXTBOOK-N032-CYCLOTOMIC-UNIT-CLOSURE-261106.md` の3ブロックは全文一致し、
  import 直後の正確な `#print "file: …"` を保持する。
- 主要12宣言の公理・再帰依存監査、8件の公開入力監査を追加した。
  詳細は `evidence/validation-note032-cyclotomic-unit-closure.txt`。

**今回の2ステップと、単元側の hrank/hunit の算術実装は完成（素数 p≥5）。**
同じ円分類群商の hclass、共鳴素点での hbad、巡回塔の反復と最終接続は残る。
**一般 hno は引き続き未完成。**


## 2026-11-06: 2ステップ — 算術条件付き次段から同じ巡回塔・合併へ

1. `FreyCyclotomicTowerStep` の `ResidualCyclicStage` は同じ Source と同じ L を固定し、
   同じ点群内の部分群・位数 p^(n+1)・巡回性・Galois 安定性・元の底への包含を保持する。
   有限性、指数による零化、p-socle の元の底への降下は不変量から内部導出する。
   第0段は元の pointSubgroup から構成し、hbad/hclass を要求しない。
   次段は以前の実際の hbad/hclass 付き安定補空間から持ち上げ、
   その存在・位数・巡回性・安定性・底の包含・socle の降下を出力する。
2. `FreyCyclotomicConditionalTower` で次段を選び、Nat.rec により同じ底のもとで反復した。
   各 n で無関係な部分群を選ぶのでなく、隣接包含を持つ同じ単調な塔を構成する。
   同じ次段内の実際の p 倍の逆像も、有限巡回群の p 倍像=核公式から導く。
   同じ点群内の合併は Galois 安定・p-primary・p-divisible・無限であり、
   その p-socle は元の同じ pointSubgroup と正確に一致する。

- hclass は従来の同じ ClassModP の特定 ω² 固有成分の消滅のまま保持する。
- 一段では同じ p•y∈K の共鳴素点条件 `ResonantAbsorptionAt K` が必要。
  反復ではそれをすべての適格な段に供給する hbad を明示入力にする。
  **これは一つの K の hbad より強い段ごとの入力であり、保存性を算術的に証明したものではない。**
- 次段存在・指標消滅・分裂・hrank/htrace/hunit を新しい provider として仮定しない。
  前回完成した実際の単元算術と同じ Frey 分裂をそのまま利用する。
- 2回の互換な p 倍逆像から、元の底の点の p² 倍の逆像が同じ第2段へ入る回帰例を確認する。
  段0/1/2の位数 p,p²,p³、第4段の socle の元の底への降下、
  合併の可除性と Infinite なのに Nat.card=0 となる区別も確認する。
- 新規2 production を FLT/root、2 test を通常の DkMathTest 入口へ公開した。
  教科書 `TEXTBOOK-N032-FREY-CONDITIONAL-TOWER-261106.md` の2ブロックは全文一致し、
  import 直後の正確な `#print "file: …"` を保持する。
- 主要15宣言の公理・再帰依存監査、8件の公開入力監査を追加した。
  詳細は `evidence/validation-note032-frey-conditional-tower.txt`。

**今回の2ステップは条件付きの実際の巡回塔構成として完成。**
外部の類群 ω² 消滅 source は Thaine 関係等を使う経路として照合したが、今回移植していない。
hclass、各段の hbad、高位捩れ全体の慣性吸収、良還元点数による最後の大域矛盾は未完成。
Galois 安定性を商の自明作用と混同せず、**一般 hno は引き続き未完成。**


## 2026-11-06: 2ステップ — 同じ巡回塔の有限単元値指標と剰余両立性

1. `CyclicActionCharacter` を実装した。
   巡回座標 e:ZMod N≃+G と実際の群作用から、係数 e⁻¹(ρ(g)(e(1))) を構成する。
   合成則と群の逆元から単元値指標を内部構成し、N≠0 で同じ元への scalar 作用を証明した。
   指標値1と全点固定性の同値、巡回座標を取り替えても同じ指標となることを証明した。
2. `FreyCyclicTowerCharacter` を実装した。
   同じ Source・同じ実際の巡回段へ同じ pointAction を制限して指標を構成した。
   全捩れ表現の開核から各段の指標の開核を証明した。
   同じ段の包含に沿う標準剰余写像との両立性と、mod p で元の円分指標になることを証明した。
   以前の条件付き塔へ適用し、同じ塔の実際の指標族と隣接両立性を得た。

- 任意の既存段の指標・開核・包含に沿う両立性は hclass/hbad を追加要求しない。
  元の直線の円分指標との一致には同じ hline/hcofixed を保持する。
  塔全体の構成には以前と同じ hclass と全適格段での hbad が引き続き必要である。
- 既存の固定捩れ還元定理は点ごとの Frobenius 固定性を要求する。
  商上の作用差吸収を使う定理は、高位捩れ全体での吸収を要求する別の経路である。
  新しい良還元上界は具体的な Frobenius 指標値1を明示入力に残す。
  これは十分条件であり、この値1を算術的に導いたものでも、最終経路をこれに限定したものでもない。
- 実際の ZMod 5 の単元作用で、全群は安定だが−1が1を動かす回帰例を確認した。
  座標の符号変更に対する指標の不変性、同じ塔の二段分の剰余両立性も確認した。
- 新規2 production を Lib/FLT/root、2 test を通常の DkMathTest 入口へ公開した。
  教科書 `TEXTBOOK-N032-FREY-TOWER-CHARACTER-261106.md` の2ブロックは全文一致し、
  import 直後の正確な `#print "file: …"` を保持する。
- 主要11宣言の公理・再帰依存監査、10件の公開入力監査を追加した。
  ルートビルド・lake test・通常テスト入口・root smoke・教科書個別コンパイルを確認した。
  詳細は `evidence/validation-note032-frey-tower-character.txt`。

**今回の2ステップは同じ有限単元値指標とその両立性として完成。**
hclass、各段の hbad、最終矛盾に必要な Galois 作用の追加算術は未完成。
Zp 指標への極限や Tate 加群はまだ構成していない。
Galois 安定性を点ごとの固定性と混同せず、**一般 hno は引き続き未完成。**


## 2026-11-06: 2ステップ — 同じ塔の連続 p 進指標と良還元 Frobenius の非自明性

1. `PadicCharacterLimit` を実装した。
   法 p^(n+1) の両立する単元値指標から、法1の成分を補った整数代表列を取る。
   隣接差の p 冪可除性、実際の Cauchy 極限、元の有限剰余との一致を証明した。
   剰余外延性から乗法性を導き、群の逆元で単元値へ持ち上げる。
   同じ有限剰余を持つ指標の一意性、全有限値1との同値を証明した。
   有限段の開核から p 進ノルムの近傍評価を導き、極限指標の連続性を証明した。
   無限段の核の開性は主張しない。
2. `FreyPadicTowerCharacter` を実装した。
   同じ Source・同じ条件付き塔の有限指標と以前の両立性を代入し、実際の ℤₚˣ 値指標を構成した。
   元の有限段の剰余、連続性、mod p で元の円分指標と一致することを証明した。
   極限指標値1は、同じ実際の塔の合併内の全点固定と正確に同値である。
   良還元点数 N=#E(𝔽ℓ) に対し、n≥N の同じ段は Frobenius 指標が非自明となる。
   段 N の存在と正確な有限剰余から、極限 Frobenius 指標の非自明性も証明した。

- 有限段の非自明性は実際の段 T と同じ良還元素点・付値・Frobenius の条件のみで成立する。
  hclass/hbad/hchar/hfixed を追加要求しない。
- 極限の Frey 適用は、以前の同じ hclass と全適格段での hbad を保持する。
  新たな hlimit/hcompat/hcont/hchar provider を要求しない。
- 非自明性は矛盾ではない。mod p の一致から高位固定性を結論しない。
  実際の Frobenius の存在、高位特性多項式、Tate 部分加群やイソジェニー分類は今回構成していない。
- 具体的な5進単元群の全標準有限剰余から、元の任意の単元を正確に復元する回帰例を確認した。
  実際の単元6 mod 25（逆元21）は mod 5 で1だが mod 25 で非自明であることも確認した。
  同じ既存段で、良還元点数から非自明性と実際に動く点の存在を確認した。
- 新規2 production を Lib/FLT/root、2 test を通常の DkMathTest 入口へ公開した。
  教科書 `TEXTBOOK-N032-FREY-PADIC-CHARACTER-261106.md` の2ブロックは全文一致し、
  import 直後の正確な `#print "file: …"` を保持する。
- 主要13宣言の公理・再帰依存監査、10件の公開入力監査を追加した。
  詳細は `evidence/validation-note032-frey-padic-character.txt`。

**今回の2ステップは実際の連続 p 進指標と定量的 Frobenius 非自明性として完成。**
hclass、全段 hbad、最終矛盾の Galois 作用の追加算術は未完成。
Tate 加群の階数1部分加群はまだ構成していない。
**一般 hno は引き続き未完成。**


## 2026-11-06: 2ステップ — 実際の加法 Tate 点列と同じ塔の互換生成元

1. `PrimePowerTateSequence` を実装した。
   同じ加法可換群 G 内で、p^(n+1)•xₙ=0 と p•xₙ₊₁=xₙ を満たす列を
   G^ℕ の加法部分群として構成した。通常の第0零成分を除いた添字である。
   評価準同型・零化・遷移・外延性、準同型の成分ごとの写像とその単射性を証明した。
   元の同じ群作用から成分ごとの実際の作用を構成した。ℤₚ 加群構造はまだ追加しない。
2. `FreyCyclicTateVector` を実装した。
   同じ塔の第0生成元を選び、既存の同じ次段内 p 倍逆像から依存再帰で点列を構成した。
   pⁿ•eₙ=e₀≠0 と同じ段の零化から、各 eₙ の位数 p^(n+1) を証明した。
   生成部分群の濃度と同じ段の実際の濃度を比較し、ℤeₙ=Kₙ を証明した。
   各成分が同じ Kₙ に属する Tate 点列の加法部分群を定義し、全幾何学的点の
   Tate 点列群への自然な加法単射とその Galois 同変性を証明した。
   選んだ互換生成元はその部分群の実際の非零点列となる。

- 同じ点列 e の固定性 σ(e)=e と、元の同じ p 進指標 χ∞(σ)=1 は正確に同値である。
  各成分の生成性と以前の合併の全点固定性判定を使う。
- 同じ良還元素点・付値・Frobenius の入力のもとで、その Frobenius が e を動かすことも証明した。
  非固定性は以前の指標非自明性の点列上の実現であり、それ自体は矛盾ではない。
- 以前と同じ hclass と全適格段での hbad を保持する。
  hgen/hnext/hvector/hnonzero/hfixed/hchar/hmoved を新たな provider として要求しない。
- ZMod 25 の5進 Tate 点列が零となる回帰例で、有限段の非零元と互換無限点列を区別した。
  同じ塔の第2点の p² 倍逆像・正確な位数 p³・点列内の同じ第2成分、
  全点群の Tate 点列への包含後も非零となることを確認した。
- 新規2 production を Lib/FLT/root、2 test を通常の DkMathTest 入口へ公開した。
  教科書 `TEXTBOOK-N032-FREY-TATE-VECTOR-261106.md` の2ブロックは全文一致し、
  import 直後の正確な `#print "file: …"` を保持する。
- 主要12宣言の公理・再帰依存監査、10件の公開入力監査を追加した。
  詳細は `evidence/validation-note032-frey-tate-vector.txt`。

**今回の2ステップは、実際の加法 Tate 点列と同じ互換生成元の構成として完成。**
ℤₚ 加群構造・階数1線形同型・scalar 作用公式、合併 U の Tₚ(U) との同定、
Tₚ(E) の階数2・Weil pairing・Frobenius 特性多項式はまだ証明していない。
hclass・全段 hbad・最終矛盾の作用算術も未完成であり、**一般 hno は引き続き未完成。**


## 2026-11-06: 2ステップ — 標準 p 進加群と同じ Tate 直線の階数1線形同型

1. `PrimePowerTateModule` を実装した。
   同じ全点列上で (a•x)ₙ=(a mod p^(n+1)).val•xₙ と定義した。
   N で消える元への倍作用が法 N の剰余だけで決まることを証明し、
   元の点列の零化・隣接遷移・標準剰余写像から scalar の閉性と全加群公理を導いた。
   元の加法準同型と成分ごとの群作用も、同じ写像のまま ℤₚ 線形化した。
   一般の互換剰余列（単元に限らない）を実際の Cauchy 極限へ復元する API も証明した。
2. `FreyCyclicTateLine` を実装した。
   同じ Source・塔・互換生成元を保持し、以前の同じ点列部分群を標準 scalar の部分加群とした。
   全点群の Tate 加群への自然な包含は線形単射となる。
   同じ各段の生成元を1の像とする座標を作り、任意の点列の実際の係数を読む。
   点列と生成元の互換性から、係数の標準剰余両立性を証明した。
   a↦a•v は剰余外延性で単射、同じ係数の実際の Cauchy 復元で全射となる。
   従って ℤₚ≃ₗ[ℤₚ]同じTate直線という実際の階数1線形同型を構成した。

- 標準加群構造はこの線形同型より先に零化条件から構成している。
  同型で運び込んだ抽象 scalar を元の点作用と同一視したのではない。
- 任意の同じ直線の点列 x について、実際の Galois 点作用は χ∞(σ)•x と等しい。
  同じ有限段の character_spec と以前の p 進指標の剰余公式を比較した結果である。
  線形包含後も同じ全点群の線形作用と scalar 作用が一致する。
- 同じ hclass と全適格段での hbad を保持する。
  hmodule/hrank/hfree/hsurj/hequiv/hscalar を新しい provider として要求しない。
- 任意の5進整数の標準剰余からの復元と、非単元5の非零性を回帰例で確認した。
  同じ Frey 点列の p•v は第0成分が零でも全体で非零であり、
  任意の点列の線形同型での往復と、同じ包含の線形性も確認した。
- 新規2 production を Lib/FLT/root、2 test を通常の DkMathTest 入口へ公開した。
  教科書 `TEXTBOOK-N032-FREY-TATE-LINE-261106.md` の2ブロックは全文一致し、
  import 直後の正確な `#print "file: …"` を保持する。
- 主要13宣言の公理・再帰依存監査、10件の公開入力監査を追加した。
  詳細は `evidence/validation-note032-frey-tate-line.txt`。

**今回の2ステップは、標準 ℤₚ 加群・同じ階数1線形同型・線形包含・実際の scalar 作用公式として完成。**
合併 U の捩れと各 Kₙ の一致／Tₚ(U) との同定、Tₚ(E) の階数2、Weil pairing、
Frobenius 特性多項式、点列群の位相はまだ追加していない。
hclass・全段 hbad・最終矛盾の作用算術は未完成であり、**一般 hno は引き続き未完成。**


## 2026-11-06: 2ステップ — 合併の全低位捩れと標準 Tate p U の同定

1. `CyclicPrimePowerTorsion` を実装した。
   位数 pᵇ の有限巡回群 K に含まれる位数 pᵃ の B（a≤b、pᵃ で零化）について、
   pᵃ 倍核の実際の濃度 gcd(pᵇ,pᵃ)=pᵃ と包含の単射を比較し、K[pᵃ]=B を証明した。
   この群論は p の素数性を必要とせず、巡回性・濃度・包含・零化は保持する。
2. `FreyCyclicTateUnion` を実装した。
   既存の同じ二段に上の補題を適用し、合併所属を有限段へ戻すことで、
   全ての n で U[p^(n+1)]=Kₙ を証明した。
   主張は同じ U 内の捩れであり、全幾何学的捩れ全体の同一視ではない。
   同じ U を標準 Tate 点列定義へ代入した Tate p U から以前の同じ直線へ自然な線形写像を構成した。
   逆向きは同じ Kₙ の点を U の点とみなすだけであり、自然な線形同型を得た。
   以前の階数1同型を合成し、ℤₚ≃ₗ[ℤₚ]Tate p U を実際に構成した。

- 自然な同定の前後で全点群の Tate 加群内の点列は変わらない。
  元の U への点作用の制限・標準線形 Tate 作用・全点群への包含の同変性を証明した。
  標準 Tate p U の全点列への作用は以前の同じ χ∞ の scalar 倍である。
- 元の同じ非零生成元点列 v は、全幾何学的点の Tate 加群の p 倍に属さない。
  任意の p•w の第0成分は0だが v の第0成分は同じ e₀≠0 であることを使う。
  全 Tate 加群の自由階数2や基底への拡張はこの定理で仮定・証明していない。
- 有限段の群論は新たな hclass/hbad を必要としない。
  同じ合併・標準 Tate p U の構成には従来の hclass と全適格段の hbad を保持する。
  htorsion/hequiv/hrank/hfree/hscalar/hprimitive を新しい provider にしない。
- 実際の ZMod 125 の25捩れと、非巡回な ZMod 5×ZMod 5 の軸外の5捩れを回帰例で検査した。
  同じ第4段の p² 捩れが同じ第1段へ戻ること、Tate p U の同定での往復・同じ第3成分も確認した。
- 新規2 production を Lib/FLT/root、2 test を通常の DkMathTest 入口へ公開した。
  教科書 `TEXTBOOK-N032-FREY-TATE-UNION-261106.md` の2ブロックは全文一致し、
  import 直後の正確な `#print "file: …"` を保持する。
- 主要13宣言の公理・再帰依存監査、10件の公開入力監査を追加した。
  詳細は `evidence/validation-note032-frey-tate-union.txt`。

**今回の2ステップは、同じ合併の全 p 冪捩れと標準 Tate p U の自然な線形同定として完成。**
全 Tate 加群の階数2・原始元の基底への拡張・Weil pairing・Frobenius 特性多項式は未完成。
点列群の位相や作用の連続性も今回追加していない。
hclass・全段 hbad・最終矛盾の作用算術も未完成であり、**一般 hno は引き続き未完成。**


## 2026-11-06: 3ステップ — 第0評価の完全性・全 Tate 商 mod p・同じ直線の還元

1. `PrimePowerTateReduction` を実装した。
   第0評価 Tate p G→G[p] の核は、同じ Tate 点列内の p 倍像と証明した。
   第0成分が零なら一段シフトが実際の p 倍逆像となり、p 倍写像自体は単射でもある。
   G の p 倍全射性がある場合には、直前の点の逆像を依存再帰で選び、
   第0評価の全射性と Tate p G/p(Tate p G)≃+G[p] を構成した。
   汎用加法群論では p の素数性は不要で、全射性の hdiv は明示保持する。
2. `EllipticTateReduction` を実装した。
   同じ標数0楕円曲線の実際の multiplication_surjective から hdiv を内部供給した。
   標準 Tate 商 mod p は、同じ実際の E[p] と ZMod p 線形同型となる。
   商の実際の濃度 p²・次元2を既存の有限捩れ次元から導いた。
   第0評価は元の同じ Galois 点作用と可換する。
3. `FreyCyclicTateReduction` を実装した。
   同じ直線 C について p•x∈C↔x∈C を、隣接段と低位捩れ判定から証明した。
   第0評価を元の同じ L へ制限し、同じ U の既存可除性と互換逆像列から全射性を導いた。
   第0成分が零の全 Tate 逆像は p 飽和性で C 内へ戻り、C 自身でも核=p 倍像となる。
   標準商 C/pC≃ₗ[ZMod p]L と実際の次元1、全加群の還元との同じ点の図式を証明した。

- 全 Frey Tate 商 mod p の次元2は、同じ曲線の楕円曲線性から供給し、hclass/hbad を要求しない。
- 同じ C の構成には従来の hclass と全適格段での hbad を保持する。
  hfree/hrank/hker/hsurj/hlift/hsat/hequiv を新しい provider にしない。
- 有限群 ZMod 25 の5進 Tate 点列は零だが非零5捩れがあるため、
  第0評価の全射性は自動ではないことを回帰例で確認した。
  同じ Frey 残余点の持ち上げ、L での商同型の往復、p² 飽和性、同じ還元点も検証した。
- 新規3 production を Lib/FLT/root、2 test を通常の DkMathTest 入口へ公開した。
  教科書 `TEXTBOOK-N032-FREY-TATE-REDUCTION-261106.md` の3ブロックは全文一致し、
  import 直後の正確な `#print "file: …"` を保持する。
- 主要15宣言の公理・再帰依存監査、12件の公開入力監査を追加した。
  詳細は `evidence/validation-note032-frey-tate-reduction.txt`。

**今回の3ステップは、評価の完全性・実際の全 Tate 商 mod p・同じ直線の還元として完成。**
次元2の定理は mod p 商に対するものであり、全 Tate 加群の自由階数2や基底拡張ではない。
完備性・Nakayama から自由性を導く議論、全加群の基底・高位 Weil pairing・Frobenius 特性多項式は未完成。
hclass・全段 hbad・最終矛盾の作用算術も未完成であり、**一般 hno は引き続き未完成。**


## 2026-11-06: 3ステップ — 互換有限基底から同じ全 Frey Tate 基底と作用行列へ

1. `PrimePowerTatePairSpan` を実装した。
   二つの同じ互換点列の第0成分が p 捩れを生成すれば、各有限 p 冪捩れ段も生成すると証明した。
   次段の p^n 倍を第0段で展開し、その差を一つ低い段へ戻す実際の帰納法である。
   有限生成性・自由性・階数・素数性をこの群論の入力にしない。
2. `EllipticTatePairBasis` を実装した。
   同じ各有限段の標準二成分線形写像を、前段の生成性で全射にした。
   実際の楕円捩れ濃度 N² と定義域の濃度の一致から有限段の線形同型を得た。
   任意の全点列を同じ有限同型で読んだ両係数は、標準剰余で両立すると証明した。
   その実際の Cauchy 復元と剰余外延性から、(ℤₚ×ℤₚ)≃ₗ[ℤₚ]全Tate加群を構成した。
   汎用入口の第0段生成性 hbase は明示保持する。
3. `FreyTateBasis` を実装した。
   元の同じ非零生成元 v の第0点を、同じ E[p] の実際の次元2を使って二点基底へ拡張した。
   第二点は既存の実際の第0評価全射性で同じ全 Tate 点列 w へ持ち上げた。
   実際の残余基底から hbase を内部証明し、全 Tate 加群の実際の Fin 2 基底を構成した。
   第一・第二ベクトルは正確に元の同じ v と選んだ同じ w である。

- 以前の同じ Tate 直線は、新しい二成分座標の第二成分が0である点列全体と正確に一致する。
- 同じ全点群の実際の Galois 線形作用をこの基底で行列化し、第一列が同じ χ∞ と0になると証明した。
  三角性を新たな provider として仮定せず、以前の同じ scalar 作用公式を使う。
- この元の直線に適合する全 Frey 基底は、従来の hclass と全段 hbad を保持した構成である。
  汎用 hbase は保持し、最終 Frey 入口に hbase/hbasis/hrank/hfree/hbij/htriangle を追加しない。
- 任意の全 Tate 点列の二成分往復、元の v/w の座標、w が元の直線の外にあること、
  任意の p³ 捩れ点の同じ有限段座標往復、恒等元の作用行列=単位行列を回帰例で確認した。
- 新規3 production を Lib/FLT/root、2 test を通常の DkMathTest 入口へ公開した。
  教科書 `TEXTBOOK-N032-FREY-TATE-BASIS-261106.md` の3ブロックは全文一致し、
  import 直後の正確な `#print "file: …"` を保持する。
- 主要15宣言の公理・再帰依存監査、12件の公開入力監査を追加した。
  詳細は `evidence/validation-note032-frey-tate-basis.txt`。

**今回の3ステップは、有限全段の同型・全 Tate 基底・元の同じ直線に適合する作用行列として完成。**
この条件下で全 Tate 加群の自由階数2を実際の Fin 2 基底として構成済み。
第二対角指標の算術、高位 Weil pairing・円分行列式、Frobenius 特性多項式は未完成。
位相的な基底同型・点列作用の連続性は今回追加していない。
hclass・全段 hbad・最終矛盾の作用算術も未完成であり、**一般 hno は引き続き未完成。**


## 2026-11-06: 3ステップ — 第二連続 Tate 指標・非対角の積公式・mod p 自明性

1. `TriangularTwoCharacter` を実装した。
   実際の群から上三角2×2行列への準同型から、両対角成分の乗法性を証明した。
   群の逆元を写して両成分を単元値指標へ持ち上げた。
   上右成分の積公式 b(στ)=a(σ)b(τ)+b(σ)d(τ) と行列式 a(σ)d(σ) を証明した。
   p 進指標の全有限剰余の開核から、同じ指標の連続性を導く API も追加した。
2. `FreyTateCharacters` を実装した。
   元の同じ基底での実際の行列表示を行列準同型として公開し、以前の同じ行列値との一致を保った。
   第一対角指標は以前の同じ χ∞、第二対角指標 d は実際の M₁₁ である。
   同じ第二基底点列への作用を有限座標で比較し、各有限剰余の核が同じ全捩れ開核を含むと証明した。
   これにより d は連続。新たな可逆性・連続性・開核 provider は要求しない。
3. `FreyTateCharactersModP` を実装した。
   元の同じ残余 Cofixed 条件から、σ(w)−w の第0成分が同じ L に入ることを使う。
   同じ直線の還元全射性で c を持ち上げ、その差を実際の p 倍シフト逆像へ戻した。
   同じ座標の第二成分から d(σ)−1=p•z₂ を得て、第二指標の mod p 自明性を証明した。
   同じ χ∞ の mod p 円分一致と行列式の積公式から、実際の行列式 mod p の円分一致も得た。

- Cofixed 条件は元の残余条件のまま使う。作用差そのものが同じ無限直線へ入るとは結論しない。
  証明したのは作用差が直線と p 倍像の和へ入ることと、第二指標が mod p で1であること。
  第二 p 進指標全体の自明性・高位商作用の自明性・Galois 分裂は未証明。
- 同じ hclass と全適格段 hbad を保持する。
  hunit/hsecond/hcont/hcocycle/hsplit/htrivial/hmodp/hdet を新しい provider にしない。
- 実際の (ZMod 25)ˣ の上三角作用 [[u,1−u],[0,1]] を回帰例にした。
  二指標と非零の上右成分、mod 5 と mod 25 の1の区別を検査した。
  同じ Frey 第二指標の逆元公式、非対角の逆元との積公式、同じ mod p 剰余も確認した。
- 新規3 production を Lib/FLT/root、2 test を通常の DkMathTest 入口へ公開した。
  教科書 `TEXTBOOK-N032-FREY-TATE-CHARACTERS-261106.md` の3ブロックは全文一致し、
  import 直後の正確な `#print "file: …"` を保持する。
- 主要15宣言の公理・再帰依存監査、12件の公開入力監査を追加した。
  詳細は `evidence/validation-note032-frey-tate-characters.txt`。

**今回の3ステップは、第二連続単元値指標・実際の積公式・元の Cofixed 条件からの mod p 自明性として完成。**
行列式の積表示と mod p 円分一致は証明済みだが、高位 Weil pairing や全 p 進円分行列式との一致ではない。
第二指標の高位算術、Frobenius 特性多項式、最終矛盾の算術は未完成。
点列群の位相的基底同型、上右成分や全行列作用の連続性も今回追加していない。
hclass・全段 hbad も未完成であり、**一般 hno は引き続き未完成。**


## 2026-11-07: 3ステップ — 可換環上の忠実性・全非零捩れ行列式・全 p 進円分一致

1. `AlternatingDeterminantRing` を実装した。
   可換環上の二次元交代対を基底座標で展開し、非退化性から基底対への係数作用の単射性を証明した。
   非零元だけによる消去を使わず、同じ線形作用の行列式を対の同変係数と同定する。
2. `EllipticWeilDeterminantAll` を実装した。
   非零 n の全 n 乗根への実際の作用から有限円分指標を定義した。
   同じ E[n] の実際の階数2基底に対して、既存の幾何学的 Weil 対の交代性・非退化性・同変性を使い、
   実際の捩れ表現の行列式がこの有限円分指標に一致すると証明した。
   有限基底は明示入力だが、Weil 対の新しい provider は要求しない。
3. `FreyTateCyclotomicDeterminant` を実装した。
   同じ二点列の有限基底を実際に構成し、全座標・全基底ベクトル・Galois 行列各成分の還元一致を証明した。
   各正冪剰余の有限行列式公式と Mathlib 円分指標の同じ剰余を比較し、p 進外延性で全行列式一致を得た。
   以前の同じ三角行列式 χ∞・d と比較し、単元として d=cyclo∞・χ∞⁻¹ を証明した。

- SAME Source/L/rootField/tower/二点列/有限・全基底/実際の Galois 作用を保持する。
- hclass と全適格巡回段の hbad は以前の構成入力として保持する。
  hdet/hweil/hprim/hcyclo/hratio を新たな最終 provider にしない。
- 原始根を選ぶ代わりに非退化性による係数の忠実性を使う。
  原始 p 冪乗根の厳密位数を与える別定理を実装したとは扱わない。
- ZMod 25 の非零消去の失敗を回帰例とし、同じ法25の実際の幾何学的行列式公式を検査する。
- 新規3 production を Lib/FLT/root、2 test を通常入口へ公開した。
  教科書 `TEXTBOOK-N032-FREY-TATE-DETERMINANT-261107.md` は３ファイル全文を収録し、
  各 import 直後の正確な `#print "file: …"` を保持する。
- 主要15宣言の公理・再帰依存監査と12件の公開入力監査を追加した。
  実行結果は `evidence/validation-note032-frey-tate-determinant.txt` に記録する。

**全 p 進円分行列式と第２指標の比の同定は上記の同じ算術入力のもとで実装済み。**
第二指標全体の自明性・第１指標の円分一致・Galois 分裂・Frobenius 特性多項式は結論していない。
hclass・全段 hbad の算術的供給と最終矛盾は未完成であり、**一般 hno は引き続き未完成。**


## 2026-11-07: 3ステップ — 全精度 Frobenius 円分値・特性多項式・有限捩れ二次関係

1. `CyclotomicFrobeniusAll` を実装した。
   任意の非零付値単元次数 n について、同じ Frobenius 元の有限円分値を q と同定した。
   q≠p の同じ素点では p の全冪が付値単元であることを証明し、
   Mathlib の p 進円分指標の値が整数 q そのものとなることを全正冪剰余で証明した。
   円分計算には楕円曲線の良還元は不要。
2. `TriangularTwoCharacteristic` を実装した。
   実際の二指標による trace の和と特性多項式の因数分解を証明した。
   上右成分を消さず、二次関係を全行列について証明した。
   さらに任意の二次行列の関係を基底同型で同じ線形作用自体へ戻す API を追加した。
3. `FreyTateFrobenius` を実装した。
   同じ有限基底の trace と全 trace の剰余を比較した。
   同じ実際の Frobenius 元に対して det=q、trace=χ∞+qχ∞⁻¹ と同定し、
   実際の特性多項式 X²-(χ∞+qχ∞⁻¹)X+q を証明した。
   同じ全 Tate 点列および各有限 E[p^(n+1)] の実際の作用に対する二次関係を証明した。

- SAME Source/L/rootField/tower/二点列/有限・全基底/実際の Galois 作用を保持する。
  さらに同じ A と同じ Frobenius 元 σ を使い、q の選択を取り替えない。
- hclass と全適格巡回段の hbad は保持する。最終入口に htrace/hdet/hCH/hpointcount を追加しない。
  汎用 linear_quadratic の htrace/hdet は実際の Frey 計算で内部供給する。
- 特性多項式が一次式の積に分かれても、Galois 表現が分裂するとは主張しない。
  法25の非零上右成分を持つ単位行列と冪零行列の和で、重根多項式と非スカラー性を回帰確認する。
- 新規3 production を Lib/FLT/root、2 test を通常入口へ公開した。
  教科書 `TEXTBOOK-N032-FREY-TATE-FROBENIUS-261107.md` は３ファイル全文を収録し、
  import 直後の正確な `#print "file: …"` を保持する。
- 主要15宣言の公理・再帰依存監査と12件の公開入力監査を追加した。
  詳細は `evidence/validation-note032-frey-tate-frobenius.txt`。

**今回の二次関係の trace 係数は実際の χ∞+qχ∞⁻¹ であり、有限体点数との一致は未証明。**
q+1-#E(Fq) を係数とする算術的 Frobenius 関係を閉じたとは扱わない。
商上の高位固定性、第２指標全体の自明性、hclass・全段 hbad の算術的供給、最終矛盾も未完成。
**一般 hno は引き続き未完成。**


## 2026-11-07: 4ステップ — 有限商・高位吸収の同値・良還元非自明性・共鳴慣性証人

1. `FreyTateFiniteQuotient` を実装した。
   同じ有限基底の第二座標を全射線形写像とし、その核を元の同じ巡回段の点の所属で同定した。
   第一基底ベクトルは以前の同じ生成元である。実際の核による商と標準有限環の線形同型を構成した。
2. `FreyTateInertiaQuotient` を実装した。
   同じ有限商の作用は同じ第二指標の標準剰余であると証明した。
   全 p^(n+1) 捩れ上の作用差吸収と、第二指標の同じ剰余=1 を同値にした。
   同じ慣性群全体についても同値を公開した。狭い p•y∈K を高位捩れ条件へ拡張しない。
3. `FreyTateGoodReductionCharacter` を実装した。
   同じ良還元 Frobenius で第二指標の剰余=1 なら p^(n+1)≤#E(Fq) と証明した。
   既存の実際の固定捩れ点の良還元単射と、同じ巡回段の濃度を使う。
   次数が点数を越える段ではその剰余は非自明。N=#E(Fq)>0、n=N−1 を使い d(σ)≠1 を得た。
4. `FreyTateResonantWitness` を実装した。
   同じ点数高さの段を既存の条件付き点数矛盾へ渡し、高位吸収の失敗を取り出した。
   q≥5、q≠p、q|abc、q≡±1 mod p、実際の A、その慣性元 τ、p^N 捩れ点 y を与える。
   τy−y∉K_(N−1)、p•y∉K_(N−1)、同じ d(τ) mod p^N≠1 を同時に証明した。
   良還元素数の存在も内部供給し、共鳴慣性上の d(τ)≠1 を公開した。

- SAME Source/L/rootField/tower/生成元/有限基底/Galois 作用を保持する。
- hclass と全適格段についての狭い ResonantAbsorptionAt は従来どおり明示入力。
  新しい高位吸収や指標自明性、局所証人、点数／トレース公式を provider にしない。
  第三ステップの bound 定理では検査対象の有限指標=1 を仮定し、その上界を導く。
- 高位吸収の失敗点は p•y∉K。従来 hbad 自体の反例ではない。
  同じ条件付き塔から第二指標の非自明性を示したのであり、一般 hno の矛盾を得たわけではない。
- 法25の diag(1,6) を回帰例とし、5•y が第一軸へ入る場合の狭い吸収と、
  y=(0,1) での高位吸収の失敗、mod5 と mod25 の指標自明性の違いを確認する。
- 新規4 production と2 test を FLT/root および通常 test 入口へ公開した。
  教科書 `TEXTBOOK-N032-FREY-TATE-QUOTIENT-261107.md` の４ブロックは各本番ファイル全文。
  import 直後の正確な `#print "file: …"` を保持する。
- 主要14宣言の公理・再帰依存監査と12件の公開入力監査を追加した。
  実行結果は `evidence/validation-note032-frey-tate-quotient.txt`。

**追加の局所算術でこの共鳴慣性の非自明性を排除できるか、という具体的な境界まで進めた。**
hclass・全段の狭い hbad の算術的供給、トレースと点数の同定、最終矛盾は未完成。
**一般 hno は引き続き未完成。**


## 2026-11-07: 4ステップ — 実際の慣性ユニポテンス・第二指標自明性・条件付き hno 閉鎖

1. `EllipticNodalUnipotence` を実装した。
   同じ臨界中心・接方向・モデルに対して、慣性差が滑らかに還元する既存定理を使う。
   単元次数の滑らかな捩れ点は別の慣性元にも固定されるので、差分作用の積が零。
   とくに有限捩れ上で (ρ(τ)−1)²=0。中心の固定性や滑らかさを provider にしない。
2. `FreyTateInertiaUnipotent` を実装した。
   q≠p の同じ悪い住所で、実際の幾何と全 p 冪の付値単元性を内部供給した。
   全有限段の差分二次冪零性を、同じ全点列の各成分で比較し、全 Tate 作用へ戻した。
   この局所定理は hclass・狭い hbad・Cofixed・基底を入力しない。
3. `FreyTateInertiaCharacters` を実装した。
   同じ条件付き塔の全基底へ二次冪零性を移した。
   以前の同じ上三角行列の第二対角成分が (d−1)²=0 を満たすので、整域 ℤp 上で d=1。
   同じ有限商の同値を使い、同じ塔の全有限段で高位慣性吸収を内部供給した。
   有限 ZMod(p^n) で冪零元を消去していない。非対角成分の消滅も結論しない。
4. `FreyConditionalCofixedExclusion` を実装した。
   前回の同じ共鳴慣性証人の d(τ)≠1 に、ステップ3の d(τ)=1 を適用して矛盾を得た。
   hclass と全段の狭い hbad のもとで同じ直線の Cofixed 排除を閉じた。
   hclass と全直線・全段 hbadAll の明示入力で、既存の hno 形の結論を証明した。
   hclass と Cofixed から狭い吸収失敗段を得る定理は hbad 入力を要求しない。
   定義を展開し、q≥5、q≠p、q|abc、q≡±1 mod p、同じ A、τ、実際の点 y で
   p•y∈T.carrier かつ τy−y∉T.carrier となる具体的証人も出力した。

- ローカル模範解答の Frey 最終証明の局所吸収部分と２つの零成分公開定理を照合した。
  参照コミット・ファイル SHA-256 は `evidence/note032-frey-unipotence-reference-audit.json`。
  DkMath の既存幾何を直接接続し、外部 P2M/P2MW や大域分類を import していない。
- 局所差分定理は無条件の同じ幾何学の接続。条件付き基底・指標を使う段階では従来の算術入力を保持。
  最終 hno の hclass/hbadAll を新たに証明したものとは扱わない。
- 前回の高位失敗点は p•y∉K。今回、hclass と Cofixed のもとで得た狭い失敗点は p•y∈K。
  異なる仮定と結論を持つ定理であり、狭い吸収が全点で成立すると誤認しない。
- 法25の非零冪零元 (6−1)、ℤ5 上の上右成分が1のユニポテント行列を回帰検査する。
- 新規4 production と2 test を Lib/FLT/root と通常入口へ公開した。
  教科書 `TEXTBOOK-N032-FREY-TATE-UNIPOTENCE-261107.md` の４ブロックは各本番ファイル全文。
  import 直後の正確な `#print "file: …"` を保持する。
- 新規11宣言の公理・再帰依存・公開入力監査を追加した。
  実行結果は `evidence/validation-note032-frey-tate-unipotence.txt`。

**hclass と全対象直線・段の狭い吸収を保持した条件付き hno は今回閉じた。**
一般 hno に向けた残存算術は、それらの入力の必要範囲での供給／障害解析である。
トレースと有限体点数の同定や Galois 分裂は今回の証明に使わない。
**算術入力を除去した一般 hno は引き続き未完成。**


## 2026-11-07: 4ステップ — 滑らかな配置と狭い吸収・失敗点の深さ・候補限定 hno

1. `FreySmoothStageAbsorption` を実装した。
   同じ段の全体の部分群所属を、実際の座標生成元 T.coordinates(1) の所属で判定した。
   T が同じ滑らかな部分群に入るなら、同次数の滑らかな捩れ全体に一致すると証明した。
   幾何学的濃度上界と T の実際の濃度を用いる。配置自体は明示入力。
   p•y∈T の前提のまま、高い倍点の滑らかな残余固定性から慣性差の次数を下げ、狭い吸収を得た。
2. `FreyNarrowFailureGeometry` を実装した。
   同じ段と p•y∈T、τy−y∉T を保ち、y と差点の p^(n+2) 零化上界を証明した。
   差点は滑らか、同じ慣性群の全元に固定、非零、p倍は元の T に属する。
   元の段の座標生成元は非滑らか。実際の臨界中心 C と接方向、有限点座標 (x,z) を取り出し、
   v_A(x−C.x)<1 を証明した。次数上界を厳密位数と同一視しない。
3. `FreyCofixedArithmeticObstruction` を実装した。
   同じ対象を保持する命題 NarrowAbsorptionObstruction に局所幾何をまとめた。
   実際の hclass と同じ Cofixed 直線から、全段 hbad や配置を仮定せず証明書の存在を導いた。
   古典的存在証明であり、数値座標を計算するアルゴリズムではない。
4. `FreyCandidateCofixedExclusion` を実装した。
   吸収入力 hbadAll を Cofixed 候補だけの hbadCandidate へ弱めた。
   安定性を重複要求しない Cofixed 排除と、既存 hno 形への接続を公開した。
   候補段生成元の滑らかな配置 hplacement があれば、ステップ1で狭い吸収を内部証明できる。
   hplacement は未証明の算術入力として明示し、その構成や一般 hno の完成とは扱わない。

- 模範解答の htoric、非共鳴の scalar-dichotomy、p倍逆像吸収部分を照合した。
  参照コミットと SHA-256 は `evidence/note032-frey-obstruction-reference-audit.json`。
  模範の共鳴配置・m3c_escape・大域 Step Three は今回移植していない。
- 狭い対象 {y|p•y∈K_n} と高位対象 E[p^(n+1)] は一般には包含関係にない。
  同じ G=(ZMod125)^2、同じ K=〈(5,0)〉により、両方向の非包含を回帰検査した。
- SAME Source/L/段/座標生成元/実際の局所点/作用を保持する。
  差点が滑らかかつ慣性固定でも、元の別の部分群 T に入るとは結論しない。
- 新規4 production と2 test を FLT/root と通常入口へ公開した。
  教科書 `TEXTBOOK-N032-FREY-ARITHMETIC-OBSTRUCTION-261107.md` の４ブロックは本番ファイル全文。
  import 直後の正確な `#print "file: …"` を保持する。
- 11宣言の公理・再帰依存・公開入力監査を追加した。
  構造体の構成子と全フィールドの型も監査する。
  実行結果は `evidence/validation-note032-frey-arithmetic-obstruction.txt`。

**同じ失敗段の配置を、生成元の非滑らかな還元と中心での深さまで具体化した。**
その配置障害の排除、候補限定の狭い吸収／滑らかな配置、hclass の算術的供給は未完成。
**算術入力を除去した一般 hno は引き続き未完成。**


## 2026-11-07: 4ステップ — 交叉濃度・局所商像・厳密位数 p の慣性固定商元

1. `FiniteSubgroupIntersection` を実装した。
   元の K∩H と K→G/H の核を加法同型で同定し、実際の像を使う濃度積を証明した。
   |K|=p^m なら |K∩H|=p^r、|image(K→G/H)|=p^(m−r)、r≤m と正確に分解した。
2. `FreyStageLocalComponent` を実装した。
   同じ段 T と同じ滑らかな部分群 H の交叉・局所点群商における像を定義した。
   同じ段生成元が非滑らかなら交叉が全 T にはならないので、r≤n、商像濃度≥p。
   Néron 成分群との同定や判別式付値からの次数公式は含まない。
3. `FreyStageUpperQuotient` を実装した。
   元の T を E[p^(n+2)] 内の部分群として保持し、実際の有限商を構成した。
   元の安定性から同じ Galois 作用を商上の群準同型へ降ろした。
   x∉T、p•x∈T なら同じ商類は厳密位数 p。同じ点の固定性も商作用へ移送した。
   点 x 自体の厳密位数を p と主張しない。
4. `FreyIntersectionQuotientObstruction` を実装した。
   前回の同じ障害証明書の生成元非滑らかさから、交叉・局所商像の濃度分解を得た。
   差点 δ は H で滑らかなので G/H では零。一方 δ∉T、p•δ∈T から有限商では位数 p。
   全慣性元による同じ差点の固定性から、同じ商元は全慣性に固定される。
   hclass と同じ Cofixed 候補から、元の全データ・濃度分解・商元を一緒に出力した。

- ローカル模範解答の htoric/hKdown と同次数の滑らかな捩れの所属経路を照合した。
  参照コミットと SHA-256 は `evidence/note032-frey-component-reference-audit.json`。
  公開零成分所属定理に残る Step Three 条件も確認したが、その供給や proof port は今回行わない。
- 新たな配置・吸収・商元・濃度分解を算術 provider にしない。
  局所群論は hclass/Cofixed から独立し、最終障害存在定理だけが従来の hclass/Cofixed を保持する。
- 同じ差点の像が異なる二つの商で零／非零であることは矛盾ではない。
  元の段 T と滑らかな H の配置障害を、Galois 加群として記述したものである。
- G=(ZMod25)^2、K=第一軸、H=第一座標の法5剰余が零の部分群を回帰例にした。
  同じ δ=(0,5) の G/H での零と G/K での厳密位数5、K濃度25・交叉5・商像5を検査した。
- 新規4 production と2 test を Lib/FLT/root と通常入口へ公開した。
  教科書 `TEXTBOOK-N032-FREY-INTERSECTION-QUOTIENT-261107.md` は４ファイル全文を収録し、
  import 直後の正確な `#print "file: …"` を保持する。
- 17宣言の公理・再帰依存監査と13件の公開入力監査を追加した。
  実行結果は `evidence/validation-note032-frey-intersection-quotient.txt`。

**厳密位数 p の慣性固定商元と、同じ段の交叉・局所商像の濃度分解は今回実装済み。**
この配置を排除する Frey 固有の成分群・判別式の算術、hclass の供給は未完成。
**無条件の一般 hno は引き続き未完成。**


## 2026-11-07: 4ステップ — 交叉生成元・厳密位数・慣性差分準同型

1. `CyclicIntersectionGenerator` を実装した。
   元の ZMod 座標の1が同じ K を生成することと、局所商像生成元の位数=商像濃度を証明した。
   |K|=p^m、|K∩H|=p^r なら商生成元の位数は p^(m−r)。
   実際の倍点 p^(m−r)•g の位数と濃度を計算し、元の交叉=その倍点の zmultiples と証明した。
2. `UnipotentDifferenceCharacter` を実装した。
   表現の差分積零性から、同じ基点の作用差分が全作用元に固定されることを証明した。
   c_x(στ)=c_x(σ)+c_x(τ) と、元の加法群を Multiplicative で包んだ通常の群準同型を構成した。
   任意の表現の共役輸送恒等式も証明した。そこでは基点を ρ(φ)x へ動かす。
   Frobenius の q倍公式・野生作用の消滅は結論しない。
3. `FreyStageIntersectionGenerator` を実装した。
   元の同じ段座標と滑らかな部分群を使い、交叉の実際の生成元と商生成元の厳密位数を公開した。
   k•g の滑らかさは商像濃度が k を割ることと同値。
   非滑らかな場合、p^k•g が滑らかになる最小指数は n+1−r として記述できる。
4. `FreyInertiaDifferenceCharacter` を実装した。
   同じ悪い住所 q≠p の慣性群の任意の二元に対し、実際の有限捩れ差分の積零性を内部証明した。
   同じ有限点を基点とする慣性差分準同型と、同じ段による有限商への合成を構成した。
   全ての値は同じ商作用の全慣性元に固定される。
   前回の証明書の y を基点に取ると、証人 τ での値は同じ δ の非零・厳密位数 p の商類。
   同じ hclass と Cofixed 候補から、その通常の非自明な準同型の存在を出力した。

- 模範解答の htoric と公開の Frobenius 共役冪の野生誤差定理を照合した。
  参照コミットと SHA-256 は `evidence/note032-frey-generator-reference-audit.json`。
  体の作用比が1に合同という結論を、捩れ表現上の誤差の自明性へ勝手に拡張しない。
- 新しい配置・吸収・準同型・厳密位数を provider にしない。
  汎用差分定理の hprod は実際の Frey 適用で局所幾何から内部供給する。
  元の hclass/Cofixed は最終存在定理に保持する。
- Multiplicative は元の加法群への型タグであり、以前の単元値 Tate 指標 χ∞・d とは別の対象。
  商群全体の慣性自明性、連続性、外部分解群での固定基点の共役不変性は結論しない。
- ZMod25 の生成元1、交叉〈5〉、商生成元の厳密位数5を回帰検査した。
  (ZMod25)^2 の実際の剪断表現で差分値(t,0)、t=5での非零・厳密位数5を確認した。
- 新規4 production と2 test を Lib/FLT/root と通常入口へ公開した。
  教科書 `TEXTBOOK-N032-FREY-GENERATOR-CHARACTER-261107.md` は４ファイル全文を収録し、
  import 直後の正確な `#print "file: …"` を保持する。
- 新規20宣言の公理・再帰依存監査と16件の公開入力監査を追加した。
  実行結果は `evidence/validation-note032-frey-generator-character.txt`。

**同じ交叉生成元・最小滑らか指数と、通常の非自明な慣性商値準同型は実装済み。**
非自明な慣性準同型の存在自体は矛盾ではない。Frey 固有の追加の局所・大域算術と hclass の供給が残る。
**無条件の一般 hno は引き続き未完成。**


## 2026-11-07: 4ステップ — 有限慣性差分の像・連続性・開核

1. `FinitePrimePowerCharacter` を実装した。
   群準同型の核商と実際の像の濃度を第一同型定理で同定した。
   値域濃度 p^m から、像濃度・核商濃度・核指数が同じ p^s、s≤m と証明した。
   実際の非自明な値があれば s≥1。始域の有限性は要求しない。
2. `FreyStageUpperQuotientCard` を実装した。
   元の T を E[p^(n+2)] に持ち上げた段との、点を保つ加法同型を構成した。
   持ち上げ段濃度 p^(n+1) と、実際の楕円捩れ濃度から商濃度 p^(n+3) を証明した。
3. `FreyStageUpperQuotientTopology` を実装した。
   同じ標準商位相の離散性、実際の Galois 商作用の軌道と両変数の連続性を証明した。
   同じ慣性部分群位相で、実際の torsion 差分と商値差分準同型の連続性を証明した。
   その同じ核は慣性群の中で開かつ閉。連続性・開核を追加 provider にしない。
   c_x(σ)=σ[x]−[x] の同じ商作用に関する恒等式を公開した。非零 H¹ 類ではない。
4. `FreyInertiaCharacterFiniteImage` を実装した。
   同じ商の実際の慣性固定部分群と、同じ差分準同型の値域制限を構成した。
   同じ準同型の像・核商・核指数は p^s、s≤n+3。
   同じ障害証明書の非自明な位数p値から s≥1 を導いた。
   同じ正確な hclass と Cofixed 候補から、非自明値・厳密位数p・開閉核・正の p 冪指数を出力した。

- 模範解答の公開開核定理・実装・大域 hno 経路の hopen 使用箇所を照合した。
  HEAD と3ファイルの SHA-256 は `evidence/note032-frey-finite-character-reference-audit.json`。
- 新規4 production と2 test を Lib/FLT/root と通常入口へ公開した。
  教科書 `TEXTBOOK-N032-FREY-FINITE-CHARACTER-261107.md` は4 production 全文を収録し、
  import 直後の正確な `#print "file: …"` を保持する。
- 19宣言の公理・再帰依存監査と16件の公開入力監査を追加した。
  ZMod25 の5倍写像で像・核商・核指数5、指数1を検査した。自明な準同型の指数0も検査した。
  実行結果は `evidence/validation-note032-frey-finite-character.txt`。

**同じ非自明な慣性差分は、正の p 冪指数の開核を持つ有限像連続準同型として実装済み。**
開性は慣性群の中での相対位相についての主張。商全体の慣性自明性は結論しない。
野生慣性の消滅、tame/Frobenius の固定基点 q 倍則、障害排除、hclass の算術的供給は残る。
**無条件の一般 hno は引き続き未完成。**
