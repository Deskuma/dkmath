# NOTE-032: 一般 `hno` の証明経路監査

更新日: 2026-11-05。`__REVIEW.md` を参考に実ソースを照合し、局所入力を形式化した。

## 現在の証明境界

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
