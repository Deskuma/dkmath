# NOTE-032: 一般 `hno` の証明経路監査

更新日: 2026-11-01。`__REVIEW.md` を参考に実ソースを照合し、局所入力を形式化した。

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
