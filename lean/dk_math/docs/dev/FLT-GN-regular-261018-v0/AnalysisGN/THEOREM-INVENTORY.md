# 現行Leanの定理棚卸し

2026-10-23。添付監査の36宣言（A01–A36）と追加調査22宣言（B01–B22）。
初回棚卸しは合計58宣言・42所有モジュール。添付36宣言のソース行は当時のcheckoutと一致し、うち16宣言は既にLib配下にあった。
この初回58宣言は所有モジュールのビルド後に`#check`と`Lean.collectAxioms`で確認し、依存公理は標準の3つ以内だった。
この検査は既存宣言に対するもの。新しい一般化、ZIP facadeの配置、全面的な依存層監査は別工程である。

初回棚卸しの全修飾名・ソース宣言・暗黙引数・SHA256は[source-inventory.json](evidence/source-inventory.json)に保存した。
B01–B05はGN-LIB-001で移管済みであり、下表は新しい所有先を示す。
A17もGN-LIB-003aで移管済みであり、その表の所有先・行を更新した。
計17宣言の移管対応と型・証明本体の保存は [gn-lib-001.json](evidence/gn-lib-001.json) に記録した。
Lib配下でもnamespaceが歴史的名称のままの場合がある。namespaceだけで所有層を判定しない。

## 1. 添付36宣言の現行確認

| ID  | 宣言と所有ファイル                                                                                                                                                                                | 必須条件・限界                                             | 配置判断                     |
| --- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------- | ---------------------------- |
| A01 | [`add_pow_eq_mul_GTail_one_add_gap`](../../../../DkMath/Lib/Cosmic/GTail.lean#L132)<br>`DkMath/Lib/Cosmic/GTail.lean`                                                                             | CommSemiring、全次数、除算なし。                           | Lib既存・再作成不要          |
| A02 | [`GTail_rec`](../../../../DkMath/Lib/Cosmic/GTail.lean#L165)<br>`DkMath/Lib/Cosmic/GTail.lean`                                                                                                    | 切断index r<d。次数降下ではない。                          | Lib既存・再作成不要          |
| A03 | [`powerCore_split`](../../../../DkMath/Lib/Cosmic/CoreNested.lean#L44)<br>`DkMath/Lib/Cosmic/CoreNested.lean`                                                                                     | CommRing。冪差の加法分割。                                 | Lib既存・再作成不要          |
| A04 | [`powerCore_eq_gtail_one`](../../../../DkMath/Lib/Cosmic/CoreNested.lean#L62)<br>`DkMath/Lib/Cosmic/CoreNested.lean`                                                                              | CommRing。step*GTailとの一致。                             | Lib既存・再作成不要          |
| A05 | [`selected_balance_eq_pow_add_powerCore`](../../../../DkMath/Lib/Cosmic/CoreNestedTransport.lean#L27)<br>`DkMath/Lib/Cosmic/CoreNestedTransport.lean`                                             | CommRing。同じbase/stepの選択量。                          | Lib既存・再作成不要          |
| A06 | [`selectedGap_add_selectedBody`](../../../../DkMath/Lib/Cosmic/GTailSelection.lean#L38)<br>`DkMath/Lib/Cosmic/GTailSelection.lean`                                                                | CommSemiring、任意の有限選択。                             | Lib既存・再作成不要          |
| A07 | [`selected_balance_transport`](../../../../DkMath/Lib/Cosmic/GTailTransport.lean#L81)<br>`DkMath/Lib/Cosmic/GTailTransport.lean`                                                                  | 同じd,x,uで全量のみ保存。                                  | Lib既存・再作成不要          |
| A08 | [`coeffGCD_prime_interior`](../../../../DkMath/Lib/Cosmic/GTailFactor.lean#L178)<br>`DkMath/Lib/Cosmic/GTailFactor.lean`                                                                          | p素数、内部全index。係数のgcd。                            | Lib既存・再作成不要          |
| A09 | [`prime_mul_coords_dvd_selectedBody_interior`](../../../../DkMath/Lib/Cosmic/GTailFactor.lean#L189)<br>`DkMath/Lib/Cosmic/GTailFactor.lean`                                                       | p素数。評価Bodyの可除性、完全なgcdではない。               | Lib既存・再作成不要          |
| A10 | [`gcd_GN_eq_gcd_of_one_le`](../../../../DkMath/Lib/Cosmic/GTailBoundary.lean#L61)<br>`DkMath/Lib/Cosmic/GTailBoundary.lean`                                                                       | 1≤d、Coprime g u。素数次数不要。                           | Lib既存・再作成不要          |
| A11 | [`prime_dvd_GN_iff_dvd_gap`](../../../../DkMath/Lib/Cosmic/GTailCongruence.lean#L181)<br>`DkMath/Lib/Cosmic/GTailCongruence.lean`                                                                 | p素数、原始性不要、p=2含む。                               | Lib既存・再作成不要          |
| A12 | [`padicValNat_GN_prime_eq_one_of_dvd_gap`](../../../../DkMath/Lib/Cosmic/GTailPadic.lean#L191)<br>`DkMath/Lib/Cosmic/GTailPadic.lean`                                                             | p素数、3≤p、原始性、p∣g。                                  | Lib既存・再作成不要          |
| A13 | [`GN_mul_degree`](../../../../DkMath/Lib/Cosmic/GNProductDegree.lean#L53)<br>`DkMath/Lib/Cosmic/GNProductDegree.lean`                                                                             | CommSemiring、g=0・零因子を含む。                          | Lib既存・再作成不要          |
| A14 | [`GTail_one_eq_cyclotomicHomEval_of_prime`](../../../../DkMath/Lib/Cosmic/GTailCyclotomic.lean#L233)<br>`DkMath/Lib/Cosmic/GTailCyclotomic.lean`                                                  | 既存署名はField、g≠0。B22の一般橋も参照。                  | Lib既存・再作成不要          |
| A15 | [`add_pow_seven_sub_endpoints`](../../../../DkMath/Lib/Cosmic/GTailSeven.lean#L107)<br>`DkMath/Lib/Cosmic/GTailSeven.lean`                                                                        | CommRing、次数7。                                          | Lib既存・7次の回帰として保持 |
| A16 | [`coprime_sum_seven_quadratic`](../../../../DkMath/Lib/Cosmic/GTailSevenArithmetic.lean#L39)<br>`DkMath/Lib/Cosmic/GTailSevenArithmetic.lean`                                                     | Nat.Coprime a b、7次の二次形式。                           | Lib既存・7次の回帰として保持 |
| A17 | [`add_pow_gt_sum_pows_nat_of_two_le`](../../../../DkMath/Lib/Algebra/BinomTail.lean#L227)<br>`DkMath/Lib/Algebra/BinomTail.lean`                                                                          | Nat、2≤n、a,b>0。                                          | GN-LIB-003aでLib所有化済み・旧名互換 |
| A18 | [`add_pow_gap_factor`](../../../../DkMath/CosmicFormula/CosmicFormulaBinom.lean#L383)<br>`DkMath/CosmicFormula/CosmicFormulaBinom.lean`                                                           | CommSemiring。A01のlegacy語彙への転送。                    | 薄いadapter                  |
| A19 | [`body_not_perfect_pow_of_squarefree_GN`](../../../../DkMath/CosmicFormula/CosmicFormulaBinom.lean#L497)<br>`DkMath/CosmicFormula/CosmicFormulaBinom.lean`                                        | 1<d、1<GN、Coprime x GN、Squarefree GN。                   | 昇格候補                     |
| A20 | [`square_add_squareGnomonBand`](../../../../DkMath/Gnomon/Algebra.lean#L114)<br>`DkMath/Gnomon/Algebra.lean`                                                                                      | Nat、平方帯の定義を保持。                                  | 003bのLib一般核へのNat wrapper |
| A21 | [`squareGnomonBand_eq_sum_shifted_oddGnomon`](../../../../DkMath/Gnomon/Algebra.lean#L145)<br>`DkMath/Gnomon/Algebra.lean`                                                                        | Nat、平方帯の有限和分割。                                  | 003bのLib一般核へのNat wrapper |
| A22 | [`squareGnomonBand_eq_mul_GTail_two_one`](../../../../DkMath/Gnomon/CosmicBridge.lean#L43)<br>`DkMath/Gnomon/CosmicBridge.lean`                                                                   | Nat、平方帯とGTailのbridge。                               | Bridge保持                   |
| A23 | [`squareBody_add_one_eq`](../../../../DkMath/NumberTheory/Primitive/SquareBody.lean#L49)<br>`DkMath/NumberTheory/Primitive/SquareBody.lean`                                                       | Nat、P=0含む。squareBodyは上位定義。                       | 003bのLib一般核へのNat wrapper |
| A24 | [`prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody`](../../../../DkMath/NumberTheory/Primitive/SquareBody.lean#L98)<br>`DkMath/NumberTheory/Primitive/SquareBody.lean`                  | 1<m≤squareBody P、全旧素数支持との非交差。候補の存在は別。 | Primitive保持                |
| A25 | [`squarePrimeExpansion_eq_primeScalesUpTo_squareBody`](../../../../DkMath/NumberTheory/Primitive/SquarePrimeExpansion.lean#L86)<br>`DkMath/NumberTheory/Primitive/SquarePrimeExpansion.lean`      | 有限prime worldの定義を持つ等式。                          | Primitive保持                |
| A26 | [`squareBody_thirty_add_one_eq_thirtyOne_sq`](../../../../DkMath/NumberTheory/PrimorialUniverse/ThirtySquareWorld.lean#L67)<br>`DkMath/NumberTheory/PrimorialUniverse/ThirtySquareWorld.lean`     | P=30の数値特例。                                           | 特例保持                     |
| A27 | [`primeWorldResidues_eq_packetBase`](../../../../DkMath/NumberTheory/Legendre/PrimeWorldPacketBridge.lean#L23)<br>`DkMath/NumberTheory/Legendre/PrimeWorldPacketBridge.lean`                      | 1<primeWorldModulus Sが必要。                              | Bridge既存                   |
| A28 | [`supportDisjointFrom_iff_coprime_primeWorldModulus`](../../../../DkMath/NumberTheory/Primitive/PeriodicPrimeWorld.lean#L163)<br>`DkMath/NumberTheory/Primitive/PeriodicPrimeWorld.lean`          | KnownPrimeScales S。有限支持の意味を保持。                 | Primitive保持                |
| A29 | [`card_survivingChildIndices`](../../../../DkMath/NumberTheory/Primitive/PrimeWorldRefinement.lean#L357)<br>`DkMath/NumberTheory/Primitive/PrimeWorldRefinement.lean`                             | KnownPrimeScales S、q素数、q∉S、r<modulus。                | Primitive保持                |
| A30 | [`squareOffset_prime_iff_projection_survivor`](../../../../DkMath/NumberTheory/Legendre/PrimorialWheelBridge.lean#L109)<br>`DkMath/NumberTheory/Legendre/PrimorialWheelBridge.lean`               | 2≤n、SquareOffset n r。範囲付きの同値。                    | Legendre保持                 |
| A31 | [`legendreConjecture_iff_open_oddGnomon_prime`](../../../../DkMath/NumberTheory/Legendre/GnomonBridge.lean#L89)<br>`DkMath/NumberTheory/Legendre/GnomonBridge.lean`                               | LegendreConjectureとの同値。予想そのものの証明ではない。   | Legendre保持                 |
| A32 | [`gnomonPascalCell_factorization_carries`](../../../../DkMath/NumberTheory/Legendre/GnomonPascalCell.lean#L71)<br>`DkMath/NumberTheory/Legendre/GnomonPascalCell.lean`                            | p素数とNat.logによる有限上限b。                            | 抽出候補                     |
| A33 | [`coprime_squarePacketPoints_of_coprime_offset`](../../../../DkMath/NumberTheory/Legendre/PacketCoprimality.lean#L37)<br>`DkMath/NumberTheory/Legendre/PacketCoprimality.lean`                    | Coprime n r、平方殻の対向二点。                            | Bridge保持                   |
| A34 | [`padicValNat_choose_prime_pow`](../../../../DkMath/NumberTheory/BinomialPrimePower.lean#L214)<br>`DkMath/NumberTheory/BinomialPrimePower.lean`                                                   | p素数、0<k≤p^n。n=0も現行署名に含む。                      | 003cのLib一般核へのwrapper                     |
| A35 | [`unitCoordinate_refine`](../../../../DkMath/NumberTheory/PrimorialUniverse/UnitCoordinateRefinement.lean#L77)<br>`DkMath/NumberTheory/PrimorialUniverse/UnitCoordinateRefinement.lean`           | PositiveUnit、UnitRefinesBy。座標の存在は入力。            | 昇格候補                     |
| A36 | [`finitePrimeBasis_subset_primeScalesUpTo_product`](../../../../DkMath/NumberTheory/PrimorialUniverse/SquareBodyBridge.lean#L63)<br>`DkMath/NumberTheory/PrimorialUniverse/SquareBodyBridge.lean` | IsFinitePrimeBasis S。有限基底から積アンカーへ。           | Primitive保持                |

## 2. 追加で見つかった再利用対象

| ID  | 宣言と所有ファイル                                                                                                                                                                            | 必須条件・限界                                 | 配置判断                                       |
| --- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------- | ---------------------------------------------- |
| B01 | [`GN_succ_right`](../../../../DkMath/Lib/Cosmic/GNSuccessor.lean#L46)<br>`DkMath/Lib/Cosmic/GNSuccessor.lean`                                                         | CommSemiring、d=0・零座標を含む。              | GN-LIB-001でLib所有化済み・旧名互換 |
| B02 | [`GN_succ_left`](../../../../DkMath/Lib/Cosmic/GNSuccessor.lean#L60)<br>`DkMath/Lib/Cosmic/GNSuccessor.lean`                                                          | CommSemiring、同じ二つの底の再帰。             | GN-LIB-001でLib所有化済み・旧名互換 |
| B03 | [`nat_coprime_adjacent_GN`](../../../../DkMath/Lib/Cosmic/GNSupport.lean#L122)<br>`DkMath/Lib/Cosmic/GNSupport.lean`                                                   | Nat.Coprime x u、d=0含む。                     | GN-LIB-001でLib所有化済み・旧名互換 |
| B04 | [`isCoprime_adjacent_GN`](../../../../DkMath/Lib/Cosmic/GNSupport.lean#L235)<br>`DkMath/Lib/Cosmic/GNSupport.lean`                                                    | CommRing、IsCoprime x u。                      | GN-LIB-001でLib所有化済み・旧名互換 |
| B05 | [`nat_exists_prime_dvd_GN_succ_not_dvd_GN`](../../../../DkMath/Lib/Cosmic/GNSupport.lean#L158)<br>`DkMath/Lib/Cosmic/GNSupport.lean`                                   | d>0、x,u>0、原始性。直前との非共有のみ。       | GN-LIB-001でLib所有化済み・旧名互換 |
| B06 | [`kernelPolynomial_eq_prod_cyclotomic`](../../../../DkMath/NumberTheory/GapFocusing/Degree.lean#L53)<br>`DkMath/NumberTheory/GapFocusing/Degree.lean`                                         | d>0、ℤ[X]、非自明な約数の層。                  | 一般核抽出候補・整数評価と区別                 |
| B07 | [`kernelPolynomial_irreducible_iff_prime`](../../../../DkMath/NumberTheory/GapFocusing/Degree.lean#L149)<br>`DkMath/NumberTheory/GapFocusing/Degree.lean`                                     | d≥2、ℤ[X]。整数評価の素数性とは別。            | 同じnamespaceを保持して抽出候補                |
| B08 | [`isRoot_cyclotomic_iff_prime_pow_mul_orderOf`](../../../../DkMath/Lib/NumberTheory/CyclotomicAddress.lean#L31)<br>`DkMath/Lib/NumberTheory/CyclotomicAddress.lean`           | 整域、CharP R q、q素数、n>0。                  | 006aでLib所有化・旧名互換 |
| B09 | [`int_dvd_pow_sub_pow_iff_primeOrder_dvd`](../../../../DkMath/Lib/NumberTheory/PrimeRatioOrder.lean#L70)<br>`DkMath/Lib/NumberTheory/PrimeRatioOrder.lean`                              | q素数、q∤b。冪差全体の可除性。                 | 006aでLib所有化・旧名互換 |
| B10 | [`primeOrder_dvd_prime_sub_one`](../../../../DkMath/Lib/NumberTheory/PrimeRatioOrder.lean#L99)<br>`DkMath/Lib/NumberTheory/PrimeRatioOrder.lean`                                        | q素数、q∤a,b。                                 | 006aでLib所有化・旧名互換 |
| B11 | [`dvd_cyclotomicShiftedEval_iff_prime_pow_mul_orderOf`](../../../../DkMath/NumberTheory/GapFocusing/HomogeneousAddress.lean#L91)<br>`DkMath/NumberTheory/GapFocusing/HomogeneousAddress.lean` | q素数、n>0、q∤b。単一円分層の添字。            | CFBRCのcarrierを監査して再利用                 |
| B12 | [`primeLayerAddresses_isLeast_of_one_lt_primeOrder`](../../../../DkMath/NumberTheory/GapFocusing/HomogeneousAddress.lean#L194)<br>`DkMath/NumberTheory/GapFocusing/HomogeneousAddress.lean`   | q素数、q∤b、1<primeOrder。                     | 層の最初と全GNの次の次数を区別                 |
| B13 | [`padicValNat_pow_sub_pow_mul_prime_pow`](../../../../DkMath/Lib/NumberTheory/CyclotomicLayerValuation.lean#L79)<br>`DkMath/Lib/NumberTheory/CyclotomicLayerValuation.lean`                       | q奇素数、b<a、r≠0、q∤a、q∣a^r−b^r。            | 006aでLib所有化・旧名互換 |
| B14 | [`padicValNat_pow_sub_pow_mul_two_pow_succ`](../../../../DkMath/Lib/NumberTheory/CyclotomicLayerValuation.lean#L97)<br>`DkMath/Lib/NumberTheory/CyclotomicLayerValuation.lean`                    | b<a、r≠0、a奇数、2∣a^r−b^r。和の補正項を保持。 | 006aでLib所有化・旧名互換 |
| B15 | [`GN_eq_nontrivial_phase_prod_range`](../../../../DkMath/Lib/Cosmic/GNPhaseFactorization.lean#L115)<br>`DkMath/Lib/Cosmic/GNPhaseFactorization.lean`                                          | 原始根を持つ整域、d>0、全非自明位相の積。      | Lib既存・再作成不要                            |
| B16 | [`prime_choose_exact_layer`](../../../../DkMath/Lib/Cosmic/GNPrime37.lean#L50)<br>`DkMath/Lib/Cosmic/GNPrime37.lean`                                                                          | p素数、0<k<p。正則性不要。                     | Lib既存。GNPrime37の上位Defs依存を分離する候補 |
| B17 | [`prime_GN_zmod`](../../../../DkMath/Lib/Cosmic/GNPrime37.lean#L89)<br>`DkMath/Lib/Cosmic/GNPrime37.lean`                                                                                     | ZMod p、p素数。正則性不要。                    | Lib既存・再作成不要                            |
| B18 | [`padicValNat_pow`](../../../../DkMath/Lib/NumberTheory/PadicValNat.lean#L113)<br>`DkMath/Lib/NumberTheory/PadicValNat.lean`                                                                  | p素数、a≠0。零の付値規約を保持。               | Lib既存・再作成不要                            |
| B19 | [`GN_mul_degree`](../../../../DkMath/NumberTheory/GNDegreeFactorization.lean#L31)<br>`DkMath/NumberTheory/GNDegreeFactorization.lean`                                                         | A13のNat特殊化。互換wrapper。                  | Lib一般版のNat互換wrapper                      |
| B20 | [`gap_dvd_iff_dvd_defect`](../../../../DkMath/NumberTheory/GapFocusing/Focus.lean#L50)<br>`DkMath/NumberTheory/GapFocusing/Focus.lean`                                                        | CommRing。数値xによる可除性。                  | 形式変数の零性と区別                           |
| B21 | [`X_dvd_unfocused_iff`](../../../../DkMath/NumberTheory/GapFocusing/Focus.lean#L74)<br>`DkMath/NumberTheory/GapFocusing/Focus.lean`                                                           | CommRing。形式変数Xによる可除性。              | 多項式上の条件として保持                       |
| B22 | [`GTail_one_eq_GTailCyclotomicShell`](../../../../DkMath/Lib/Cosmic/GTailCyclotomic.lean#L166)<br>`DkMath/Lib/Cosmic/GTailCyclotomic.lean`                                                    | CommSemiring、全次数・零座標を含む。           | Lib既存・再作成不要                            |

## 3. 新規APIと昇格を区別する

| 課題                        | 判定                                          | 対応・残る行動                     |
| --------------------------- | --------------------------------------------- | -------------------------------- |
| Big/Body/Gapの三つのgcd=h^d | GN-LIB-002で実装済み | `Lib.Cosmic.CompletionCoprime`。原始性不要、次数0を含む |
| R_nの有限和とGTail          | GN-LIB-004で実装済み | B22から座標変換。Nat減算にはy≤xを保持 |
| R_nの二階再帰               | GN-LIB-004で実装済み | GN後続の翻訳と有限和再帰、CommSemiring版 |
| D_nの正性・漸化式           | GN-LIB-004で実装済み | 上界→Nat差→再帰。n≥3、両座標正の条件を保持 |
| 隣接次数の互いに素性        | B03/B04は001でLib所有化、005aでRへ接続 | 環版とNat版を原始性のもとで固定 |
| 円分層のq住所=r q^k         | B08/B11に既存                                 | carrierと上位importを分離        |
| qでの次数膨張のLTE          | B13/B14に既存                                 | 奇素数と2の条件を維持            |
| gcd(R_m,R_n)=R_gcd(m,n)     | GN-LIB-005bで実装済み | 原始性を保持し、全次数で強可除列APIへ接続 |
| 原始ABC三項                 | GN-LIB-005bで実装済み | h_nの正確なgcd・可除性・再構成→正のpairwise-coprime三項 |
| 任意yでの大素数脱出         | サイズ条件が必要な後続目標                    | 追加因子と互いに素条件を先に設計 |

「特定できなかった」はリポジトリやMathlib全体での不存在を証明したという意味ではない。
実装直前にも重複を再確認する。

## 4. 昇格の先例と注意

- B19はLibのA13を呼ぶNat互換wrapperである。
- `NumberTheory.GapFocusing.Phase` は `Lib.Cosmic.GNPhaseFactorization` の互換入口であり、元のnamespaceを保持する。
- `ABC.PadicValNat` は `Lib.NumberTheory.PadicValNat` を呼ぶ互換facadeである。

新しいLibからABC・FLT・Legendre・CFBRCを逆importしない。
`[DkMath.Lib]` は実際の昇格と検証を終えた定理の完了マーカーとする。
既存配置を確認しただけで一括追記することはしない。詳細は[実装計画](IMPLEMENTATION-PLAN.md)へ。

## 5. GN-LIB-002で固定した新規一般橋

初回58宣言の棚卸しとは別に、`Lib.Cosmic.CompletionCoprime` へ13宣言を追加した。
三者gcdを中心に、原始対の三者coprime、正次数の素数支持、Bigの付値倍化を公開する。
既存58宣言の名前・型は変更していない。
[公開APIと保持条件](IMPLEMENTATION-GN-LIB-002.md)、[型と検証証跡](evidence/gn-lib-002.json) を参照。

## 6. GN-LIB-003aで所有化したBinomTail

A17の依存先を含む既存5補題を `Lib.Algebra.BinomTail` へ移管した。
A17の表は新所有者へ更新し、初回JSONは移管前snapshotとして保持する。
全修飾名・型・証明は変えていない。[実装報告](IMPLEMENTATION-GN-LIB-003a.md) と
[移管対応・型・ハッシュ](evidence/gn-lib-003a.json) を参照。

## 7. GN-LIB-003bの平方完成・有限帯

A20,A21,A23などから一般可換半環の7定理を抽出し、旧7定理をNat carrierのwrapperにした。
旧全修飾名は旧所有者に残るため、表のリンクはそのwrapperを指す。
一般核の対応先は [003b報告](IMPLEMENTATION-GN-LIB-003b.md) と [型の対応表](evidence/gn-lib-003b.json) を参照。
フルビルド・テストライブラリを省略した対象モジュール単位の検証である。

## 8. GN-LIB-003cの素数冪二項係数付値

A34と加法版、添字付値に基づく整除性、単位添字の全層整除性の4定理を
`DkMath.Lib.NumberTheory.BinomialPrimePower` に固定した。
旧 `DkMath.NumberTheory` の4名は同一の公開型で一般核へ転送する。
`UniformBeamHeight` 等の旧carrierは移していない。
素数性、非零添字、上界 `k ≤ p^n`、端点、次数0を保持した。
[003c報告](IMPLEMENTATION-GN-LIB-003c.md) と [新旧対応・型](evidence/gn-lib-003c.json) を参照。

## 9. GN-LIB-004の有限和R_nと完成不足D_n

新所有者は `Lib.Cosmic.PowerDifferenceCofactor` と `CompletionDefect`。
3定義・24定理。B22からGNの座標変換を、B01から加法座標の後続再帰を再利用した。
一般の可換半環でR_nの二階再帰を固定し、自然数の上界を証明してから不足を定義した。
環の符号付き不足と自然数の不足を区別し、再構成・再帰・正性・castの橋を固定した。
既存A/Bの宣言の移動や型変更は行っていない。
[004報告](IMPLEMENTATION-GN-LIB-004.md) と [全宣言・型・ハッシュ](evidence/gn-lib-004.json) を参照。

## 10. GN-LIB-005aの奇数完成不足coprime

`Lib.NumberTheory.PowerDifferenceCofactorGcd` の11定理と、
`Lib.Cosmic.PowerDifferenceCofactor` のcast定理1個を追加した。
A10のgap gcdを保持した橋、B04からの隣接Bézout関係とNat特殊化、
奇数合同式 `R_(2k+1) ≡ (-xy)^k (mod x+y)`、原始座標でのsum/deficit coprimeを固定した。
Natの `Odd n` 入口では原始性を明示する。零座標や次数1に不要な正性は課さない。
既存定理の型・本文を変更せず、強可除性・偶数精密gcd・ABC三項は後続に残した。
[005a報告](IMPLEMENTATION-GN-LIB-005a.md) と [全新定理・型・ハッシュ](evidence/gn-lib-005a.json) を参照。

## 11. GN-LIB-005bの強可除性と原始借入三項

3新所有者に4定義・25定理、16例を追加した。
加法・指数積の恒等式、原始座標での強可除性とMathlib列APIへの接続、
借入補正との正確なgcd、h_nによる三つの分子の可除性と再構成、
正のpairwise-coprimeなA+B=Cの終点を固定した。
倍次数と平方借入はCommSemiringの恒等式であり、底がx²,y²に変わることを明示する。
原始性を落とすと強可除性・正規化後のcoprimeが壊れる例も確認した。
[005b報告](IMPLEMENTATION-GN-LIB-005b.md) と [全新宣言・型・ハッシュ](evidence/gn-lib-005b.json) を参照。

## 12. GN-LIB-006aの位数・通常円分住所・LTE

比／位数2定義・一般7定理、通常円分住所8定理、層付値8定理をLib所有へ移管した。
全25宣言の歴史的namespace、型、証明／定義本体を保持し、旧モジュールを互換入口にした。
全余因子R_nの素数出現は新5定理として分離し、r>1とr=1の枝、次数0、2進補正を保持した。
B11/B12の斉次carrierは変更せず、006bでCFBRCとの互換を先に設計する。006全体は継続中。
[006a報告](IMPLEMENTATION-GN-LIB-006a.md) と [対応・型・依存](evidence/gn-lib-006a.json) を参照。
