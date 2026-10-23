# 現行Leanの定理棚卸し

2026-10-23。添付監査の36宣言（A01–A36）と追加調査22宣言（B01–B22）。
合計58宣言・42所有モジュール。添付36宣言のソース行は現行と一致し、うち16宣言は既にLib配下にある。
今回の58宣言は所有モジュールのビルド後に`#check`と`Lean.collectAxioms`で確認し、依存公理は標準の3つ以内だった。
この検査は既存宣言に対するもの。新しい一般化、ZIP facadeの配置、全面的な依存層監査は別工程である。

初回棚卸しの全修飾名・ソース宣言・暗黙引数・SHA256は[source-inventory.json](evidence/source-inventory.json)に保存した。
B01–B05はGN-LIB-001で移管済みであり、下表は新しい所有先を示す。
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
| A17 | [`add_pow_gt_sum_pows_nat_of_two_le`](../../../../DkMath/Algebra/BinomTail.lean#L188)<br>`DkMath/Algebra/BinomTail.lean`                                                                          | Nat、2≤n、a,b>0。                                          | 昇格候補                     |
| A18 | [`add_pow_gap_factor`](../../../../DkMath/CosmicFormula/CosmicFormulaBinom.lean#L383)<br>`DkMath/CosmicFormula/CosmicFormulaBinom.lean`                                                           | CommSemiring。A01のlegacy語彙への転送。                    | 薄いadapter                  |
| A19 | [`body_not_perfect_pow_of_squarefree_GN`](../../../../DkMath/CosmicFormula/CosmicFormulaBinom.lean#L497)<br>`DkMath/CosmicFormula/CosmicFormulaBinom.lean`                                        | 1<d、1<GN、Coprime x GN、Squarefree GN。                   | 昇格候補                     |
| A20 | [`square_add_squareGnomonBand`](../../../../DkMath/Gnomon/Algebra.lean#L102)<br>`DkMath/Gnomon/Algebra.lean`                                                                                      | Nat、平方帯の定義を保持。                                  | 昇格候補                     |
| A21 | [`squareGnomonBand_eq_sum_shifted_oddGnomon`](../../../../DkMath/Gnomon/Algebra.lean#L125)<br>`DkMath/Gnomon/Algebra.lean`                                                                        | Nat、平方帯の有限和分割。                                  | 昇格候補                     |
| A22 | [`squareGnomonBand_eq_mul_GTail_two_one`](../../../../DkMath/Gnomon/CosmicBridge.lean#L43)<br>`DkMath/Gnomon/CosmicBridge.lean`                                                                   | Nat、平方帯とGTailのbridge。                               | Bridge保持                   |
| A23 | [`squareBody_add_one_eq`](../../../../DkMath/NumberTheory/Primitive/SquareBody.lean#L42)<br>`DkMath/NumberTheory/Primitive/SquareBody.lean`                                                       | Nat、P=0含む。squareBodyは上位定義。                       | 昇格候補                     |
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
| A34 | [`padicValNat_choose_prime_pow`](../../../../DkMath/NumberTheory/BinomialPrimePower.lean#L210)<br>`DkMath/NumberTheory/BinomialPrimePower.lean`                                                   | p素数、0<k≤p^n。n=0も現行署名に含む。                      | 昇格候補                     |
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
| B08 | [`isRoot_cyclotomic_iff_prime_pow_mul_orderOf`](../../../../DkMath/NumberTheory/GapFocusing/CyclotomicAddress.lean#L27)<br>`DkMath/NumberTheory/GapFocusing/CyclotomicAddress.lean`           | 整域、CharP R q、q素数、n>0。                  | 中立核抽出候補                                 |
| B09 | [`int_dvd_pow_sub_pow_iff_primeOrder_dvd`](../../../../DkMath/NumberTheory/GapFocusing/PrimeOrder.lean#L40)<br>`DkMath/NumberTheory/GapFocusing/PrimeOrder.lean`                              | q素数、q∤b。冪差全体の可除性。                 | Zsigmondy依存を分離して再利用                  |
| B10 | [`primeOrder_dvd_prime_sub_one`](../../../../DkMath/NumberTheory/GapFocusing/PrimeOrder.lean#L61)<br>`DkMath/NumberTheory/GapFocusing/PrimeOrder.lean`                                        | q素数、q∤a,b。                                 | qと座標の非可除条件を保持                      |
| B11 | [`dvd_cyclotomicShiftedEval_iff_prime_pow_mul_orderOf`](../../../../DkMath/NumberTheory/GapFocusing/HomogeneousAddress.lean#L91)<br>`DkMath/NumberTheory/GapFocusing/HomogeneousAddress.lean` | q素数、n>0、q∤b。単一円分層の添字。            | CFBRCのcarrierを監査して再利用                 |
| B12 | [`primeLayerAddresses_isLeast_of_one_lt_primeOrder`](../../../../DkMath/NumberTheory/GapFocusing/HomogeneousAddress.lean#L194)<br>`DkMath/NumberTheory/GapFocusing/HomogeneousAddress.lean`   | q素数、q∤b、1<primeOrder。                     | 層の最初と全GNの次の次数を区別                 |
| B13 | [`padicValNat_pow_sub_pow_mul_prime_pow`](../../../../DkMath/NumberTheory/GapFocusing/LayerValuation.lean#L71)<br>`DkMath/NumberTheory/GapFocusing/LayerValuation.lean`                       | q奇素数、b<a、r≠0、q∤a、q∣a^r−b^r。            | 既存の範囲付きLTEを再利用                      |
| B14 | [`padicValNat_pow_sub_pow_mul_two_pow_succ`](../../../../DkMath/NumberTheory/GapFocusing/LayerValuation.lean#L85)<br>`DkMath/NumberTheory/GapFocusing/LayerValuation.lean`                    | b<a、r≠0、a奇数、2∣a^r−b^r。和の補正項を保持。 | 補正項を消さない                               |
| B15 | [`GN_eq_nontrivial_phase_prod_range`](../../../../DkMath/Lib/Cosmic/GNPhaseFactorization.lean#L115)<br>`DkMath/Lib/Cosmic/GNPhaseFactorization.lean`                                          | 原始根を持つ整域、d>0、全非自明位相の積。      | Lib既存・再作成不要                            |
| B16 | [`prime_choose_exact_layer`](../../../../DkMath/Lib/Cosmic/GNPrime37.lean#L50)<br>`DkMath/Lib/Cosmic/GNPrime37.lean`                                                                          | p素数、0<k<p。正則性不要。                     | Lib既存。GNPrime37の上位Defs依存を分離する候補 |
| B17 | [`prime_GN_zmod`](../../../../DkMath/Lib/Cosmic/GNPrime37.lean#L89)<br>`DkMath/Lib/Cosmic/GNPrime37.lean`                                                                                     | ZMod p、p素数。正則性不要。                    | Lib既存・再作成不要                            |
| B18 | [`padicValNat_pow`](../../../../DkMath/Lib/NumberTheory/PadicValNat.lean#L113)<br>`DkMath/Lib/NumberTheory/PadicValNat.lean`                                                                  | p素数、a≠0。零の付値規約を保持。               | Lib既存・再作成不要                            |
| B19 | [`GN_mul_degree`](../../../../DkMath/NumberTheory/GNDegreeFactorization.lean#L31)<br>`DkMath/NumberTheory/GNDegreeFactorization.lean`                                                         | A13のNat特殊化。互換wrapper。                  | Lib一般版のNat互換wrapper                      |
| B20 | [`gap_dvd_iff_dvd_defect`](../../../../DkMath/NumberTheory/GapFocusing/Focus.lean#L50)<br>`DkMath/NumberTheory/GapFocusing/Focus.lean`                                                        | CommRing。数値xによる可除性。                  | 形式変数の零性と区別                           |
| B21 | [`X_dvd_unfocused_iff`](../../../../DkMath/NumberTheory/GapFocusing/Focus.lean#L74)<br>`DkMath/NumberTheory/GapFocusing/Focus.lean`                                                           | CommRing。形式変数Xによる可除性。              | 多項式上の条件として保持                       |
| B22 | [`GTail_one_eq_GTailCyclotomicShell`](../../../../DkMath/Lib/Cosmic/GTailCyclotomic.lean#L166)<br>`DkMath/Lib/Cosmic/GTailCyclotomic.lean`                                                    | CommSemiring、全次数・零座標を含む。           | Lib既存・再作成不要                            |

## 3. 新規APIと昇格を区別する

| 課題                        | 判定                                          | 実装前の行動                     |
| --------------------------- | --------------------------------------------- | -------------------------------- |
| Big/Body/Gapの三つのgcd=h^d | 一体化したLib APIは今回特定できなかった       | A01と既存gcd算術から薄い橋を作る |
| R_nの有限和とGTail          | B22の殻が同じ幾何和を持つ                     | 除算定義を避け、座標変換を固定   |
| R_nの二階再帰               | B01/B02を合成して再利用可能                   | 同じ底の再帰へ翻訳               |
| D_nの正性・漸化式           | 同型の独立APIは今回特定できなかった           | 自然数差の前に上界を証明         |
| 隣接次数の互いに素性        | B03/B04に既存                                 | 所有層の抽出と旧名互換           |
| 円分層のq住所=r q^k         | B08/B11に既存                                 | carrierと上位importを分離        |
| qでの次数膨張のLTE          | B13/B14に既存                                 | 奇素数と2の条件を維持            |
| gcd(R_m,R_n)=R_gcd(m,n)     | 今回の限定検索では直接のAPIを特定できなかった | 加法公式・互除法の再利用を再確認 |
| 原始ABC三項                 | 資料の有限観測。独立APIは今回特定できなかった | h_n可除性→加法→互いに素性→正性   |
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
