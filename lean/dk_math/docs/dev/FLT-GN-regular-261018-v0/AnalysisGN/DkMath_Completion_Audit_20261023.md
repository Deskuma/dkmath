# DkMath Completion・GN・PrimeAddress 定理棚卸しと Facade 設計

基準：2026-10-22 00:15 の添付 snapshot（SHA256一致）、調査日：2026-10-23。
リポジトリ元ブランチ：`dev/FLT-GN-regular-261018-v0`（ハンドオフの記録に基づく）。

## 監査の判定範囲

- Lean 2026-10-22 snapshot の `.lean` ファイルから **宣言名と行番号が存在すること** を機械的に確認した。
- この調査環境には `lean` / `lake` がないため **新規 Lean ビルドや kernel の独立検証は行っていない**。
- 「既存」はソースにその宣言があることを指す。命題が条件付きの場合、その条件まで証明済みとは意味しない。
- 典型的なアプリ固有の同値定理（Legendre の同値等）を conjecture の完成と取り違えない。
- **これは既存定理の公開面を整理する作業であって、FLT の新規証明ではない**。

## 設計上の結論

1. **Lib の既存 GN / GTail / 核は移動しない**。新しい `DkMath.Lib.Cosmic.Completion` を import-only facade とする。
2. **既存の `Gnomon`、`Primitive`、`PrimorialUniverse`、`Legendre` の実装をすぐ Lib に取り込まない**。いきなりの移動は import 逆流と既存参照の破壊を招く。
3. 分野別の再公開層 `DkMath.NumberTheory.Completion` を作り、最上位 `DkMath.Completion` が既存の Bridge・回帰例を束ねる。
4. 共通構造の抽出は「原定義の名前・型・namespace を維持したまま独立補題へ置換」してから。旧名は alias / lemma forwarding を使う。

## ソース監査済みの定理一覧

| 領域 | 定理・定義 | 元ファイル（行） | 措置 | 役割・注意 |
|---|---|---|---|---|
| GN/Cosmic | `add_pow_eq_mul_GTail_one_add_gap` | `DkMath/Lib/Cosmic/GTail.lean:132` | Lib既存 | (x+u)^d = x * GTail d 1 x u + u^d。完成三項分解の最優先API |
| GN/Cosmic | `GTail_rec` | `DkMath/Lib/Cosmic/GTail.lean:165` | Lib既存 | GTail を次の切断次数へ再帰分解。次数でなく切断 index を再帰する点に注意 |
| GN/Cosmic | `powerCore_split` | `DkMath/Lib/Cosmic/CoreNested.lean:44` | Lib既存 | 冪差の二段分割・telescoping。差の保存は完全冪状態の降下ではない |
| GN/Cosmic | `powerCore_eq_gtail_one` | `DkMath/Lib/Cosmic/CoreNested.lean:62` | Lib既存 | 冪差と GTail の橋。既存 Core 語彙と GN を接続 |
| GN/Cosmic | `selected_balance_eq_pow_add_powerCore` | `DkMath/Lib/Cosmic/CoreNestedTransport.lean:27` | Lib既存 | 選択項の balance と powerCore の接続。選択切断の保存則 |
| GN/Cosmic | `selectedGap_add_selectedBody` | `DkMath/Lib/Cosmic/GTailSelection.lean:38` | Lib既存 | 任意の項集合選択で Big を復元。Gap/Body 任意分割 |
| GN/Cosmic | `selected_balance_transport` | `DkMath/Lib/Cosmic/GTailTransport.lean:81` | Lib既存 | 項の移動をしたときの保存。不足の貸借操作の代数核 |
| Pascal/prime | `coeffGCD_prime_interior` | `DkMath/Lib/Cosmic/GTailFactor.lean:178` | Lib既存 | 素数行の内部係数 gcd = p。素数次数の新たな係数共通因子 |
| Pascal/prime | `prime_mul_coords_dvd_selectedBody_interior` | `DkMath/Lib/Cosmic/GTailFactor.lean:189` | Lib既存 | p*x*u が内部交差項 Body を割る。元の量の素数性とは別 |
| gcd | `gcd_GN_eq_gcd_of_one_le` | `DkMath/Lib/Cosmic/GTailBoundary.lean:61` | Lib既存 | primitive 時 gcd(g,GN)=gcd(g,d)。指数例外を厳密化 |
| gcd | `prime_dvd_GN_iff_dvd_gap` | `DkMath/Lib/Cosmic/GTailCongruence.lean:181` | Lib既存 | 素数次数 p で p|GN iff p|gap。p=2 含む |
| valuation | `padicValNat_GN_prime_eq_one_of_dvd_gap` | `DkMath/Lib/Cosmic/GTailPadic.lean:191` | Lib既存 | 条件付き GN の p 進付値1。条件は本体で確認 |
| GN/Cosmic | `GN_mul_degree` | `DkMath/Lib/Cosmic/GNProductDegree.lean:53` | Lib既存 | 合成次数 ab の GN 積分解。合成次数一般化 |
| cyclotomic | `GTail_one_eq_cyclotomicHomEval_of_prime` | `DkMath/Lib/Cosmic/GTailCyclotomic.lean:233` | Lib既存 | 素数次数 GN と円分評価の橋。環と型条件に注意 |
| d=7 | `add_pow_seven_sub_endpoints` | `DkMath/Lib/Cosmic/GTailSeven.lean:107` | Lib既存 | 7次両端除去因数分解。一般核ではなく回帰例として保持 |
| d=7 | `coprime_sum_seven_quadratic` | `DkMath/Lib/Cosmic/GTailSevenArithmetic.lean:39` | Lib既存 | primitive pair で sum と二次形式 coprime。七次専用補題；一般化は別途 |
| mixed terms | `add_pow_gt_sum_pows_nat_of_two_le` | `DkMath/Algebra/BinomTail.lean:188` | 昇格候補 | d≥2 の内部交差項は正。Lib.Algebra 移管は依存整理後 |
| GN/Cosmic | `add_pow_gap_factor` | `DkMath/CosmicFormula/CosmicFormulaBinom.lean:383` | 薄いadapter | Big = Gap + xGN の legacy facade。Lib の canonical GTail を再利用 |
| perfect power | `body_not_perfect_pow_of_squarefree_GN` | `DkMath/CosmicFormula/CosmicFormulaBinom.lean:497` | 昇格候補 | squarefree GN + coprime から Body は完全冪でない。squarefree 仮定付きであり FLT一般不可 |
| square gnomon | `square_add_squareGnomonBand` | `DkMath/Gnomon/Algebra.lean:102` | 昇格候補 | x² + u(2x+u) = (x+u)²。中立実装だが配置は Gnomon; namespace互換必須 |
| square gnomon | `squareGnomonBand_eq_sum_shifted_oddGnomon` | `DkMath/Gnomon/Algebra.lean:125` | 昇格候補 | 太い帯を奇数幅の単位帯へ telescoping。有限和の汎用化 |
| square gnomon | `squareGnomonBand_eq_mul_GTail_two_one` | `DkMath/Gnomon/CosmicBridge.lean:43` | Bridge保持 | 2次の平方帯と GTail の一致。Lib から Gnomon を逆輸入させない |
| square completion | `squareBody_add_one_eq` | `DkMath/NumberTheory/Primitive/SquareBody.lean:42` | 昇格候補 | squareBody P + 1 = (P+1)^2。算術式のみなら Lib.Algebra 候補 |
| square/primes | `prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody` | `DkMath/NumberTheory/Primitive/SquareBody.lean:98` | Primitive保持 | old support を回避した squareBody 内の整数は素数。primeScalesUpTo の意味に依存 |
| finite prime world | `squarePrimeExpansion_eq_primeScalesUpTo_squareBody` | `DkMath/NumberTheory/Primitive/SquarePrimeExpansion.lean:86` | Primitive保持 | 有限 prime world の拡張と平方 Body。一般 gcd 恒等式へ昇格しない |
| regression P30 | `squareBody_thirty_add_one_eq_thirtyOne_sq` | `DkMath/NumberTheory/PrimorialUniverse/ThirtySquareWorld.lean:67` | 特例保持 | P=30 の961=31²。回帰テスト |
| PrimeAddress | `primeWorldResidues_eq_packetBase` | `DkMath/NumberTheory/Legendre/PrimeWorldPacketBridge.lean:23` | Bridge既存 | modulus>1 で wheel residues と packet 一致。旧課題が snapshot では実装済 |
| PrimeAddress | `supportDisjointFrom_iff_coprime_primeWorldModulus` | `DkMath/NumberTheory/Primitive/PeriodicPrimeWorld.lean:163` | Primitive保持 | old prime support 不在 iff modulus に coprime。基礎 wheel |
| PrimeAddress | `card_survivingChildIndices` | `DkMath/NumberTheory/Primitive/PrimeWorldRefinement.lean:357` | Primitive保持 | 新 prime 追加後の生存 q-1 子住所。CRT refinement |
| Legendre | `squareOffset_prime_iff_projection_survivor` | `DkMath/NumberTheory/Legendre/PrimorialWheelBridge.lean:109` | Legendre保持 | square shell における prime と projection。Legendre 条件依存 |
| Legendre | `legendreConjecture_iff_open_oddGnomon_prime` | `DkMath/NumberTheory/Legendre/GnomonBridge.lean:89` | Legendre保持 | Legendre と open square gnomon の同値。条件付き同値であり予想証明ではない |
| Kummer carry | `gnomonPascalCell_factorization_carries` | `DkMath/NumberTheory/Legendre/GnomonPascalCell.lean:71` | 抽出候補 | 平方 shell の choose 付値を carry と同一視。一般 carry の Lib 化は別設計 |
| Legendre packet | `coprime_squarePacketPoints_of_coprime_offset` | `DkMath/NumberTheory/Legendre/PacketCoprimality.lean:37` | Bridge保持 | 向かい二席が coprime。square shell n の特殊形 |
| Pascal/prime | `padicValNat_choose_prime_pow` | `DkMath/NumberTheory/BinomialPrimePower.lean:210` | 昇格候補 | p^r 行の binomial 付値。ABC.PadicValNat への依存を解消してから |
| real vs discrete | `unitCoordinate_refine` | `DkMath/NumberTheory/PrimorialUniverse/UnitCoordinateRefinement.lean:77` | 昇格候補 | 実数点の単位変更・Nat座標 refinement。独立化できる部分と prime 依存部を分離 |
| finite prime world | `finitePrimeBasis_subset_primeScalesUpTo_product` | `DkMath/NumberTheory/PrimorialUniverse/SquareBodyBridge.lean:63` | Primitive保持 | 有限素数基底を積アンカーの prime closure へ。アプリ意味論に依存 |

監査した宣言: **36 件**、異なるソースファイル: **30 件**。
ファイル全文を単純文字列で検査した `sorry` / `axiom` 出現モジュール: **0 件**（構文・依存公理の検証ではない）。

## 推奨する依存グラフ

```text
DkMath.Lib.Cosmic.Completion
  └─ 既存 Lib.Cosmic.GTail / CoreNested / GTail* / GNProductDegree ...

DkMath.NumberTheory.Completion
  ├─ 既存 DkMath.Algebra.BinomTail
  ├─ 既存 NumberTheory.Primitive.*
  ├─ 既存 NumberTheory.PrimorialUniverse.*
  ├─ 既存 NumberTheory.Legendre.*
  └─ 既存 NumberTheory.BinomialPrimePower

DkMath.Completion
  ├─ DkMath.Lib.Cosmic.Completion
  ├─ DkMath.NumberTheory.Completion
  ├─ DkMath.CosmicFormula.CosmicFormulaBinom (legacy)
  ├─ DkMath.Gnomon.Algebra / CosmicBridge
  └─ Lib.Cosmic.GTailSeven* (特殊次数回帰)
```

`DkMath.Lib.Cosmic.Completion` は NumberTheory.Legendre などを import しない。これにより上位の応用層から一般理論へ import が逆流しない。

## 昇格（移管）候補の優先順

1. **正の混合項の存在と差分**: `DkMath.Algebra.BinomTail.add_pow_gt_sum_pows_nat_of_two_le` は汎用。`Lib.Algebra` に *別実装せず* 数学的内容を移動する余地がある。
2. **平方 Body の単純等式**: `Primitive.SquareBody.squareBody_add_one_eq` や `Gnomon.Algebra.square_add_squareGnomonBand` は中立。ただし `squareBody` と `squareGnomonBand` の既存名を壊さず、Lib に無条件一般式を抽出してアプリ側は証明のラッパーにする。
3. **Kummer/Pascal の一般公式**: `BinomialPrimePower.padicValNat_choose_prime_pow` は指数一般の命題だが `DkMath.ABC.PadicValNat` 依存。まず既存 `Lib.NumberTheory.PadicValNat` などへの置換可能性と循環 import を監査する。
4. **相対単位と座標**: `PrimorialUniverse.UnitCoordinateRefinement.PositiveUnit` と `unitCoordinate_refine` は prime-world に依存しない部分だけ Lib 側への分割を検討。
5. **GN 完成三項の一般 gcd**: `gcd((x+u)^d,u^d)=gcd(x,u)^d` および `gcd(Body,Gap)=...` 等を **明示的な単一 bridge** として提供する余地がある。Mathlib の gcd 既存定理との重複を先に確認。

## 「新規」と取り違えない既存接続

- `PrimeWorldPacketBridge.primeWorldResidues_eq_packetBase` は既に存在（ただし `1 < primeWorldModulus S` 条件）。新たな adapter は不要。
- 7次交差項の `GTailSeven.add_pow_seven_sub_endpoints` は既に Lib 側にある。general theorem と取り違えず **特殊回帰** に位置づける。
- `Gnomon.CosmicBridge` で平方グノモンと `GTail 2 1` が一致済み。
- `ThirtySquareWorld` の 30→960→961 も回帰テストとして存在済み。
- `legendreConjecture_iff_open_oddGnomon_prime` は **同値命題** であり、Legendre の予想を証明した意味ではない。

## 今回新しく作っていない研究課題

- 余因子 `R_n=(x^n-y^n)/(x-y)` と不足量 `D_n=(x+y)^(n-1)-R_n` を GN へ接続する一般 bridge、および prime-address/valuation を保った降下変換は、既存定理一覧とは区別する。
- 実数上の幾何完成と `Nat` の素因数分解は同一概念にしない。`PositiveUnit` による座標射影を経て整数算術を評価する。

## 配置・テスト手順

1. 添付 ZIP の `.lean` を各パスのまま `lean/dk_math/` 直下へ追加。旧ファイルは変更しない。
2. `lake build DkMath.Lib.Cosmic.Completion`（Lib だけ）を先に確認。
3. `lake build DkMath.NumberTheory.Completion`、`lake build DkMath.Completion` と順に確認。
4. 既存の DkMath 全体で依存循環を確認し、`lake build DkMath DkMath.Lib DkMathTest`。
5. 追加 Facade 内には数学的 theorem、`sorry`、axiom を置かず、audit は import の整合性に限定。
6. 次の PR に一般定理の本体昇格を分ける。昇格先と旧 namespace の互換性を Lean の `#check` で回帰する。

### 最初に `#check` してほしい公開 API

```lean
import DkMath.Completion

#check DkMath.CosmicFormula.add_pow_eq_mul_GTail_one_add_gap
#check DkMath.Lib.Cosmic.powerCore_split
#check DkMath.CosmicFormula.coeffGCD_prime_interior
#check DkMath.CosmicFormula.gcd_GN_eq_gcd_of_one_le
#check DkMath.Gnomon.squareGnomonBand_eq_mul_GTail_two_one
#check DkMath.NumberTheory.Primitive.squareBody_add_one_eq
#check DkMath.NumberTheory.PrimorialUniverse.squareBody_thirty_add_one_eq_thirtyOne_sq
#check DkMath.NumberTheory.Legendre.primeWorldResidues_eq_packetBase
```

注意：`import DkMath.Completion` は比較的重い研究用 Facade。一般算術だけ使うモジュールからは `DkMath.Lib.Cosmic.Completion` を選択すること。
