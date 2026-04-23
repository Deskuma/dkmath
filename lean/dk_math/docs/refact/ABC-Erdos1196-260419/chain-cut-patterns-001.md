# ABC 連番チェイン切断メモ 001

## 目的

`ABC001.lean -> ABC002.lean -> ... -> ABC040.lean` の直列 import は、
分割時の保存を優先した結果であり、依存の最小化を反映していない。
このメモは、どの種類の依存が切りやすいか、どこが break point になりうるかを
次サイクルで再利用できる形に固定する。

## 現状の観測

- `ABC001` だけはすでに直列起点ではなく、
  `DkMath.ABC.Square` と `DkMath.ABC.RatioBound` を直接 import している。
- `ABC009` は `ABC008` に加えて `DkMath.ABC.Core` を直接 import している。
  これは `RpowExtras` owner がまだ `Core` に残っていることを示す。
- `ABC024`, `ABC025`, `ABC028` は
  `CountPowersDividing2n1` を直接 import しており、
  すでに serial chain を横切る seed になっている。
- `ABC025` はさらに
  `ABC025_bound2` と `PadicValNat` を直接 import している。
- `ABC002` 以降の多くの file は、
  依然として前番号 file を 1 本だけ import している。

## 切断パターン

### 1. Owner import 露出型

直列 predecessor を通じて見えていた補題が、
public entry build で unknown identifier として露出する型。

例:

- `coprime_succ` は `DkMath.Basic.Nat` owner
- `RpowExtras.rpow_mul_nat` は現状 `DkMath.ABC.Core` owner

処方:

- 使用 file に owner module を explicit import する
- 必要なら `open` または fully-qualified name に置き換える

効果:

- 直列 predecessor が「何となく持っていた」依存を可視化できる
- chain を切る前に、symbol owner の棚卸しが進む

### 2. Shared utility 横刺し型

複数の `ABC連番` file が同じ補題群を使うが、
それが predecessor を経由してしか見えていない型。

現時点の seed:

- `CountPowersDividing2n1`
- `PadicValNat`
- `Square`
- `RatioBound`

処方:

- serial predecessor ではなく utility module を直接 import する
- 同じ utility に依存する file 群を cluster として切り出す

効果:

- 「前番号だから import」ではなく
  「このテーマの kernel だから import」という構造へ寄せられる

### 3. Thin base + thematic band 型

連番の中に、同じテーマの帯が見えている。

候補:

- `ABC001`-`ABC009`:
  Adjacent / diagonal / middle-band 前段
- `ABC024`-`ABC028`:
  p-adic counting / layer-cake / MGF 帯
- `ABC031`-`ABC040`:
  tail / quality / Chernoff 接続帯

処方:

- 帯の先頭に utility import を寄せる
- 帯内部では predecessor import を減らし、
  帯の public seed file を 1 つ決める

効果:

- 40 本の鎖ではなく、数本の thematic chain に落とせる

## 次に試すと良い具体候補

### 候補 A: `RpowExtras` 専用 module 化

理由:

- `ABC009` が `Core` を直接 import する唯一の明確な理由が
  `RpowExtras.rpow_mul_nat` である
- ここを `ABC.RpowExtras` のような薄い module に切れば、
  `ABC009 -> Core` 依存を落とせる可能性が高い

期待効果:

- `Core` の catch-all 性をさらに削れる
- `ABC009` 以降の middle-band chain が `Core` 非依存に寄る

### 候補 B: `ABC024`-`ABC028` の utility-first 化

理由:

- すでに `CountPowersDividing2n1` と `PadicValNat` を直接 import し始めている
- serial predecessor が純粋な utility owner ではないことが可視化されている

期待効果:

- p-adic / layer-cake 帯の chain を短くできる
- `ABC025_bound2` を seed とする小 cluster 化がしやすい

進捗:

- 2026/04/21 の first cut で
  `ABC024.lean`
  から
  `import DkMath.ABC.ABC023`
  を外し、
  `ABC022` + `RatioBound` + `CountPowersDividing2n1`
  の direct import に置換した
- `ABC024`, `ABC025`, `ABC028`
  の build は成功
- この帯では
  empty relay
  を飛ばして owner import へ寄せるパターンが有効だと確認できた
- 次の観測点は、
  `ABC025` 以降で
  `ABC024`
  由来のものと
  `ABC025`
  自身の kernel をどう分離するか
- 2026/04/22 の次段では
  `ABC025.lean`
  から
  `import DkMath.ABC.ABC024`
  を削除しても build が通ることを確認した
- 同時に
  `ABC028`
  では
  `markov_card_bound`
  の owner が
  `ABC019`
  だと露出し、
  thematic band 内でも hidden import 探索が有効に働くことを確認した

### 候補 C: `ABC001`-`ABC003` の base seam 固定

理由:

- `ABC001` はすでに `Square`, `RatioBound` を直接 import している
- `ABC002`, `ABC003` で `coprime_succ` hidden import が露出し、
  owner import 明示化が始まった

期待効果:

- chain の先頭 3 本を「base combinatorial band」として扱える
- 以後の `ABC004+` から predecessor reliance を段階的に観測しやすい

## ノート

- `DkMath.ABC.Demo.*` は standalone / 非対象としてこのメモから除外する。
- `ABC090.lean` には comment block 内に `ABC041` 相当の残骸が見えるが、
  これは chain-cut とは別件の cleanup 候補である。
- `ABC031`-`ABC040` 帯では、
  `ABC033`
  の時点で
  `three_pow_ge_linear -> Core`,
  `rpow_layer_cake -> ABC022`
  という hidden import が露出した。
  この帯も
  predecessor chain
  より utility owner import を先に揃える方が良い。
- 同じ `ABC033` で、
  serial predecessor
  `ABC032`
  自体は不要で、
  実依存は
  `ABC025`
  の
  `ABC.Telescoping.sum_pow_padicValNat_le_geom_log2_div_log3`
  だったことも確認できた。
  つまりこの帯では
  「直前 file を引いているが、実際にはもっと前の thematic kernel を使っている」
  という chain drift が起きている。
- `ABC090`
  では別パターンとして、
  predecessor どころか
  empty relay
  しか引いていない shell file が確認できた。
  この種の file は
  thematic kernel
  すら要らず、
  `ABC.Basic`
  のような最小環境 import に落とせる。
- `ABC038`
  では
  `ABC037`
  relay を外しても通った一方で、
  `ABC039`
  では
  `ABC037`
  owner の
  `bad_set_density_bound_quality`
  が direct import として必要になった。
  つまり
  `ABC031`-`ABC040`
  帯は一本鎖ではなく、
  quality branch と density branch が途中で分岐している。
- 同じ帯の前半でも、
  `ABC036`
  は
  `ABC035`
  の union-bound layer を使っておらず、
  実依存は
  `ABC034`
  の
  `chernoff_single_prime_uniform_rpow`
  だった。
  つまり
  `ABC034 -> ABC036`
  は
  single-prime branch、
  `ABC035`
  は
  union-bound branch
  として分けて見たほうが依存実態に近い。
- さらに
  `ABC033`
  自体は番号付き predecessor として保持する必要が薄く、
  中身は
  single-prime Chernoff kernel
  そのものだった。
  したがってこの層は
  `ChernoffSinglePrime`
  のような非連番 utility module を owner にし、
  `ABC033`
  は compatibility relay に落とすのが自然だった。
  これは
  `thin base + thematic band`
  を
  「帯の先頭番号 file」
  ではなく
  「非連番 thematic utility」
  に置き換えるパターンの具体例になる。
- 同じパターンは utility module の内部にも適用できる。
  今回は
  `ChernoffSinglePrime`
  をさらに
  `ChernoffBasic`
  と
  `ChernoffSinglePrime`
  に割り、
  notation/constants/Markov
  と
  MGF/engine
  を分離した。
  つまり
  chain cut
  は
  `ABC0**`
  から utility owner へ寄せる段だけでなく、
  utility owner 自体を
  `basic + engine`
  に薄く割る段まで進められる。
- utility owner 化の次段として、
  番号 file 自体を compatibility relay に降格できる。
  今回は
  `ABC034`
  がその具体例になった。
  `chernoff_single_prime_uniform`
  と
  `chernoff_single_prime_uniform_rpow`
  を
  `ChernoffSinglePrime`
  へ移した結果、
  `ABC034`
  は
  `import DkMath.ABC.ChernoffSinglePrime`
  だけを持つ thin relay に落とせた。
  つまり
  `thin base + thematic utility`
  は
  「番号 file の import を owner import に置き換える」
  段で終わらず、
  「番号 file から convenience theorem も吸い上げて relay 化する」
  段まで進められる。
- この relay 化パターンは
  単一 branch だけでなく、
  その上位 branch にも連鎖適用できる。
  今回は
  `ABC035`
  の
  explicit specialization / union-bound 層を
  `ChernoffUnionBound`
  に移し、
  `ABC035`
  自体を relay に落とした。
  つまり
  `ChernoffBasic -> ChernoffSinglePrime -> ChernoffUnionBound`
  の thematic band を先に立ててから、
  `ABC033`, `ABC034`, `ABC035`
  を順に compatibility relay 化する、
  という階段状の chain cut が実際に機能する。
- 同じ階段を
  density branch
  にも延長できる。
  今回は
  `ABC036`
  の
  `Bad_ε` / `bad_set_density_bound_param`
  などを
  `ChernoffDensity`
  に移し、
  `ABC036`
  を relay 化した。
  さらに
  `ABC037`
  と
  `ABC038`
  は
  `ABC036`
  を経由せず、
  owner module
  `ChernoffDensity`
  を direct import する形に寄せられた。
  つまり
  chain cut
  の完成形は
  「relay を残す」
  だけでなく、
  downstream を順次 direct owner import へ付け替える
  段まで含む。
- quality-specific specialization も、
  density owner の上に
  さらに一段 utility を重ねる形で分離できる。
  今回は
  `ABC037`
  の
  `construct_HΛ_for_quality`
  と
  `bad_set_density_bound_quality`
  を
  `ChernoffQualityDensity`
  に移し、
  `ABC037`
  を relay 化した。
  さらに
  `ABC039`
  は
  `ABC037`
  ではなく
  `ChernoffQualityDensity`
  を direct import する形へ寄せられた。
  したがって
  Chernoff 帯は
  `Basic -> SinglePrime -> UnionBound -> Density -> QualityDensity`
  の多段 thematic band として持ち上げられる。
- この quality branch は
  さらに
  `Bridge`
  と
  `Final`
  に二段分解できる。
  今回は
  `ABC038`
  を
  `ChernoffQualityBridge`
  へ、
  `ABC039`
  を
  `ChernoffQualityFinal`
  へ昇格させた。
  したがって
  Chernoff 帯の終端は
  `Basic -> SinglePrime -> UnionBound -> Density -> QualityDensity -> QualityBridge -> QualityFinal`
  と読める。
- この時点で
  `ABC038` / `ABC039`
  は compatibility relay に落ち、
  `ABC040`
  も
  `ChernoffQualityFinal`
  直参照の shell に整理できた。
  つまり
  serial tail
  の最終三本も
  「番号 file が owner」
  ではなく
  「番号 file は relay / shell」
  という形に寄せられる。
- 同じ方針は
  final theorem file
  にも適用できる。
  今回は
  `ABC032`
  の
  `K_eps` / `abc_main_axiom` / `abc_main`
  を
  `ABCMainTheorem`
  へ昇格させた。
  これにより
  「番号 file に最後の大域定理が残る」
  状態から、
  `Main`
  が識別子付き final theorem owner を import する
  形へ一歩寄せられた。
- さらに
  final theorem の一段下にある
  eventual / adjacent-quality 層も、
  theorem-named utility
  に昇格できる。
  今回は
  `ABC031`
  の
  `adjacent_quality_le_density_one`
  と
  `adjacent_quality_le_ae_alt`
  を
  `AdjacentQuality`
  に移した。
  これにより
  `ABC032 -> ABC031`
  の serial edge も、
  少なくとも owner 観点では
  `ABCMainTheorem`
  から外せることが確認できた。
- adjacent branch のさらに下にある
  tail / Chernoff budget 層も、
  thematic owner
  として切り出せる。
  今回は
  `ABC030`
  の
  `union_bound_chernoff_log_rad`
  /
  `EventuallyChernoffBudgetAdjacentHypothesis`
  /
  `twoTail_log_bound_adjacent_density_one`
  などを
  `AdjacentTailDensity`
  に移した。
  その結果、
  adjacent branch は
  `ABC029`
  helper 層
  ->
  `AdjacentTailDensity`
  ->
  `AdjacentQuality`
  ->
  `ABCMainTheorem`
  という
  lower utility owner
  ->
  eventual-quality owner
  ->
  global final theorem owner
  の三段構造へ近づいた。
- この
  `ABC029`
  helper 層
  自体も、
  constants / dyadic partition / block-sum の thematic owner
  として昇格できる。
  今回は
  `ABC029`
  を
  `ChernoffDyadic`
  に持ち上げた。
  これで adjacent branch は
  `ChernoffDyadic`
  ->
  `AdjacentTailDensity`
  ->
  `AdjacentQuality`
  ->
  `ABCMainTheorem`
  と読み直せる。
  したがって
  「lower utility owner
  ->
  branch-local theorem owner
  ->
  global final theorem owner」
  の帯構造は、
  adjacent branch でも
  番号 file
  を介さずに記述できる。
- 同じ lower Chernoff 帯の一段下も、
  さらに thematic owner に分割できる。
  今回は
  `ABC028`
  を
  `ChernoffMgf`
  に持ち上げ、
  `mgf_padic_excess_bound_pbase`
  /
  `mgf_padic_excess_bound_two`
  /
  `mgf_padic_excess_bound_le_C`
  /
  `chernoff_single_prime`
  を owner 側へ移した。
  これで adjacent / Chernoff lower branch は
  `ChernoffMgf`
  ->
  `ChernoffDyadic`
  ->
  `AdjacentTailDensity`
  ->
  `AdjacentQuality`
  ->
  `ABCMainTheorem`
  と読める。
- さらに
  `ABC027`
  も
  heavy-prime budget 専用の thematic owner
  として切り出せた。
  今回の
  `HeavyPrimeBudget`
  は
  `AdjacentTailDensity`
  にだけ刺さる local utility だが、
  それでも
  relay 経由の hidden import
  より
  direct owner import
  を優先する、
  という切断パターンが有効だと確認できた。
  この型は
  「branch 全体の共通 kernel」
  でなくても
  「branch 内の局所 budget helper」
  を名前付き owner に上げられることを示している。
- 同じ adjacent branch のさらに下段では、
  heavy-prime の選別集合と witness 構成も
  thematic owner
  に分離できる。
  今回は
  `ABC026`
  を
  `HeavyPrimeSelection`
  に持ち上げた。
  これにより branch は
  `HeavyPrimeSelection`
  ->
  `HeavyPrimeBudget`
  ->
  `ChernoffMgf`
  ->
  `ChernoffDyadic`
  ->
  `AdjacentTailDensity`
  ->
  `AdjacentQuality`
  ->
  `ABCMainTheorem`
  と読める。
  したがって adjacent branch は、
  number 連番ではなく
  `selection / budget / mgf / dyadic / tail / quality / main`
  という役割分解で追跡する方が自然だと確認できた。
- `ABC025`
  のように file 全体が
  ほぼ一つの namespace owner
  になっている場合は、
  小さく裂くより先に
  namespace 名を反映した named owner
  に丸ごと昇格させるのが自然だった。
  今回は
  `ABC025`
  を
  `PadicTelescoping`
  に持ち上げた。
  これは
  `thin base + thematic band`
  の別パターンで、
  「局所 helper 群を複数 owner に砕く」
  前に
  「既存 namespace そのものを relay から救い出す」
  という first cut が有効だと示している。
- `ABC024`
  のように downstream code import が
  すでに消えている file でも、
  relay 化して owner 名を与える価値がある。
  今回は
  `ChernoffMgfLayercake`
  へ昇格させることで、
  `ABC022`
  の layer-cake primitive 群の上に乗る
  alternative MGF proof
  という役割を番号なしで追えるようにした。
  これは chain-cut というより
  archive / ownership cleanup
  だが、
  最終的に
  `ABC0*.lean`
  を削除していくための前提整備として必要な型である。
- `ABC022`
  のように branch 上流の helper 束を持つ file は、
  branch-specific theorem 名より
  technique 名で owner を付けるのが自然だった。
  今回は
  `LayerCakeBasic`
  として昇格させたことで、
  `rpow_layer_cake`
  とその周辺補題が
  `ABC019`
  の exp-layer-cake 層と
  `ChernoffMgfLayercake` / `ChernoffSinglePrime`
  の間にある
  reusable primitive band
  だと追えるようになった。
  これは
  `thin base + thematic band`
  の典型例で、
  上流 helper を先に番号なし化すると
  下流 theorem owner 側も relay import を減らしやすい。
- `ABC019`
  のように
  tail bridge と finite Chernoff helper が
  同居している file では、
  無理に theorem ごとへ細断せず、
  まず
  `TailAnalyticBasic`
  のような mixed basic band
  に持ち上げる first cut も有効だった。
  今回は
  `TailBound`
  / `quality_le_of_pi_tail_general`
  / `log_twoTail_le_excess_sum`
  と
  `markov_card_bound`
  / `exp_layer_cake`
  が同居する owner として整理し、
  downstream では
  `ChernoffMgf`
  と
  `ABC020`
  の relay 依存だけ先に落とした。
  これは
  「完全分解の前に mixed helper band として救出する」
  型で、
  後続サイクルで
  `TailSquareBridge` と
  `FiniteChernoffBasic`
  へ再分割する余地も残す。
- mixed helper band を一度 rescue した後で、
  live consumer の import を見ながら
  second cut を入れる型も有効だった。
  今回
  `TailAnalyticBasic`
  を
  `TailSquareBridge`
  と
  `FiniteChernoffBasic`
  に割ったところ、
  `ChernoffMgf`
  と
  `ABC020`
  の direct consumer だけでなく、
  `LayerCakeBasic`
  に hidden import が残っていることも露出した。
  したがって
  mixed band の分割では
  「owner の再配置」
  と
  「露出した transitive import の direct 化」
  を
  1 サイクルでまとめて処理するのが実践的である。
- live chain で未使用になっている numbered file も、
  先に named owner へ昇格して relay 化しておく価値がある。
  今回の
  `ABC021 -> JansonRoadmap`
  はその型で、
  `LayerCakeBasic`
  から
  `ABC021`
  import を削ったことで
  main spine から切り離された Janson branch を
  番号なし owner として保存できた。
  ただし、
  この cleanup によって別 branch の
  `ChernoffQualityBridge`
  で
  `TailSquareBridge`
  hidden import が露出したため、
  dead branch 救出でも
  `Main`
  build を最後まで通して
  transitive 依存の崩れを確認する必要がある。
- named owner 化のあとも、
  直後に relay を踏んでいる import が残ることがある。
  今回の
  `JansonRoadmap`
  では
  `ABC020`
  relay を経由していたが、
  実際に必要なのは
  `ABC008`
  側の Janson 基本定義だった。
  この型では
  「owner 昇格の次サイクルで、
  relay 経由 import を最小の上流へ直接寄せる」
  ことで、
  numbered chain をもう一段短くできる。
- `ABC008`
  のように
  branch 基底の巨大ファイルが
  既に thematic にまとまっている場合は、
  無理に細断せず
  whole-file promotion
  を先に入れるのが有効だった。
  今回は
  `JansonBasic`
  として丸ごと昇格させ、
  `ABC009`
  と
  `JansonRoadmap`
  を direct import に寄せた。
  これは
  「branch base を named owner で固定してから、
  下流を順に relay 離れさせる」
  型として再利用できる。
