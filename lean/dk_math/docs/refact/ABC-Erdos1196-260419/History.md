# History - リファクタリング作業履歴

cid: 69e46b72-e8bc-83e8-8b9c-152498680a64

- 時刻の打刻は `date` コマンドを使用して時間(時分秒)まで正確に行うこと。
- 新規履歴は **ファイル末尾** に追加すること。

## History Log

Archive

過去ログは、以下にアーカイブしてあります。

- [History-001.md](./History-001.md)

## Note

タイムスタンプの打刻は `date` コマンドを使用して、実際の日時を正確に記録してください。例: `date "+%Y/%m/%d %H:%M JST"` など。

※コミット時間がより正確であり、異なる場合は、コミット時間を優先とする。

## Template

### 日時: `タイムスタンプ date コマンドを使用して年月日時分まで` JST (作業概要の見出し)

1. 目的:
   - （内容）
2. 実施:
   - （内容）
3. 結論:
   - （内容）
4. 検証:
   - （内容）
5. 失敗事例:
   - （内容）
6. 次の課題:
   - （内容）

## 2026/04/24 10:45 JST

1. 実施:
   - `ABC018`
     を
     `HeavyPrimeCounting`
     に昇格した。
   - `HeavyPrimeCounting.lean`
     を新設し、
     per-prime threshold counting と
     heavy-prime union-bound 本体を移した。
   - `ABC018.lean`
     自体は
     `import DkMath.ABC.HeavyPrimeCounting`
     だけを持つ compatibility relay に縮小した。
2. moved 内容:
   - public:
     `count_n_with_high_vp_bound`,
     `heavy_primes_affect_sublinear_n`
   - private helper:
     `count_multiples_le_ceil`,
     `count_shifted_multiples_le_ceil`
3. downstream 調整:
   - `AdjacentTailDensity.lean`
     は
     `heavy_primes_affect_sublinear_n`
     を直接参照しているため、
     hidden dependency を避ける目的で
     `HeavyPrimeCounting`
     direct import を追加した。
   - `FiniteChernoffBasic.lean`
     は
     `ABC018`
     relay ではなく
     `HeavyPrimeCounting`
     の direct import に差し替えた。
4. `SquareTailBasic` 再分割の再評価:
   - 今回も分割は見送った。
   - 理由:
     `ABC018+`
     側では
     `BorelCantelliDensity`
     と
     `HeavyPrimeCounting`
     が独立 owner として立ち始めており、
     先に relay 縮小を進めたほうが
     downstream の import 安定性を測りやすいため。
   - したがって
     `SquareTailBasic`
     の decomposition / adjacent wrapper 分離は
     もう少し後段で再評価する。
5. 結論:
   - counting branch は
     `BorelCantelliDensity`
     の次段で
     `HeavyPrimeCounting`
     として独立に読めるようになった。
   - また
     `FiniteChernoffBasic`
     に残っていた
     relay 慣性 import を 1 本除去できた。
6. 追跡文書:
   - changed:
     `refact-changed-001.md`
     に
     `ABC018 -> HeavyPrimeCounting`
     と
     `AdjacentTailDensity`
     の direct import 化、
     `FiniteChernoffBasic`
     の direct import 化、
     ならびに
     `SquareTailBasic`
     再分割 defer を追記した。
   - pattern:
     `chain-cut-patterns-001.md`
     に
     counting branch の owner 分離と
     不要 import 削除パターンを追記した。
   - relay:
     `check-relay-lean.md`
     に
     `ABC018 -> HeavyPrimeCounting`
     を追加した。
7. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.HeavyPrimeCounting`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC018`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.FiniteChernoffBasic`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.AdjacentTailDensity`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上をこの順で確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知警告:
     `ABC038Bridge.lean`
     の axioms note
8. 次の課題:
   - `ABC019`
     以降で
     `HeavyPrimeCounting`
     relay を介さずに済む箇所をさらに削る。
   - `SquareTailBasic`
     の再分割は、
     counting / density / quality の owner 面が
     もう一段整理された時点で再評価する。

## 2026/04/24 10:56 JST

1. 実施:
   - `ABC019+`
     側で残っていた
     `ABC018`
     relay 依存を追加で削減した。
   - 対象は
     `TailSquareBridge.lean`
     で、
     `import DkMath.ABC.ABC018`
     を
     `import DkMath.ABC.HeavyPrimeCounting`
     に差し替えた。
2. 判断:
   - 現時点で
     `ABC018`
     relay を明示的に import していた
     `ABC019+`
     側の consumer は
     `TailSquareBridge`
     が最後だった。
   - したがって
     compatibility relay
     `ABC018.lean`
     は、
     いまは後方互換のためだけに残る状態になった。
3. `SquareTailBasic` 再分割の再評価:
   - 今回も見送った。
   - 理由:
     counting / density / quality の owner 面は
     `HeavyPrimeCounting`,
     `BorelCantelliDensity`,
     `AdjacentQuality`
     系へ順に分離できている一方、
     `SquareTailBasic`
     の consumer 群はまだ
     `TailSquareBridge`,
     `AdjacentTailDensity`,
     `AdjacentQuality`,
     `ABC038Bridge`
     にまたがって共有が残っているため。
   - よって分割より先に、
     owner direct import 化の残りを削る方を優先する。
4. 追跡文書:
   - changed:
     `refact-changed-001.md`
     に
     `TailSquareBridge`
     の
     `ABC018 -> HeavyPrimeCounting`
     差し替えを追記した。
   - pattern:
     `chain-cut-patterns-001.md`
     に
     downstream bridge file の relay import を
     direct import に差し替えるパターンを追記した。
5. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.TailSquareBridge`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.AdjacentTailDensity`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上をこの順で確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知警告:
     `ABC038Bridge.lean`
     の axioms note
6. 次の課題:
   - `ABC019+`
     側で
     `ABC017`
     / `ABC018`
     以外の relay import が
     direct owner import に置換できる箇所を順次洗う。
   - `SquareTailBasic`
     の再分割は、
     direct import 化の残りがさらに減った段階で再評価する。

## 2026/04/24 11:00 JST

1. 実施:
   - anchor shell
     `ABC090`
     を参照していた consumer を
     最小環境 import へ戻した。
   - `Main.lean`
     の
     `import DkMath.ABC.ABC090`
     を
     `import DkMath.ABC.Basic`
     に差し替えた。
   - `ABCError.lean`
     も同様に
     `ABC090`
     ではなく
     `Basic`
     を直接 import する形へ変更した。
2. 判断:
   - `ABC090`
     自体は
     すでに
     `Basic`
     だけを import する空 shell であり、
     下流がこれを経由する意味は薄い。
   - よって
     owner 化というより
     anchor consumer cleanup
     として扱うのが自然だった。
3. `SquareTailBasic` 再分割の再評価:
   - 今回も見送った。
   - 理由:
     counting / density / quality の owner 面整理は進んでいるが、
     `SquareTailBasic`
     の consumer 群は依然として
     bridge / density / quality
     の複数枝で共有されているため。
   - 先に
     numbered shell / relay import
     の cleanup を進める。
4. 追跡文書:
   - changed:
     `refact-changed-001.md`
     に
     `Main`
     / `ABCError`
     の
     `ABC090 -> Basic`
     差し替えを追記した。
   - pattern:
     `chain-cut-patterns-001.md`
     に
     anchor shell consumer を
     最小環境 import へ戻すパターンを追記した。
5. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABCError`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上をこの順で確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知警告:
     `ABC038Bridge.lean`
     の axioms note
6. 次の課題:
   - `ABC019+`
     側で残る
     numbered shell / relay import をさらに洗う。
   - `SquareTailBasic`
     の再分割は、
     direct import cleanup がもう少し進んだ段階で再評価する。

## 2026/04/24 11:03 JST

1. 実施:
   - research / scratch file でも
     relay import を owner 直参照へ戻した。
   - 対象は
     `ABC#Research.lean`
     で、
     `import DkMath.ABC.ABC036`
     を
     `import DkMath.ABC.ChernoffDensity`
     に差し替えた。
2. 判断:
   - `ABC#Research`
     で実際に使っていた numbered 系識別子はなく、
     必要なのは
     `Bad_ε`
     をはじめとする
     `ChernoffDensity`
     owner の記号だった。
   - したがって
     ここも relay cleanup の一環として扱える。
3. `SquareTailBasic` 再分割の再評価:
   - 今回も見送った。
   - 理由:
     まだ優先順位は
     numbered shell / relay import
     の cleanup 側にあるため。
4. 追跡文書:
   - changed:
     `refact-changed-001.md`
     に
     `ABC#Research`
     の
     `ABC036 -> ChernoffDensity`
     差し替えを追記した。
   - pattern:
     `chain-cut-patterns-001.md`
     に
     research / scratch file
     でも relay ではなく owner を直接引くパターンを追記した。
5. 検証:
   - `lake env lean DkMath/ABC/ABC#Research.lean`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上をこの順で確認済み。
   - 既知警告:
     `ABC#Research.lean`
     の `sorry`
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知警告:
     `ABC038Bridge.lean`
     の axioms note
6. 次の課題:
   - `ABC019+`
     側で残る
     numbered shell / relay import をさらに洗う。
   - `SquareTailBasic`
     の再分割は、
     direct import cleanup がもう少し進んだ段階で再評価する。

## 2026/04/24 11:40 JST

1. 実施:
   - 前段 chain の起点
     `ABC001`
     を
     `AdjacentDiagonalBasic`
     に昇格した。
   - `AdjacentDiagonalBasic.lean`
     を新設し、
     `ABC001.lean`
     にあった adjacent / diagonal / slice-radical helper 群を移した。
   - `ABC001.lean`
     自体は
     `import DkMath.ABC.AdjacentDiagonalBasic`
     だけを持つ compatibility relay に縮小した。
2. moved 内容:
   - adjacent / diagonal:
     `Adj`,
     `adjBadCount`,
     `diagBadCount`,
     `eventually_diagBadCount_oX`,
     `Keystone_bridge_quality_adjacent_imp`
   - slice / radical counting:
     `T_zero_card_le_one`,
     `Tr_card_le_div_plus_one`,
     `sliceBadCount_le_sum_div_plus_one`,
     `eventually_most_slices_light`
   - pair predicate / quality:
     `BadPair`,
     `quality`
3. downstream 調整:
   - `ABC002.lean`
     は
     `ABC001`
     relay 経由ではなく
     `AdjacentDiagonalBasic`
     の direct import に変更した。
4. 判断:
   - `ABC001`
     は責務が広いが、
     ここで細分化すると
     `ABC002`
     以降の検証範囲が広がる。
   - まず whole-file promotion により
     chain 起点を名前付き owner に固定し、
     後続で
     adjacent / diagonal / slice-radical
     の再分割価値を判断する。
5. 追跡文書:
   - relay:
     `check-relay-lean.md`
     に
     `ABC001 -> AdjacentDiagonalBasic`
     を追加した。
   - changed:
     `refact-changed-001.md`
     に
     `ABC001`
     whole-file promotion と
     `ABC002`
     の direct import 化を追記した。
   - pattern:
     `chain-cut-patterns-001.md`
     に
     前段 chain 起点を named owner 化する判断を追記した。
6. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.AdjacentDiagonalBasic`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC001`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC002`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上をこの順で確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知警告:
     `ABC038Bridge.lean`
     の axioms note
7. 次の課題:
   - `ABC002`
     の adjacent bad density layer を named owner 化する。
   - `AdjacentDiagonalBasic`
     の細分化は、
     `ABC002`
     以降の owner 面が立ってから再評価する。

## 2026/04/24 12:22 JST

1. 実施:
   - 前段 adjacent density 層
     `ABC002`
     を
     `AdjacentBadDensity`
     に昇格した。
   - `AdjacentBadDensity.lean`
     を新設し、
     `ABC002.lean`
     にあった adjacent bad density / quality density helper 群を移した。
   - `ABC002.lean`
     自体は
     `import DkMath.ABC.AdjacentBadDensity`
     だけを持つ compatibility relay に縮小した。
2. moved 内容:
   - bad count bridge:
     `adjBadCount_le_diag`,
     `tendsto_adj_bad_fraction_zero`
   - finite-prefix / eventual helper:
     `eventually_forall_on_Icc_of_eventually`,
     `prefix_over_X_tendsto_zero`
   - quality density:
     `adj_quality_density_one_no_equiv`,
     `adj_quality_density_one`
3. downstream 調整:
   - `ABC003.lean`
     は
     `ABC002`
     relay 経由ではなく
     `AdjacentBadDensity`
     の direct import に変更した。
4. 判断:
   - `ABC002`
     は
     adjacent bad count density zero
     から
     adjacent quality density one
     へ渡す一枚の層としてまとまっている。
   - ここでは補題単位への再分割より、
     前段 chain の
     `ABC001 -> ABC002 -> ABC003`
     を名前付き owner import に置換することを優先した。
5. 追跡文書:
   - relay:
     `check-relay-lean.md`
     に
     `ABC002 -> AdjacentBadDensity`
     を追加した。
   - changed:
     `refact-changed-001.md`
     に
     `ABC002`
     whole-file promotion と
     `ABC003`
     の direct import 化を追記した。
   - pattern:
     `chain-cut-patterns-001.md`
     に
     adjacent density layer
     の named owner 化を追記した。
6. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.AdjacentBadDensity`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC002`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC003`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上をこの順で確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知警告:
     `ABC038Bridge.lean`
     の axioms note
7. 次の課題:
   - `ABC003`
     の dyadic scaffold / middle-band combinatorial shell を named owner 化する。
   - `ABC004+`
     側で
     `ABC003`
     relay を介さずに済む direct import へ切る。

## 2026/04/24 12:38 JST

1. 実施:
   - 前段
     `ABC003`
     を
     `MiddleDyadicScaffold`
     と
     `AdjKBasic`
     に分割昇格した。
   - `ABC003.lean`
     自体は両 owner を import する compatibility relay に縮小した。
2. moved 内容:
   - `MiddleDyadicScaffold.lean`:
     `MidIdx`,
     `MidBlock`,
     `MidIdx_subset_blocks`,
     `MidBlock_pairwise_disjoint`,
     `BadCountOn`,
     `BadCountOn_bind_le`,
     `BadCountOn_mono`,
     `BlockBound`,
     `geom_sum_pow_two_le`
   - `AdjKBasic.lean`:
     `AdjK_of_coprime`,
     `AdjK`,
     `AdjK'`,
     `Bad_adjK_decidable`,
     `Bad_adjK_pred`,
     `Bad_adjK_pred_general`,
     `rad_ge_two_of_two_le`,
     `eventually_log_rad_pos_adjK`
3. downstream 調整:
   - `ABC004.lean`
     は
     `ABC003`
     relay 経由ではなく
     `AdjKBasic`
     を direct import する形に変更した。
   - `ABC005.lean`
     は
     `MiddleDyadicScaffold`
     を direct import する形にした。
     `ABC004`
     への import は、
     `ABC007`
     までの既存 chain が
     `adjKBadCount`
     系をまだ
     `ABC004`
     から受け取っているため今回は残した。
4. 判断:
   - `ABC003`
     は whole-file promotion では owner 名が曖昧になる。
   - dyadic middle scaffold と k-diagonal / AdjK basic は downstream が分かれているため、
     初回から二分割した方が chain-cut の追跡が明確になる。
5. 追跡文書:
   - relay:
     `check-relay-lean.md`
     に
     `ABC003 -> MiddleDyadicScaffold, AdjKBasic`
     を追加した。
   - changed:
     `refact-changed-001.md`
     に
     `ABC003`
     split promotion と
     `ABC004` / `ABC005`
     の direct import 化を追記した。
   - pattern:
     `chain-cut-patterns-001.md`
     に
     `ABC003`
     は二分割 owner が自然だったことを追記した。
6. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleDyadicScaffold`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.AdjKBasic`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC003`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC004`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC005`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上をこの順で確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知警告:
     `ABC038Bridge.lean`
     の axioms note
7. 次の課題:
   - `ABC004`
     の
     `adjKBadCount` / residue inclusion / finite union density
     層を named owner 化する。
   - `ABC005+`
     が
     `ABC004`
     relay を介して受けている
     `adjKBadCount`
     系を direct owner import へ切る。

## 2026/04/24 12:48 JST

1. 実施:
   - `ABC004`
     を
     `AdjKBadDensity`
     に昇格した。
   - `ABC004.lean`
     自体は
     `import DkMath.ABC.AdjKBadDensity`
     だけを持つ compatibility relay に縮小した。
2. moved 内容:
   - k-diagonal bad count:
     `eventually_log_rad_pos_adjK_one`,
     `adjKBadCount`,
     `adjKBadCount_le_half_range`
   - residue inclusion:
     `adjK_image_subset_R_with_dec`,
     `adjK_image_subset_R_with_dec'`,
     `adjK_image_subset_R`
   - density transfer:
     `tendsto_adjK_bad_fraction_zero`,
     `finset_sum_tendsto_zero`,
     `union_finite_density_zero`,
     `gridBadCount`
3. downstream 調整:
   - `ABC005.lean`
     から
     `ABC004`
     import を削除した。
     `ABC005`
     は
     `MiddleDyadicScaffold`
     のみで build 可能だった。
   - `ABC007.lean`
     は
     `adjKBadCount`
     unfold helper を持つため
     `AdjKBadDensity`
     を direct import する形に変更した。
   - `JansonBasic.lean`
     は
     `gridBadCount`
     を使うため
     `AdjKBadDensity`
     を direct import する形に変更した。
4. 判断:
   - `ABC004`
     は
     `AdjK`
     bad counting から finite-union density までの一枚の owner としてまとまっている。
   - `ABC005`
     には不要な numbered predecessor import が残っていたため、
     dyadic 側の import だけに縮小した。
5. 追跡文書:
   - relay:
     `check-relay-lean.md`
     に
     `ABC004 -> AdjKBadDensity`
     を追加した。
   - changed:
     `refact-changed-001.md`
     に
     `ABC004`
     promotion と downstream import cut を追記した。
   - pattern:
     `chain-cut-patterns-001.md`
     に
     `ABC004`
     owner 化と
     `ABC005` / `ABC007` / `JansonBasic`
     の import 判断を追記した。
6. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.AdjKBadDensity`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC004`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC005`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC006`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC007`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.JansonBasic`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上をこの順で確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知警告:
     `ABC038Bridge.lean`
     の axioms note
7. 次の課題:
   - `ABC005`
     の dyadic tail bound / block aggregation 層を named owner 化する。
   - `ABC006`
     から
     `ABC005`
     relay を介さずに済む direct import へ切る。

## 2026/04/24 18:19 JST

1. 実施:
   - `ABC005`
     を
     `MiddleDyadicTailBound`
     に昇格した。
   - `ABC005.lean`
     自体は
     `import DkMath.ABC.MiddleDyadicTailBound`
     だけを持つ compatibility relay に縮小した。
2. moved 内容:
   - dyadic tail:
     `dyadic_tail_bound`
   - finite head absorption:
     `head_absorb'`
3. downstream 調整:
   - `ABC006.lean`
     は
     `ABC005`
     relay 経由ではなく
     `MiddleDyadicTailBound`
     の direct import に変更した。
4. 判断:
   - `ABC005`
     は
     `MiddleDyadicScaffold`
     上の tail bound / head absorption 層として責務が明確である。
   - `ABC006`
     の合成定理群は
     `dyadic_tail_bound`
     を直接参照しているため、
     owner import に切るのが自然だった。
5. 追跡文書:
   - relay:
     `check-relay-lean.md`
     に
     `ABC005 -> MiddleDyadicTailBound`
     を追加した。
   - changed:
     `refact-changed-001.md`
     に
     `ABC005`
     promotion と
     `ABC006`
     の direct import 化を追記した。
   - pattern:
     `chain-cut-patterns-001.md`
     に
     middle dyadic tail bound
     の owner 化を追記した。
6. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleDyadicTailBound`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC005`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC006`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC007`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.JansonBasic`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上をこの順で確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知警告:
     `ABC038Bridge.lean`
     の axioms note
7. 次の課題:
   - `ABC006`
     の
     `tail_geom_bound` / `dyadic_compose`
     層を named owner 化する。
   - `ABC007`
     から
     `ABC006`
     relay を介さずに済む direct import へ切る。

## 2026/04/24 21:06 JST

1. 実施:
   - `ABC006`
     を
     `MiddleDyadicCompose`
     に昇格した。
   - `ABC006.lean`
     自体は
     `import DkMath.ABC.MiddleDyadicCompose`
     だけを持つ compatibility relay に縮小した。
2. moved 内容:
   - head/tail helper:
     `pow_two_mono`,
     `one_le_X_pow`,
     `MidBlock_card_le_pow_head`,
     `head_absorb`
   - dyadic composition:
     `tail_geom_bound'`,
     `tail_geom_bound`,
     `dyadic_compose`
3. downstream 調整:
   - `ABC007.lean`
     は
     `ABC006`
     relay 経由ではなく
     `MiddleDyadicScaffold`
     を direct import する形に変更した。
     実際に必要だったのは
     `BlockBound`,
     `BadCountOn`,
     `MidIdx`
     側だったため。
   - `MiddleJansonBridge.lean`
     は
     `head_absorb` / `tail_geom_bound`
     を直接使うため
     `MiddleDyadicCompose`
     を direct import する形に変更した。
4. 判断:
   - `ABC006`
     は
     `MiddleDyadicTailBound`
     を入力にして
     head/tail 分割を合成し、
     `dyadic_compose`
     に到達する owner としてまとまっている。
   - `ABC007`
     には compose 層そのものへの依存はなかったため、
     direct import はより浅い
     `MiddleDyadicScaffold`
     に留めた。
5. 追跡文書:
   - relay:
     `check-relay-lean.md`
     に
     `ABC006 -> MiddleDyadicCompose`
     を追加した。
   - changed:
     `refact-changed-001.md`
     に
     `ABC006`
     promotion と downstream import cut を追記した。
   - pattern:
     `chain-cut-patterns-001.md`
     に
     `ABC006`
     の owner 化と
     `ABC007` / `MiddleJansonBridge`
     の import 判断を追記した。
6. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleDyadicCompose`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC006`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC007`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleJansonBridge`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上をこの順で確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知警告:
     `ABC038Bridge.lean`
     の axioms note
7. 次の課題:
   - `ABC007`
     の
     `middleBandBlockBound` / middle-band exception skeleton
     層を named owner 化する。
   - `JansonBasic`
     から
     `ABC007`
     relay を介さずに済む direct import へ切る。

## 2026/04/25 00:31 JST

1. 実施:
   - `ABC007.lean`
     の middle-band exception / Janson-Suen skeleton / finite-uniform probability helper 群を
     `MiddleBandJansonSkeleton.lean`
     に whole-file promotion した。
   - `ABC007.lean`
     自体は
     `import DkMath.ABC.MiddleBandJansonSkeleton`
     だけを持つ compatibility relay に縮小した。
2. moved 内容:
   - adjacent-k bridge:
     `adjKBadCount_unfold`,
     `AdjK_proof`
   - middle-band exception API:
     `middleBandBlockBound`,
     `MiddleBand_exception_bound'_via_dyadic`,
     `MiddleBand_exception_bound'`
   - Janson/Suen skeleton:
     `Janson_downward_tail_skeleton`,
     `Suen_upper_tail_skeleton`
   - finite-uniform probability helper:
     `indicator`,
     `S_of`,
     `mu_of`,
     `prob_of`,
     `delta_of`,
     `mgf_bound_unit01`,
     `Prob.indR`,
     `Prob.hoeffding_downward_indep01`,
     `Prob.hoeffding_downward_indep01_indicator`
     など。
3. downstream 調整:
   - `JansonBasic.lean`
     を
     `ABC007`
     relay 経由ではなく
     `MiddleBandJansonSkeleton`
     direct import に変更した。
   - 実コード側の
     `import DkMath.ABC.ABC007`
     は解消した。
4. 判断:
   - `ABC007`
     は
     `middleBandBlockBound`
     だけでなく
     `S_of` / `Prob.indR`
     など
     `JansonBasic`
     が直接使う有限一様確率 helper も含んでいた。
   - そのため今回は partial extraction ではなく whole-file promotion にして、
     owner 名を
     `MiddleBandJansonSkeleton`
     とした。
5. 追跡文書:
   - relay:
     `check-relay-lean.md`
     に
     `ABC007 -> MiddleBandJansonSkeleton`
     を追加した。
   - changed:
     `refact-changed-001.md`
     に
     `ABC007`
     promotion と
     `JansonBasic`
     import cut を追記した。
   - pattern:
     `chain-cut-patterns-001.md`
     に
     `ABC007`
     の whole-file promotion 判断を追記した。
6. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleBandJansonSkeleton`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC007`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.JansonBasic`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleJansonBridge`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上をこの順で確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知警告:
     `ABC038Bridge.lean`
     の axioms note
7. 次の課題:
   - `ABC001` から `ABC007`
     までの前段 numbered relay 化は一通り完了。
   - 次は
     `ABC008`
     relay と
     `JansonBasic`
     の境界を見直し、
     Janson 系 owner の再分割候補を整理する。

## 2026/04/25 03:03 JST

1. 実施:
   - `ABC008`
     relay の実体である
     `JansonBasic.lean`
     の冒頭 finite-uniform wrapper 層を
     `JansonFiniteUniform.lean`
     に分離した。
   - `JansonBasic.lean`
     は
     `DkMath.ABC.JansonFiniteUniform`
     を import し、
     Janson model / PMF product / expectation helper owner として残した。
2. moved 内容:
   - `Block_Janson_downward_skeleton_indep`
   - `adjK_quality_density_one`
   - `tendsto_grid_bad_fraction_zero`
3. downstream 調整:
   - `JansonBasic.lean`
     の import を
     `MiddleBandJansonSkeleton` / `AdjKBadDensity`
     から
     `JansonFiniteUniform`
     へ変更した。
   - `ABC008.lean`
     は既に
     `JansonBasic`
     relay なので変更なし。
4. 判断:
   - `Block_Janson_downward_skeleton_indep`
     は
     `MiddleBandJansonSkeleton`
     の
     `S_of` / `Prob.indR` / `Prob.hoeffding_downward_indep01_indicator`
     だけを主に使う finite-uniform wrapper であり、
     `JansonModel` / `product_pmf`
     以降の PMF product 本体から分けられる。
   - adjacent density placeholders は
     `AdjKBadDensity`
     側の API を使うため、
     同じ finite-uniform 外側 owner に置いた。
5. 追跡文書:
   - relay:
     `check-relay-lean.md`
     の
     `ABC008`
     に
     `JansonFiniteUniform`
     を再分割先として追記した。
   - changed:
     `refact-changed-001.md`
     に
     `JansonBasic -> JansonFiniteUniform`
     分離を追記した。
   - pattern:
     `chain-cut-patterns-001.md`
     に
     `ABC008`
     relay 後の owner 内部再分割パターンを追記した。
6. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.JansonFiniteUniform`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.JansonBasic`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC008`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleJansonBridge`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上をこの順で確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知警告:
     `ABC038Bridge.lean`
     の axioms note
7. 次の課題:
   - `JansonBasic`
     に残る
     `JansonSetup` / `JansonModel` / `product_pmf`
     系を観察し、
     PMF product owner と abstract bound owner を分けられるか判断する。
   - `MiddleJansonBridge`
     が本当に必要とする Janson API を確認し、
     `JansonBasic`
     全体 import を狭められるか検討する。

## 2026/04/25 03:21 JST

1. 実施:
   - `JansonBasic.lean`
     に残っていた Janson model / PMF product / expectation helper 本体を
     `JansonPMFProduct.lean`
     に whole-file promotion した。
   - `JansonBasic.lean`
     自体は
     `import DkMath.ABC.JansonPMFProduct`
     だけを持つ compatibility relay に縮小した。
2. moved 内容:
   - PMF expectation helpers:
     `PMF.expect_ennreal`,
     `PMF.expect`,
     `PMF.expect_bind`,
     `PMF.expect_const_mul`
   - Janson abstract/model layer:
     `JansonSetup`,
     `JansonModel`,
     `JansonModel'`,
     `indicatorA`,
     `mu`,
     `dbar`
   - PMF product layer:
     `bernoulli_pmf`,
     `product_pmf`,
     `product_pmf_on`,
     `expect_product_pmf_on`
   - downstream-facing lemmas:
     `expect_indicator_prod'`,
     `expect_indicator_prod`,
     `expect_indicator_joint`,
     `bound_v2`
   - middle-band prototype:
     `MiddleBandParams`,
     `middle_band_bound_proto`
3. downstream 調整:
   - `MiddleJansonBridge.lean`
     を
     `JansonBasic`
     relay 経由ではなく
     `JansonPMFProduct`
     direct import に変更した。
   - `JansonRoadmap.lean`
     も
     `JansonPMFProduct`
     direct import に変更した。
4. 判断:
   - `MiddleJansonBridge`
     は
     `ABC.Janson.JansonModel`,
     `ABC.Janson.product_pmf`,
     `ABC.Janson.expect_indicator_prod'`,
     `ABC.Janson.mu`,
     `ABC.Janson.dbar`
     を直接使っているため、
     PMF product owner への direct import が自然。
   - `JansonBasic`
     は外部互換名として残し、
     `ABC008`
     relay からの compatibility chain は維持した。
5. 追跡文書:
   - relay:
     `check-relay-lean.md`
     の
     `ABC008`
     に
     `JansonPMFProduct`
     を再分割先として追記した。
   - changed:
     `refact-changed-001.md`
     に
     `JansonBasic -> JansonPMFProduct`
     promotion と downstream import cut を追記した。
   - pattern:
     `chain-cut-patterns-001.md`
     に
     `JansonBasic`
     relay 化と
     `JansonPMFProduct`
     direct import パターンを追記した。
6. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.JansonPMFProduct`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.JansonBasic`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleJansonBridge`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.JansonRoadmap`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC008`
   - 以上をこの順で確認済み。
   - 既知警告:
     `JansonRoadmap.lean`
     の roadmap `sorry`
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知警告:
     `ABC038Bridge.lean`
     の axioms note
7. 次の課題:
   - `ABC008`
     relay chain は
     `ABC008 -> JansonBasic -> JansonPMFProduct`
     として互換維持された。
   - 次は
     `MiddleJansonBridge`
     内の
     JSProb / BlockJS / aggregation bridge を観察し、
     `ABC009`
     relay 周辺の owner 境界をさらに切れるか確認する。

## 2026/04/25 03:34 JST

1. 実施:
   - `MiddleJansonBridge.lean`
     から
     JSProb wrapper 層を
     `MiddleJSProb.lean`
     に分離した。
   - `MiddleJansonBridge.lean`
     は
     `JansonPMFProduct`
     direct import ではなく
     `MiddleJSProb`
     を import する形に変更した。
2. moved 内容:
   - `JSProb.Ibit`
   - `JSProb.Setup`
   - `JSProb.X`
   - `JSProb.jPr_joint`
   - `JSProb.jPr_zero`
   - `JSProb.jPr_joint_eq`
   - `JSProb.jPr_zero_nonneg`
   - `JSProb.jPr_joint_nonneg`
3. downstream 調整:
   - `ABC009.lean`
     は既に
     `MiddleJansonBridge`
     relay なので変更なし。
   - `MiddleBlockTail.lean`
     は
     `MiddleJansonBridge`
     経由のまま通ることを確認した。
4. 判断:
   - `JSProb`
     は
     `JansonPMFProduct`
     の
     `JansonModel`,
     `product_pmf`,
     `expect_indicator_prod'`,
     `PMF.expect_nonneg`
     を使って
     middle-band 用の実数確率 API を作る薄い wrapper である。
   - `MiddleJansonBridge`
     本体の
     `Middle`
     namespace は
     `Params`,
     `BlockJS`,
     `middle_band_sum_bound`,
     `middle_band_bound_top`
     など aggregation 側に寄るため、
     JSProb と分けるのが import 境界として自然。
5. 追跡文書:
   - relay:
     `check-relay-lean.md`
     の
     `ABC009`
     に
     `MiddleJSProb`
     を再分割先として追記した。
   - changed:
     `refact-changed-001.md`
     に
     `MiddleJansonBridge -> MiddleJSProb`
     分離を追記した。
   - pattern:
     `chain-cut-patterns-001.md`
     に
     `ABC009`
     relay target 内の JSProb 分離パターンを追記した。
6. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleJSProb`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleJansonBridge`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC009`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleBlockTail`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上をこの順で確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知警告:
     `ABC038Bridge.lean`
     の axioms note
7. 次の課題:
   - `MiddleJansonBridge`
     に残る
     `Middle`
     namespace の
     `Params` / `BlockJS` / `middle_band_sum_bound`
     / `middle_band_bound_top`
     を観察し、
     BlockJS owner と aggregation owner をさらに分ける価値があるか判断する。

## 2026/04/25 04:22 JST

1. 実施:
   - `MiddleJansonBridge.lean`
     から
     block-level Janson/Suen API を
     `MiddleBlockJS.lean`
     に分離した。
   - `MiddleJansonBridge.lean`
     は
     `middle_band_sum_bound`
     と
     `middle_band_bound_top`
     を持つ aggregation owner に縮小した。
   - `MiddleBlockTail.lean`
     は
     `MiddleJansonBridge`
     relay 経由ではなく、
     `MiddleBandJansonSkeleton`
     と
     `MiddleDyadicCompose`
     を direct import する形に変更した。
2. moved 内容:
   - Janson real-evaluation layer:
     `janson_mu`,
     `janson_mu_nonneg`,
     `janson_dbar`,
     `janson_dbar_nonneg`
   - block-cost / exponential layer:
     `janson_block_cost`,
     `janson_block_cost_le`,
     `janson_block_exp`,
     `janson_block_exp'`,
     `janson_block_exp_nonneg`,
     `janson_block_exp_nonneg'`,
     `janson_block_exp_mono_mu`,
     `janson_block_exp_mono_dbar`
   - bridge alignment:
     `mu_eq`,
     `dbar_eq`,
     `janson_bound_v2`
   - block API:
     `Params`,
     `BlockJS`,
     `buildBlockJS`,
     `block_bound_from_janson`
3. 判断:
   - `MiddleBlockJS`
     は
     `MiddleJSProb`
     と
     `MiddleDyadicCompose`
     を合流させ、
     PMF→実数確率 wrapper を
     block-level API に変換する owner とした。
   - `MiddleJansonBridge`
     は
     `RpowExtras.rpow_mul_nat`,
     `geom_sum_pow_two_le`,
     `head_absorb`,
     `tail_geom_bound`
     を使う aggregation 層として残すのが自然。
   - `MiddleBlockTail`
     は
     `middle_band_sum_bound`
     / `middle_band_bound_top`
     を使わず、
     `Prob.indR`
     と
     mid-block dyadic primitive を使うため、
     aggregation relay を経由させない方が依存境界が明確。
4. 追跡文書:
   - relay:
     `check-relay-lean.md`
     の
     `ABC009`
     に
     `MiddleBlockJS`
     を再分割先として追記した。
   - changed:
     `refact-changed-001.md`
     に
     `MiddleJansonBridge -> MiddleBlockJS`
     分離と
     `MiddleBlockTail`
     の direct import 化を追記した。
   - pattern:
     `chain-cut-patterns-001.md`
     に
     block-level owner 分離と
     downstream direct import 化の注意点を追記した。
5. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleBlockJS`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleJansonBridge`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleBlockTail`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC009`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC010`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上をこの順で確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知 info:
     `ABC038Bridge.lean`
     の axioms note
6. 失敗事例:
   - `MiddleBlockTail.lean`
     を
     `MiddleDyadicCompose`
     単独 import に差し替えたところ、
     `Prob.indR`,
     `chernoff_lower_tail`,
     `middleBandBlockBound`
     が見えなくなり build error になった。
   - 修正として
     `MiddleBandJansonSkeleton`
     を direct import に追加し、
     `MiddleBlockTail`
     の必要 owner を
     finite-uniform / probability primitive 側と
     dyadic compose 側に分けた。
7. 次の課題:
   - `ABC010`
     relay target の
     `MiddleBlockTail`
     は大きい owner なので、
     `Zmid` / `QuadMGF` / Chernoff wrapper / `GoodX`
     周辺を観察し、
     さらに named owner 化できる境界を探す。
   - `MiddleJansonBridge`
     は aggregation owner として残しつつ、
     consumer が本当に aggregation API を使う場合だけ
     direct import する方針にする。

## 2026/04/25 04:38 JST

1. 目的:
   - `ABC010`
     relay target の
     `MiddleBlockTail`
     から、
     `Zmid` / mid-block finite-sum 基礎層を分離する。
   - `MiddleBlockTail`
     を
     `QuadMGF` / Chernoff wrapper / tail absorption / `GoodX`
     側の owner に寄せる。
2. 実施:
   - 新設:
     `DkMath.ABC.MiddleZmidBasic`
   - `MiddleBlockTail.lean`
     から以下を移設した:
     `MidBlock_card_lower_when_2k_le_X`,
     `Prob.middleBandBlockBound_alt`,
     `Prob.mid_block_sum_ae_bounds`,
     `Prob.mid_block_sum_ae_bounds'`,
     `Prob.mid_block_sum_aestronglyMeasurable`,
     `Prob.mid_block_sum_integrable`,
     `Prob.Zmid`,
     `Prob.BadCountOnRV`,
     `Prob.integrable_exp_of_mid_block`,
     `Prob.BadCountOnRV_eq_Zmid`
   - `MiddleBlockTail.lean`
     は
     `import DkMath.ABC.MiddleZmidBasic`
     に差し替え、
     以降の
     `QuadMGF`,
     `QuadMGFPos`,
     `SubGammaParam`,
     `QuadMGFPosUpTo`,
     `mgf_midblock_via_janson_pos`,
     Chernoff wrapper,
     tail absorption,
     `GoodX`
     周辺を保持した。
3. 判断:
   - `MiddleZmidBasic`
     は
     `MiddleBandJansonSkeleton`
     と
     `MiddleDyadicCompose`
     のみを直接 import し、
     `Prob.indR`
     finite-sum の可測性・可積分性と
     `Zmid`
     の owner として読むのが自然。
   - `MiddleBlockTail`
     は
     MGF witness から tail bound へ進む層であり、
     finite-sum の基礎補題を持たせない方が後続分割しやすい。
   - `ABC010.lean`
     relay target は引き続き
     `MiddleBlockTail`
     だが、
     その内部境界として
     `MiddleZmidBasic`
     を追跡可能にした。
4. 追跡文書:
   - `check-relay-lean.md`
     の
     `ABC010`
     に
     `MiddleZmidBasic`
     を再分割先として追記した。
   - `refact-changed-001.md`
     に
     `MiddleBlockTail -> MiddleZmidBasic`
     分離内容を追記した。
   - `chain-cut-patterns-001.md`
     に
     `Zmid` / finite mid-block sum 層の切り出しパターンを追記した。
5. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleZmidBasic`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleBlockTail`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC010`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleBlockIndependentTail`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上をこの順で確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知 info:
     `ABC038Bridge.lean`
     の axioms note
6. 次の課題:
   - `MiddleBlockTail`
     内の
     `QuadMGF` / `QuadMGFPos` / `SubGammaParam`
     と Chernoff wrapper の境界を観察し、
     MGF owner と tail absorption owner を分けられるか確認する。
   - `GoodX`
     / union absorption 側は、
     MGF wrapper 分離後に import 安定性を見て切り出し可否を判断する。

## 2026/04/25 11:55 JST

1. 目的:
   - `MiddleBlockTail`
     内の
     `QuadMGF` / `QuadMGFPos` / `SubGammaParam`
     と Chernoff wrapper の境界を観察し、
     MGF owner と tail absorption owner を分ける。
   - `GoodX`
     / union absorption 側は、
     MGF wrapper 分離後に残責務として保持する。
2. 実施:
   - 新設:
     `DkMath.ABC.MiddleBlockMGF`
   - `MiddleBlockTail.lean`
     から以下を移設した:
     `Prob.QuadMGF`,
     `Prob.QuadMGFPos`,
     `Prob.SubGammaParam`,
     `Prob.QuadMGFPosUpTo`,
     `Prob.quad_from_subgamma_upto`,
     `Prob.mgf_midblock_via_janson_pos`,
     `Prob.chernoff_upper_from_quad_mgf_pos`,
     `Prob.chernoff_from_quad_mgf`,
     `Prob.chernoff_upper_from_local_mgf_pos`,
     `Prob.chernoff_upper_from_quad_mgf_upto`,
     `Prob.mid_block_upper_hp_dep`,
     `Prob.chernoff_upper_from_quad_mgf_upto_linear`,
     `Prob.mid_block_upper_hp_dep_expCard`,
     `Prob.mid_block_upper_hp_dep_expCard_factor`,
     `Prob.mid_block_upper_hp_dep_expCard_exists`,
     `Prob.mid_block_upper_hp_dep_expCard_exists'`,
     `Prob.mid_block_upper_hp_dep_card`,
     `Prob.EZmid_eq_sum_probs`,
     `Prob.mgf_midblock_via_indep`,
     `Prob.mgf_midblock_via_indep_pos`,
     `Prob.mid_block_upper_hp_indep`,
     `Prob.mgf_midblock_via_janson`,
     `Prob.mid_block_chernoff_fixed`
   - private helper も
     `MiddleBlockMGF`
     内へ移した:
     `Prob.indR_measurable_each`,
     `Prob.indR_integrable_each`,
     `Prob.mgf_bound_centered_each`,
     `Prob.prod_mgf_bound_by_exp_card`
   - `MiddleBlockTail.lean`
     は
     `import DkMath.ABC.MiddleBlockMGF`
     に差し替え、
     `mid_block_chernoff_tail`
     以降の tail absorption / `midblockCstar` / `Kset` / `Emid` / `GoodX`
     側を保持した。
3. 判断:
   - `MiddleBlockMGF`
     は
     `MiddleZmidBasic`
     の
     `Zmid`
     と finite-sum integrability を使い、
     fixed-block MGF witness から fixed-block Chernoff bound までを担当する owner とした。
   - `MiddleBlockTail`
     は
     MGF wrapper ではなく、
     dyadic two-pow absorption,
     `midblockCstar`,
     `Kset` / `Emid` / `GoodX`
     union absorption を束ねる owner に縮小した。
   - `GoodX`
     周辺は
     `Emid`,
     `Kset`,
     `midblockCstar`,
     `midblock_union_absorb_dep`
     と相互参照が強いため、
     今回は切り出さず import 安定性を優先した。
4. 追跡文書:
   - `check-relay-lean.md`
     の
     `ABC010`
     に
     `MiddleBlockMGF`
     を再分割先として追記した。
   - `refact-changed-001.md`
     に
     `MiddleBlockTail -> MiddleBlockMGF`
     分離内容を追記した。
   - `chain-cut-patterns-001.md`
     に
     MGF owner と tail absorption owner の切り分けパターンを追記した。
5. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleBlockMGF`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleBlockTail`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC010`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleBlockIndependentTail`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上をこの順で確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知 info:
     `ABC038Bridge.lean`
     の axioms note
6. 次の課題:
   - `MiddleBlockTail`
     の残存本体を観察し、
     `Kset` / `Emid` / `GoodX`
     の定義層と
     `midblock_union_absorb_dep`
     以降の union absorption 証明層を分けられるか確認する。
   - `MiddleBlockIndependentTail`
     が
     `GoodX`
     / `Emid`
     を参照しているため、
     次回はこの downstream import も同時に確認する。

## 2026/04/25 13:07 JST

1. 目的:
   - `MiddleBlockTail`
     の残存本体から、
     `Kset` / `Emid` / `GoodX`
     の定義層と点ごと補題を分離する。
   - dependent union absorption と
     `GoodX`
     測度下界は、
     import 安定性を見ながら
     `MiddleBlockTail`
     に残す。
2. 実施:
   - 新設:
     `DkMath.ABC.MiddleBlockEvents`
   - `MiddleBlockTail.lean`
     から以下を移設した:
     `Prob.Kset`,
     `Prob.Emid`,
     `Prob.GoodX`,
     `Prob.goodX_compl_eq_union`,
     `Prob.goodX_pointwise`,
     `Prob.goodX_pointwise_qaddδ_card`,
     `Prob.goodX_sum_over_k_qaddδ_card`,
     `Prob.Kset_mono`,
     `Prob.GoodX_antitone`
   - `MiddleBlockTail.lean`
     は
     `import DkMath.ABC.MiddleBlockEvents`
     に差し替え、
     `midblockCstar`,
     `union_over_k_midblock_bound_dep`,
     `midblock_union_absorb_dep`,
     `midblock_union_absorb_dep_const`,
     `goodX_measure_ge_one_sub_midblockCstar`
     側を保持した。
3. 判断:
   - `MiddleBlockEvents`
     は
     `MiddleBlockMGF`
     の
     `Zmid`
     API を使う event definition owner とした。
   - `goodX_pointwise`
     や
     `Kset_mono`
     は union absorption ではなく、
     `Kset` / `Emid` / `GoodX`
     の定義から直接出る基本 API なので、
     event owner 側に置く方が downstream から参照しやすい。
   - `midblockCstar`
     と dependent union absorption は
     `summable_exp_neg_two_pow`,
     `mid_block_upper_hp_dep_expCard_factor`,
     Boole bound を束ねるため、
     今回は
     `MiddleBlockTail`
     に残すのが自然。
4. downstream 確認:
   - `TailRadicalBasic`
     は従来どおり
     `MiddleBlockTail`
     を import し、
     `summable_exp_neg_two_pow`
     と
     event API を参照できる。
   - `MiddleBlockIndependentTail`
     は
     `TailRadicalBasic`
     経由で
     `Kset` / `Emid` / `GoodX`
     を参照できることを build で確認した。
5. 追跡文書:
   - `check-relay-lean.md`
     の
     `ABC010`
     に
     `MiddleBlockEvents`
     を再分割先として追記した。
   - `refact-changed-001.md`
     に
     `MiddleBlockTail -> MiddleBlockEvents`
     分離内容を追記した。
   - `chain-cut-patterns-001.md`
     に
     event definition owner と tail absorption owner の切り分けパターンを追記した。
6. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleBlockEvents`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleBlockTail`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.TailRadicalBasic`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleBlockIndependentTail`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC010`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上をこの順で確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知 info:
     `ABC038Bridge.lean`
     の axioms note
7. 次の課題:
   - `MiddleBlockTail`
     の残りを、
     dyadic summability / dependent union absorption / scaffold tail theorem
     のどこで切るか再評価する。
   - `TailRadicalBasic`
     が
     `summable_exp_neg_two_pow`
     だけを必要としているなら、
     次回以降に dyadic summability owner を分けて
     `TailRadicalBasic -> MiddleBlockTail`
     の依存を薄くできるか確認する。

## 2026/04/25 16:11 JST

1. 目的:
   - `MiddleBlockTail`
     の残りから、
     dyadic two-power tail と
     `exp(-c * 2^k)`
     可和性を owner 化する。
   - `TailRadicalBasic`
     が
     `MiddleBlockTail`
     全体を import しなくてよいか確認する。
2. 実施:
   - 新設:
     `DkMath.ABC.MiddleBlockDyadicTail`
   - `MiddleBlockTail.lean`
     から以下を移設した:
     `Prob.mid_block_upper_hp_dep_twoPow_exists`,
     `Prob.mid_block_upper_hp_dep_twoPow_exists_of_2k_le_X`,
     `Prob.exp_neg_two_pow_ratio_le`,
     `Prob.exp_neg_two_pow_le_geom`,
     `Prob.summable_exp_neg_two_pow`,
     `Prob.midblock_tail_dep_dyadic`
   - `MiddleBlockTail.lean`
     は
     `import DkMath.ABC.MiddleBlockDyadicTail`
     に差し替え、
     independent scaffold tail,
     expectation wrapper,
     `midblockCstar`,
     dependent union absorption,
     `GoodX`
     測度下界を保持した。
   - `TailRadicalBasic.lean`
     は
     `MiddleBlockTail`
     ではなく
     `MiddleBlockDyadicTail`
     を direct import するよう変更した。
3. 判断:
   - `MiddleBlockDyadicTail`
     は
     `MiddleBlockEvents`
     を入口とし、
     `Zmid`
     / `Emid`
     と
     `SubGammaParam`
     には依存するが、
     `midblockCstar`
     や
     dependent union absorption には依存しない。
   - `TailRadicalBasic`
     が必要としているのは
     `summable_exp_neg_two_pow`
     と event API であり、
     `MiddleBlockTail`
     の上位 absorption 本体ではない。
     そのため
     `TailRadicalBasic -> MiddleBlockTail`
     の依存は切断できた。
   - `midblockCstar`
     は可和性と dependent union bound を束ねる上位定数なので、
     今回は
     `MiddleBlockTail`
     に残す。
4. 追跡文書:
   - `check-relay-lean.md`
     の
     `ABC010`
     に
     `MiddleBlockDyadicTail`
     を再分割先として追記した。
   - `refact-changed-001.md`
     に
     `MiddleBlockTail -> MiddleBlockDyadicTail`
     分離内容を追記した。
   - `chain-cut-patterns-001.md`
     に
     dyadic tail owner と independent tail basic owner の import 切断パターンを追記した。
5. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleBlockDyadicTail`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleBlockTail DkMath.ABC.TailRadicalBasic DkMath.ABC.MiddleBlockIndependentTail DkMath.ABC.ABC010 DkMath.ABC.Main`
   - 以上を確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知 info:
     `ABC038Bridge.lean`
     の axioms note
6. 次の課題:
   - `MiddleBlockTail`
     に残る
     independent scaffold tail,
     `EZmid_expect_le_card_smul_q`,
     dependent union absorption,
     `goodX_measure_ge_one_sub_midblockCstar`
     を見直す。
   - dependent union absorption を
     `MiddleBlockDepAbsorption`
     のような owner に分ける価値があるか、
     downstream import を見て判断する。

## 2026/04/25 21:36 JST

1. 目的:
   - `MiddleBlockTail`
     に残る dependent union absorption を named owner 化する。
   - `MiddleBlockTail`
     を
     `ABC010`
     relay entry として維持しつつ、
     実体を scaffold / independent wrapper 層へ縮小する。
2. 実施:
   - 新設:
     `DkMath.ABC.MiddleBlockDepAbsorption`
   - `MiddleBlockTail.lean`
     から以下を移設した:
     `Prob.midblockCstar`,
     `Prob.midblockCstar_nonneg`,
     `Prob.union_over_k_midblock_bound_dep`,
     `Prob.union_over_k_midblock_bound_dep'`,
     `Prob.midblock_union_absorb_dep`,
     `Prob.midblock_union_absorb_dep_const`,
     `Prob.goodX_measure_ge_one_sub_midblockCstar`
   - `MiddleBlockDepAbsorption.lean`
     は
     `MiddleBlockDyadicTail`
     を import し、
     `MiddleBlockTail`
     の
     `mid_block_chernoff_tail`
     / independent wrapper には依存しない構成にした。
   - `MiddleBlockTail.lean`
     は
     `import DkMath.ABC.MiddleBlockDepAbsorption`
     に差し替え、
     `ABC010`
     relay entry として dependent absorption API を re-export する。
3. 判断:
   - dependent absorption は
     `MiddleBlockDyadicTail`
     の
     `summable_exp_neg_two_pow`,
     `mid_block_upper_hp_dep_expCard_factor`,
     `Kset` / `Emid` / `GoodX`
     を使うが、
     `MiddleBlockTail`
     の scaffold lemma 群には依存しない。
   - よって
     `MiddleBlockDepAbsorption`
     は
     `MiddleBlockTail`
     から独立した上位 owner として成立する。
   - `MiddleBlockTail`
     に残る実体は
     `mid_block_chernoff_tail`,
     `badcount_by_expect`,
     `mid_block_chernoff_tail_indep`,
     `union_over_k_midblock_bound_indep`,
     `EZmid_expect_le_card_smul_q`
     のみとなった。
4. 追跡文書:
   - `check-relay-lean.md`
     の
     `ABC010`
     に
     `MiddleBlockDepAbsorption`
     を再分割先として追記した。
   - `refact-changed-001.md`
     に
     `MiddleBlockTail -> MiddleBlockDepAbsorption`
     分離内容を追記した。
   - `chain-cut-patterns-001.md`
     に
     dependent absorption owner と `ABC010` relay entry の切り分けパターンを追記した。
5. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleBlockDepAbsorption`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleBlockTail DkMath.ABC.ABC010 DkMath.ABC.Main`
   - 以上を確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知 info:
     `ABC038Bridge.lean`
     の axioms note
6. 次の課題:
   - `MiddleBlockTail`
     の残存
     scaffold / independent wrapper / expectation helper
     をさらに named owner 化するか判断する。
   - 候補:
     `MiddleBlockScaffoldTail`
     または
     `MiddleBlockIndependentScaffold`
     へ
     `mid_block_chernoff_tail`,
     `mid_block_chernoff_tail_indep`,
     `union_over_k_midblock_bound_indep`,
     `EZmid_expect_le_card_smul_q`
     を移す。

## 2026/04/25 22:37 JST

1. 目的:
   - `MiddleBlockTail`
     に残った scaffold / independent wrapper / expectation helper を named owner 化する。
   - `MiddleBlockTail`
     を
     `ABC010`
     互換の thin relay にする。
2. 実施:
   - 新設:
     `DkMath.ABC.MiddleBlockScaffoldTail`
   - `MiddleBlockTail.lean`
     から以下を移設した:
     `Prob.mid_block_chernoff_tail`,
     `Prob.badcount_by_expect`,
     `Prob.mid_block_chernoff_tail_indep`,
     `Prob.union_over_k_midblock_bound_indep`,
     `Prob.EZmid_expect_le_card_smul_q`
   - `MiddleBlockScaffoldTail.lean`
     は
     `MiddleBlockDepAbsorption`
     を import し、
     旧 `MiddleBlockTail`
     の最後の実体定義群を保持する owner とした。
   - `MiddleBlockTail.lean`
     は
     `import DkMath.ABC.MiddleBlockScaffoldTail`
     のみを持つ thin relay へ縮小した。
3. 判断:
   - `MiddleBlockTail`
     の実体定義はすべて named owner へ移った。
   - `ABC010.lean`
     は従来どおり
     `MiddleBlockTail`
     を import するため、
     downstream 互換性は維持される。
   - 実体 owner の流れは概ね
     `MiddleZmidBasic`
     →
     `MiddleBlockMGF`
     →
     `MiddleBlockEvents`
     →
     `MiddleBlockDyadicTail`
     →
     `MiddleBlockDepAbsorption`
     →
     `MiddleBlockScaffoldTail`
     →
     `MiddleBlockTail`
     となった。
4. 追跡文書:
   - `check-relay-lean.md`
     の
     `ABC010`
     に
     `MiddleBlockScaffoldTail`
     を再分割先として追記した。
   - `refact-changed-001.md`
     に
     `MiddleBlockTail -> MiddleBlockScaffoldTail`
     分離内容を追記した。
   - `chain-cut-patterns-001.md`
     に
     scaffold owner と thin relay 化のパターンを追記した。
5. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleBlockScaffoldTail DkMath.ABC.MiddleBlockTail DkMath.ABC.ABC010 DkMath.ABC.Main`
   - 以上を確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知 info:
     `ABC038Bridge.lean`
     の axioms note
6. 次の課題:
   - `ABC010.lean`
     を最終的に
     `MiddleBlockTail`
     relay ではなく
     named owner へ直接向けるか検討する。
   - あるいは次の番号付き relay の薄化へ進み、
     `ABC011`
     / `TailRadicalBasic`
     周辺の owner 境界を確認する。

## 2026/04/26 04:30 JST

1. 目的:
   - `ABC010.lean`
     を thin relay の
     `MiddleBlockTail`
     経由ではなく、
     実体 owner の
     `MiddleBlockScaffoldTail`
     へ直接向ける。
   - `MiddleBlockTail`
     をコード上未参照の互換 relay として切り離す。
2. 実施:
   - `ABC010.lean`
     の import を
     `DkMath.ABC.MiddleBlockTail`
     から
     `DkMath.ABC.MiddleBlockScaffoldTail`
     へ変更した。
   - `rg`
     で
     `import DkMath.ABC.MiddleBlockTail`
     がコード上に残っていないことを確認した。
   - `MiddleBlockTail.lean`
     は削除せず、
     旧互換用の未参照 thin relay として残した。
3. 判断:
   - `ABC010`
     の実体移設先は
     `MiddleBlockScaffoldTail`
     と見なせる。
   - `MiddleBlockTail`
     は最終削除フェーズで削除候補にできるが、
     今回は active file / 互換入口として残す。
4. 追跡文書:
   - `check-relay-lean.md`
     の
     `ABC010`
     移設先を
     `MiddleBlockScaffoldTail`
     に更新し、
     `MiddleBlockTail`
     を旧互換 relay として記録した。
   - `refact-changed-001.md`
     に
     `ABC010 -> MiddleBlockScaffoldTail`
     direct import 化を追記した。
   - `chain-cut-patterns-001.md`
     に
     番号付き relay から named owner へ直接向けるパターンを追記した。
5. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC010 DkMath.ABC.Main`
   - 以上を確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知 info:
     `ABC038Bridge.lean`
     の axioms note
6. 次の課題:
   - `ABC011`
     / `TailRadicalBasic`
     周辺で同様に、
     番号付き relay から direct owner import へ切れる箇所を確認する。
   - 最終削除フェーズでは
     未参照 thin relay の
     `MiddleBlockTail`
     を残すか削除するか判断する。

## 2026/04/26 04:53 JST

1. 目的:
   - `ABC011`
     の実体 owner である
     `TailRadicalBasic`
     から、
     rad / `piSqRad`
     解析ではない finite-union / independent Cstar 層を分離する。
   - `MiddleBlockIndependentTail`
     が
     `TailRadicalBasic`
     を経由せず、
     必要な確率 union API だけを import する形にする。
2. 実施:
   - `TailUnionBasic.lean`
     を新設した。
   - `TailRadicalBasic.lean`
     から次を移設した:
     `measure_union_over_k`,
     `measure_union_over_k_bound`,
     `summable_exp_neg_two_pow_mul`,
     `midblockCstarIndep`,
     `prob_real_le_one`
   - `TailRadicalBasic.lean`
     は
     `TailUnionBasic`
     import に切り替え、
     `slice_sum_eq_badcount`
     以降の slice / rad / `piSqRad`
     owner として縮小した。
   - `MiddleBlockIndependentTail.lean`
     の import を
     `TailRadicalBasic`
     から
     `TailUnionBasic`
     へ変更した。
   - `AnalyticQualityBridge.lean`
     は
     `piSqRad`
     を直接使っていたため、
     `TailRadicalBasic`
     を明示 import するようにした。
3. 判断:
   - `MiddleBlockIndependentTail`
     は independent union / Cstar API だけを必要とし、
     rad / `piSqRad`
     owner には依存しない。
   - `AnalyticQualityBridge`
     の `piSqRad`
     利用は推移 import ではなく直接 import で表現すべき依存である。
4. 追跡文書:
   - `check-relay-lean.md`
     の
     `ABC011`
     に
     `TailUnionBasic`
     を再分割先として追記した。
   - `refact-changed-001.md`
     に今回の moved declaration と import 境界変更を追記した。
   - `chain-cut-patterns-001.md`
     に
     finite-union / independent Cstar owner と rad / `piSqRad`
     owner を分けるパターンを追記した。
5. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.TailUnionBasic DkMath.ABC.TailRadicalBasic DkMath.ABC.MiddleBlockIndependentTail DkMath.ABC.AnalyticQualityBridge DkMath.ABC.ABC011 DkMath.ABC.Main`
   - 以上を確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知 info:
     `ABC038Bridge.lean`
     の axioms note
6. 次の課題:
   - `ABC012`
     / `MiddleBlockIndependentTail`
     側で、
     independent tail wrapper からさらに確率分割・small/large Kset 補題を named owner 化できるか確認する。
   - `TailRadicalBasic`
     内の
     slice counting 層と rad / `piSqRad`
     解析層の境界を、downstream import を見ながら再評価する。

## 2026/04/26 06:10 JST

1. 目的:
   - `ABC012`
     の実体 owner である
     `MiddleBlockIndependentTail`
     をさらに分解し、
     K-index decomposition,
     independent dyadic tail,
     absorption / GoodX 下界の境界を明確にする。
2. 実施:
   - `MiddleBlockKSplit.lean`
     を新設した。
   - `MiddleBlockIndependentTail.lean`
     から次を移設した:
     `Prob.Ksmall`,
     `Prob.Klarge`,
     `Prob.Kset_disjoint_union`,
     `Prob.card_Ksmall_le_three`
   - `MiddleBlockIndependentDyadic.lean`
     を新設した。
   - `MiddleBlockIndependentTail.lean`
     から次を移設した:
     `Prob.two_mul_sq_over_add_ge_self`,
     `Prob.midblock_tail_indep_dyadic_strong`
   - `MiddleBlockIndependentTail.lean`
     は
     `MiddleBlockIndependentDyadic`
     import に切り替え、
     `midblock_union_absorb_indep_const`
     と
     `goodX_measure_ge_one_sub_midblockCstarIndep`
     を保持する absorption / GoodX 下界 owner に縮小した。
3. 判断:
   - `MiddleBlockKSplit`
     は
     `Kset`
     の small/large decomposition だけを持つため、
     independent tail 以外の downstream からも参照しやすい。
   - `MiddleBlockIndependentDyadic`
     は
     independent Chernoff bound から dyadic tail へ落とす証明を保持し、
     union absorption 本体から切り離せた。
4. 追跡文書:
   - `check-relay-lean.md`
     の
     `ABC012`
     に
     `MiddleBlockKSplit`
     と
     `MiddleBlockIndependentDyadic`
     を再分割先として追記した。
   - `refact-changed-001.md`
     に今回の moved declaration と import 境界変更を追記した。
   - `chain-cut-patterns-001.md`
     に
     Kset split / independent dyadic / absorption owner
     の分離パターンを追記した。
5. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MiddleBlockKSplit DkMath.ABC.MiddleBlockIndependentDyadic DkMath.ABC.MiddleBlockIndependentTail DkMath.ABC.ABC012 DkMath.ABC.Main`
   - 以上を確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知 info:
     `ABC038Bridge.lean`
     の axioms note
6. 次の課題:
   - `ABC012`
     を
     `MiddleBlockIndependentTail`
     relay のまま残すか、
     downstream が必要とする owner へ直接向けるかを確認する。
   - `ABC013`
     / `SliceDiagonalCounting`
     の counting extraction 層で、
     `MiddleBlockIndependentTail`
     依存をさらに狭められるか調査する。

## 2026/04/26 06:27 JST

1. 目的:
   - `ABC013`
     の実体 owner である
     `SliceDiagonalCounting`
     から、
     slice-average / Markov 層を分離する。
   - `SliceDiagonalCounting`
     が
     `MiddleBlockIndependentTail`
     を経由せず、
     counting / ratio owner だけに依存する形にする。
2. 実施:
   - `SliceAverageBasic.lean`
     を新設した。
   - `SliceDiagonalCounting.lean`
     から次を移設した:
     `slice_heavy_card_le`,
     `eventually_slice_heavy_sublinear`,
     `eventually_slice_heavy_sublinear_of_badcount_subquad`
   - `SliceAverageBasic.lean`
     は
     `RatioBound`
     を import し、
     `sliceBadCount`,
     `BadCount`,
     `eventually_badcount_le_eps`
     による slice-average / Markov owner とした。
   - `SliceDiagonalCounting.lean`
     の import を
     `MiddleBlockIndependentTail`
     から
     `SliceAverageBasic`
     へ変更した。
3. 判断:
   - `SliceDiagonalCounting`
     は independent tail / GoodX absorption に依存しておらず、
     `RatioBound`
     系の counting API だけで成立する。
   - `SliceAverageBasic`
     は downstream から slice-heavy sublinear 補題だけを参照したい場合の軽い入口になる。
4. 追跡文書:
   - `check-relay-lean.md`
     の
     `ABC013`
     に
     `SliceAverageBasic`
     を再分割先として追記した。
   - `refact-changed-001.md`
     に今回の moved declaration と import 境界変更を追記した。
   - `chain-cut-patterns-001.md`
     に
     slice-average owner と diagonal counting owner の分離パターンを追記した。
5. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.SliceAverageBasic DkMath.ABC.SliceDiagonalCounting DkMath.ABC.ABC013 DkMath.ABC.Main`
   - 以上を確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知 info:
     `ABC038Bridge.lean`
     の axioms note
6. 次の課題:
   - `ABC014`
     / `AnalyticQualityBridge`
     で
     diagonal counting,
     `piSqRad`,
     analytic quality wrapper
     の import 境界を確認する。
   - `SliceDiagonalCounting`
     内の rad-log helper は
     `TailRadicalBasic`
     / `Rad`
     系 owner に移す価値があるか、downstream 参照を見て判断する。

## 2026/04/26 06:46 JST

1. 目的:
   - `ABC014`
     / `AnalyticQualityBridge`
     の import 境界を整理する。
   - `AnalyticQualityBridge`
     が
     rad-log positivity helper のためだけに
     `SliceDiagonalCounting`
     へ依存している状態を解消する。
2. 実施:
   - `RadLogBasic.lean`
     を新設した。
   - `SliceDiagonalCounting.lean`
     から次を移設した:
     `one_le_rad_real`,
     `log_rad_nonneg`,
     `log_rad_mul_nonneg`
   - `RadLogBasic.lean`
     は
     `Rad`
     だけを import し、
     radical の実数下界と log 非負性を保持する owner とした。
   - `SliceDiagonalCounting.lean`
     は
     `RadLogBasic`
     を import し、
     diagonal count / Icc rewrite owner にさらに縮小した。
   - `AnalyticQualityBridge.lean`
     は
     `SliceDiagonalCounting`
     import を廃止し、
     `RadLogBasic`
     と
     `TailRadicalBasic`
     を直接 import する形へ変更した。
3. 判断:
   - rad-log positivity helper は
     diagonal counting ではなく
     `Rad`
     近傍の基礎 API として扱うのが自然。
   - `AnalyticQualityBridge`
     は
     `piSqRad`
     と rad-log helper を使うが、
     `diagCount`
     / `diag_badcount_le_badcount`
     には依存していない。
   - そのため、
     analytic quality wrapper から diagonal counting owner を切ることで、
     `ABC014`
     relay の依存境界が明確になった。
4. 追跡文書:
   - `check-relay-lean.md`
     の
     `ABC014`
     に
     `RadLogBasic`
     を再分割先として追記した。
   - `refact-changed-001.md`
     に今回の moved declaration と import 境界変更を追記した。
   - `chain-cut-patterns-001.md`
     に
     rad-log owner と analytic quality bridge の分離パターンを追記した。
5. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.RadLogBasic DkMath.ABC.SliceDiagonalCounting DkMath.ABC.AnalyticQualityBridge DkMath.ABC.ABC014 DkMath.ABC.Main`
   - 以上を確認済み。
   - 既知警告:
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry`
   - 既知 info:
     `ABC038Bridge.lean`
     の axioms note
6. 次の課題:
   - `ABC014`
     / `AnalyticQualityBridge`
     内の analytic quality wrapper と adjacent / tail 側 wrapper の境界を確認する。
   - `ABC015`
     / `QualityTailBridge`
     との重複 API が残っていれば、
     downstream import を見ながら owner へ寄せる。
