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
