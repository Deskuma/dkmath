# History - リファクタリング作業履歴

cid: 69e46b72-e8bc-83e8-8b9c-152498680a64

- 時刻の打刻は `date` コマンドを使用して時間(時分秒)まで正確に行うこと。
- 新規履歴は **ファイル末尾** に追加すること。

## History Log

Archive

過去ログは、以下にアーカイブしてあります。

- None

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

### 日時: 2026/04/19 15:46 JST (ABC リファクタリング初回調査の固定)

1. 目的:
   - `DkMath.ABC` 再編の初手として、公開導線と kernel ownership の実測を取り、
     新しい refactoring ルート配下に進行ドキュメントを作る。
2. 実施:
   - `docs/__AGENT.md` を確認し、この branch でも
     `History.md` 継続更新と単体 build 方針を守ることを再確認した。
   - `plan-refactoring.md` を読み、既存提案の主軸が
     `rad 一本化 -> Kernel/Surface 新設 -> DkMath.ABC 軽量化`
     にあることを確認した。
   - `DkMath/ABC.lean`, `ABC/Main.lean`, `ABC/Core.lean`, `ABC/Rad.lean`,
     `ABC/Square.lean`, `ABC/Triple.lean`, `ABC/PadicValNat.lean`,
     `ABC/CountPowersDividing2n1.lean`, `ABC/Bridge.lean`
     を読み、現状を調査した。
   - 新規文書
     `current-state-001.md`
     を作成し、
     - `ABC.lean -> Main`
     - `Main -> ABC090 + Bridge + ABC038Bridge`
     - `Core` / `Rad` の `rad_dvd_nonzero` 重複
     - `Core` / `PadicValNat` の `padicValNat_split` 重複
     - `Square` / `Triple` が `Core` を引いていること
     を固定した。
   - `plan-refactoring.md` に
     実測で確認できたズレと、
     Phase 0-3 の具体的実施順を追記した。
3. 結論:
   - 最初に着手すべき対象は番号付き `ABC0**.lean` 連鎖ではなく、
     `Core` の catch-all 化と kernel ownership の曖昧さであると判断した。
   - 特に
     `rad_dvd_nonzero`
     と
     `padicValNat_split`
     の owner を固定するのが、最小かつ効果の大きい初手である。
4. 検証:
   - 今回は調査と文書更新のみであり、Lean build は実施していない。
5. 失敗事例:
   - なし。
6. 次の課題:
   - `rad_dvd_nonzero` と `padicValNat_split` の ownership を整理し、
     `Core` からの依存をどこまで外せるかを小さく検証する。
   - その後に `Kernel.lean` / `Surface.lean` 新設へ進む。

### 日時: 2026/04/20 22:26 JST (radical-kernel 補題群の `ABC.Rad` 集約)

1. 目的:
   - `rad` 本体の一本化に続いて、
     radical-kernel に属する補題群の owner も
     `DkMath.ABC.Rad`
     に寄せ、
     `Core` の catch-all 化を一段縮める。
2. 実施:
   - `ABC/Core.lean` と `ABC/Rad.lean` を再確認し、
     `Core` に残っていた radical 系補題のうち、
     `rad` の定義と factorization/support に直接依存するものを抽出した。
   - `ABC/Rad.lean` に以下を移設した。
     - `mem_support_factorization_iff`
     - `support_prod_log_eq_sum_log`
     - `support_prod_log_ge_sum_log`
     - `rad_prod`
     - `rad_log_eq_sum_prime_logs`
     - `rad_log_ge_sum_prime_logs`
     - `disjoint_support_of_coprime`
     - `support_mul_coprime`
     - `rad_mul_coprime`
     - `rad_le`
   - `ABC/Core.lean` から対応する重複ブロックを削除し、
     radical kernel は `DkMath.ABC.Rad` に集約した旨の注記へ差し替えた。
   - 証明修正として、
     `Rad.rad_le`
     は factorization product の整形後に
     `Nat.le_of_dvd`
     で閉じる形へ簡約した。
   - 変更記録
     `refact-changed-001.md`
     に今回の移設一覧を追記した。
3. 結論:
   - `rad` 本体だけでなく、
     `rad_prod` / `rad_mul_coprime` / `rad_le`
     などの radical-kernel 補題も
     `ABC.Rad`
     に揃い、
     `Core` は一段薄くなった。
   - 次の import thinning では、
     `Square` / `Triple`
     が `Core` からどこまで離れられるかを実測しやすい状態になった。
4. 検証:
   - `./lean-build.sh DkMath.ABC.Rad`
   - `./lean-build.sh DkMath.ABC.Core`
   - `./lean-build.sh DkMath.ABC.Square`
   - `./lean-build.sh DkMath.ABC.Triple`
   - `./lean-build.sh DkMath.ABC.MassBridge`
   - 以上はいずれも成功した。
5. 失敗事例:
   - 初回の `Rad.rad_le` 実装で、
     witness `k` による書き換えが target を
     `((∏ p ∈ s, p) * k).factorization.support`
     側へ変形してしまい build が落ちた。
   - これは `Nat.le_mul_of_pos_right` ではなく
     `Nat.le_of_dvd`
     を使う形へ直して解消した。
6. 次の課題:
   - `Square.lean` / `Triple.lean`
     の import を棚卸しし、
     moved radical lemmas の利用箇所が
     `Core` 依存を不要にしている部分を切り出す。
   - その後に
     `padicValNat_split`
     側の ownership 整理へ進む。

### 日時: 2026/04/21 12:37 JST (pure-rad API の `ABC.Rad` 集約と hidden import の顕在化)

1. 目的:
   - 前回の radical-kernel 集約に続き、
     `Square.lean`
     に残っていた pure-rad 補題群を
     `DkMath.ABC.Rad`
     へ寄せる。
   - あわせて
     `Triple -> Core`
     の過剰依存を薄くし、
     露出した hidden import を記録する。
2. 実施:
   - `ABC/Square.lean` と `ABC/Triple.lean` の使用箇所を棚卸しし、
     `squarefull` に依存しない pure-rad 補題を抽出した。
   - `ABC/Rad.lean` に以下を移設した。
     - `rad_eq_self_of_squarefree`
     - `rad_eq_self_of_squarefree'`
     - `factorization_prod_primes`
     - `squarefree_of_rad_eq_self`
     - `rad_pow_eq_rad`
     - `rad_mul_general`
     - `rad_mul_coprime'`
     - `abc_one_le_rad`
     - `rad_pos`
   - `ABC/Square.lean` から対応する定義群を削除し、
     squarefree / squarefull と近接積応用だけを残した。
   - `ABC/Triple.lean` の import を
     `DkMath.ABC.Core`
     から
     `DkMath.ABC.Rad`
     へ変更した。
   - その結果、
     `RatioBound.lean`
     が `Nat.ceil_spec` と `div_lt_iff` を
     `Triple -> Core`
     の隠れ依存で拾っていたことが顕在化したため、
     `import DkMath.ABC.Basic`
     を追加して明示 import に修正した。
   - `refact-changed-001.md`
     に今回の移設内容と hidden import 修正を追記した。
3. 結論:
   - `rad_eq_self_of_squarefree` や `rad_mul_general` のような
     公開 rad API は
     `ABC.Rad`
     に揃い、
     `Square.lean`
     は radical の owner ではなく応用層に近づいた。
   - `Triple` を軽くしたことで、
     `RatioBound`
     の hidden import が明示化され、
     今後の import thinning で見るべきパターンがはっきりした。
4. 検証:
   - `./lean-build.sh DkMath.ABC.Rad`
   - `./lean-build.sh DkMath.ABC.Square`
   - `./lean-build.sh DkMath.ABC.Triple`
   - `./lean-build.sh DkMath.ABC.RatioBound`
   - 以上は成功した。
5. 失敗事例:
   - 初回の `ABC038Bridge` 再 build で、
     `RatioBound.lean`
     が
     `Nat.ceil_spec`
     と
     `div_lt_iff`
     を見失って落ちた。
   - 原因は
     `Triple -> Core`
     の transitively imported な `ABC.Basic` に依存していたためであり、
     `RatioBound`
     へ明示 import を追加して解消した。
   - `ABC038Bridge` 全体 build は compile 時間が長すぎるため今回は打ち切り、
     単体の下流確認は
     `RatioBound`
     までで止めた。
6. 次の課題:
   - `Triple`
     を参照する他ファイルでも同種の hidden import がないかを洗い出す。
   - `padicValNat_split`
     と関連する補題群についても、
     owner を固定しつつ transitively imported な依存を崩していく。

### 日時: 2026/04/21 12:56 JST (gcd/coprime 小補題の owner を `DkMath.Basic.Nat` に固定)

1. 目的:
   - `coprime_succ`
     まわりの小補題群について、
     `ABC.Core`
     内の重複をやめ、
     `DkMath.Basic.Nat`
     を owner に固定する。
   - その際、
     既存の
     `DkMath.ABC.coprime_succ`
     呼び口を急に壊さず、
     hidden import も 1 件顕在化させる。
2. 実施:
   - `DkMath.Basic.Nat`
     にすでに存在する
     `succ_sub_self`
     `dvd_one_iff`
     `gcd_succ`
     `coprime_succ`
     を確認した。
   - `ABC/Core.lean`
     に
     `import DkMath.Basic.Nat`
     を追加し、
     上記 4 補題の重複定義を削除した。
   - 互換維持のため、
     `namespace DkMath.ABC`
     内で
     `export DkMath.Basic.Nat (succ_sub_self dvd_one_iff gcd_succ coprime_succ)`
     を追加し、
     既存コードからは
     `DkMath.ABC.coprime_succ`
     を引き続き見える形にした。
   - owner 直参照の試しとして
     `ABC001.lean`
     に
     `import DkMath.Basic.Nat`
     を追加した。
3. 結論:
   - gcd/coprime の小補題群は
     `Basic.Nat`
     が owner、
     `ABC.Core`
     は再輸出だけを担う形に整理できた。
   - radical 系で行った
     「owner を寄せつつ public API はいったん維持」
     の進め方を、
     gcd/coprime 側にも適用できることを確認した。
4. 検証:
   - `./lean-build.sh DkMath.Basic.Nat`
   - `./lean-build.sh DkMath.ABC.Core`
   - `./lean-build.sh DkMath.ABC.ABC001`
   - `./lean-build.sh DkMath.ABC.ABC016`
   - 以上は成功した。
5. 失敗事例:
   - 初回は
     `ABC.Core`
     から重複定義を消しただけだったため、
     `ABC001.lean`
     で
     `coprime_succ`
     未解決エラーが発生した。
   - これは
     `ABC.Core`
     での `export DkMath.Basic.Nat (...)`
     を追加して public API を維持し、解消した。
6. 次の課題:
   - `coprime_succ`
     と同様に、
     `squarefree` / `squarefull`
     についても owner と re-export の境界を整理する。
   - その後に
     `padicValNat_split`
     系の owner 固定と hidden import 顕在化へ進む。

### 日時: 2026/04/21 13:15 JST (valuation 補題 `padicValNat_split` の owner を `DkMath.ABC.PadicValNat` に固定)

1. 目的:
   - `ABC.Core`
     と
     `ABC.PadicValNat`
     に二重定義されていた
     `padicValNat_split`
     を一本化し、
     valuation 系の基本補題の owner を固定する。
   - 既存の
     `DkMath.ABC.*`
     呼び口は壊さず、
     `Core`
     を catch-all から一段薄くする。
2. 実施:
   - `ABC/Core.lean`
     と
     `ABC/PadicValNat.lean`
     を再確認し、
     `padicValNat_split`
     が同一内容で重複していることを確認した。
   - `ABC/Core.lean`
     に
     `import DkMath.ABC.PadicValNat`
     を追加した。
   - `ABC/Core.lean`
     からローカルの
     `padicValNat_split`
     定義を削除し、
     valuation の基本補題は
     `DkMath.ABC.PadicValNat`
     に集約した旨の注記へ置き換えた。
   - `refact-changed-001.md`
     に今回の owner 固定内容を追記した。
3. 結論:
   - `padicValNat_split`
     は
     `DkMath.ABC.PadicValNat`
     が owner、
     `ABC.Core`
     は import により見せるだけの層、
     という役割分担に整理できた。
   - これで
     `rad`
     と
     gcd/coprime
     のときと同じく、
     「owner module に寄せて Core は薄くする」
     方向を valuation 系にも適用できた。
4. 検証:
   - `./lean-build.sh DkMath.ABC.PadicValNat`
   - `./lean-build.sh DkMath.ABC.Core`
   - `./lean-build.sh DkMath.ABC.ABC001`
   - 以上は成功した。
5. 失敗事例:
   - `./lean-build.sh DkMath.ABC.ABC016`
     も下流確認として開始したが、
     このサイクルの確認対象としては compile 時間が長すぎたため打ち切り、
     より近い下流
     `ABC001`
     に切り替えた。
   - build failure は発生していない。
6. 次の課題:
   - `padicValNat_split`
     に続いて、
     valuation 系で
     `Core`
     から剥がせる補題がまだあるかを棚卸しする。
   - 並行して、
     `squarefree` / `squarefull`
     の owner と re-export 境界を整理し、
     `Core`
     依存をさらに薄くする。

### 日時: 2026/04/21 13:28 JST (`ABC020` の valuation 重複断片を除去し、全体 build で確認)

1. 目的:
   - `padicValNat_split`
     の owner 固定後に、
     長い全体 build を最後まで待って実エラーを確認する。
   - 露出した重複断片があれば、
     その場で owner module 側へ寄せて再 build する。
2. 実施:
   - `__build.log`
     を確認し、
     `DkMath.ABC.ABC020`
     で
     `DkMath.ABC.padic_val_two_of_odd`
     の重複宣言エラーが出ていることを確認した。
   - `ABC020.lean`
     を調べ、
     `PadicValNat.lean`
     に同名補題があるにもかかわらず、
     ローカルにも同一内容の定義が残っていることを確認した。
   - `ABC020.lean`
     からローカルの
     `padic_val_two_of_odd`
     を削除し、
     valuation/counting の基本補題は
     `DkMath.ABC.PadicValNat`
     に集約した旨の注記へ差し替えた。
   - その後、
     失敗していた局所 build
     `DkMath.ABC.ABC020`
     を通し、
     続けて
     `./lean-build.sh DkMath`
     を最後まで待って結果を確認した。
   - `refact-changed-001.md`
     に今回の follow-up 修正を追記した。
3. 結論:
   - valuation 系の owner を
     `DkMath.ABC.PadicValNat`
     に寄せた結果として、
     `ABC020`
     に残っていた旧断片が露出した。
   - これを除去したことで、
     少なくとも今回の refactoring に起因する全体 build 停止点は解消し、
     長い build も通ることを確認できた。
4. 検証:
   - `./lean-build.sh DkMath.ABC.ABC020`
   - `./lean-build.sh DkMath`
   - 以上は成功した。
   - 全体 build では既存の `sorry` 警告のみ replay された。
5. 失敗事例:
   - `ABC020`
     の局所 build 前に全体 build を確認したところ、
     `padic_val_two_of_odd`
     重複で停止した。
   - これは
     `PadicValNat`
     へ寄せた owner と、
     `ABC020`
     に残存していた旧定義が衝突したためであり、
     ローカル断片を削除して解消した。
6. 次の課題:
   - valuation 系について、
     `ABC020`
     と同様の旧断片が他の
     `ABC0**`
     に残っていないかを点検する。
   - そのうえで、
     `squarefree` / `squarefull`
     の owner 固定と re-export 境界整理を進める。

### 日時: 2026/04/21 13:38 JST (`ABC025` の valuation basic-bounds を owner module に寄せ、live chain の重複を点検)

1. 目的:
   - `ABC020`
     の follow-up として、
     live な
     `ABC0**`
     連鎖に valuation 系の旧断片がまだ残っていないかを確認する。
   - 重複があれば、
     `DkMath.ABC.PadicValNat`
     へ寄せて
     `ABC0**`
     を薄くする。
2. 実施:
   - `rg`
     で
     `PadicValNat`
     owner 側の lemma 名と
     `ABC0**`
     側の重複を調べた。
   - その結果、
     `ABC025.lean`
     に
     `padicValNat_le_self`
     と
     `padicValNat_le_log`
     が残っていることを確認した。
   - `ABC025.lean`
     に
     `import DkMath.ABC.PadicValNat`
     を追加し、
     上記 2 補題のローカル定義を削除した。
   - 既存の telescoping 部分は変更せず、
     参照側が owner module の定義をそのまま使う形に整理した。
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC025`
     を実行し、
     進捗付きで build を確認した。
   - 追加で、
     `PadicValNat.lean`
     の lemma 名と
     `ABC0*.lean`
     の lemma 名の交差を機械探索し、
     live chain には追加の重複がないことを確認した。
   - `ABCSolvedProofSamples.lean`
     と
     `ABCWorking.lean`
     に同名断片があることも検出したが、
     これは scratch/archive 系として本サイクルでは触らず、
     別管理とした。
3. 結論:
   - live chain 側の valuation basic-bounds の重複は、
     現時点で
     `ABC020`
     と
     `ABC025`
     まで除去できた。
   - `PadicValNat`
     owner と
     `ABC0**`
     連鎖の境界はかなり明確になり、
     次の対象を
     `squarefree` / `squarefull`
     へ移しやすくなった。
4. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC025`
   - 以上は成功した。
   - build 出力では
     `ABC021`
     の既存 `sorry` 警告のみ replay された。
5. 失敗事例:
   - なし。
6. 次の課題:
   - valuation 系については、
     scratch/archive 枠
     `ABCSolvedProofSamples.lean`
     と
     `ABCWorking.lean`
     を live chain と切り分ける方針を文書化する。
   - 実装作業としては、
     `squarefree` / `squarefull`
     の owner 固定と
     `Core`
     の re-export 境界整理へ進む。

### 日時: 2026/04/21 14:00 JST (`squarefree` / `squarefull` の owner を `DkMath.ABC.Square` に固定)

1. 目的:
   - valuation 系に続いて、
     `squarefree` / `squarefull`
     の定義 owner を
     `Core`
     から切り離し、
     `Square`
     に固定する。
   - そのうえで、
     `Core`
     は定義本体を持たず、
     import 経由で公開する境界に整理する。
2. 実施:
   - `Core.lean`
     と
     `Square.lean`
     を調査し、
     `squarefree`
     / `squarefull`
     と mirror alias
     `squarefull'`
     / `squarefree_prop`
     が
     `Core`
     にだけ存在し、
     `Square`
     はそれらを使う側になっていることを確認した。
   - `Square.lean`
     の import を
     `DkMath.ABC.Core`
     から
     `DkMath.ABC.Rad`
     へ変更し、
     循環しない形で standalone 化した。
   - `Square.lean`
     に
     `squarefull'`,
     `squarefree_prop`,
     `squarefree`,
     `squarefull`
     の定義を移設した。
   - `Core.lean`
     に
     `import DkMath.ABC.Square`
     を追加し、
     上記定義の重複ブロックを削除した。
   - 注記として、
     squarefree / squarefull controls の owner は
     `DkMath.ABC.Square`
     であることを明記した。
   - 下流互換の確認として
     `MassBridge`
     まで build を回した。
   - なお、
     user 移設済みの
     `DkMath.ABC.Demo.ABCSolvedProofSamples`
     と
     `DkMath.ABC.Demo.ABCWorking`
     は本サイクルでも非対象として触れていない。
3. 結論:
   - `squarefree` / `squarefull`
     の owner は
     `DkMath.ABC.Square`
     に固定され、
     `Core`
     は catch-all からさらに一段薄くなった。
   - `Square`
     自身も
     `Core`
     非依存で立つようになり、
     定義 owner と応用補題の所在が一致した。
4. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Square`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Core`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.MassBridge`
   - 以上は成功した。
5. 失敗事例:
   - なし。
6. 次の課題:
   - `Core`
     が `Square`
     を import するようになったことで、
     他ファイルの hidden import が露出していないかを点検する。
   - 次の実装対象としては、
     `Triple`
     や `Main`
     周辺で
     `Core`
     にまだ残る catch-all 依存を洗うのが自然である。

### 日時: 2026/04/21 15:46 JST (`Main` の公開入口を明示化し、hidden import 探索を開始)

1. 目的:
   - `squarefree` / `squarefull`
     の owner 固定を受けて、
     `DkMath.ABC.Main`
     がそれらを transitively ではなく direct import で公開するようにする。
   - そのうえで
     `Main`
     build を回し、
     catch-all 依存を外した結果として露出する hidden import を順に表へ出す。
2. 実施:
   - `Main.lean`
     に
     `import DkMath.ABC.Square`
     を追加した。
   - 進捗付き build
     `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
     を実行し、
     露出した停止点を順に確認した。
   - まず
     `ABC001`
     で
     `coprime_succ`
     が未解決になったため、
     owner module
     `DkMath.Basic.Nat`
     の補題であることを明示し、
     3 箇所を
     `DkMath.Basic.Nat.coprime_succ`
     へ置き換えた。
   - 次に同系統の hidden import を洗い、
     `ABC002`, `ABC003`, `ABC014`, `ABC015`, `ABC016`, `ABC031`
     に
     `import DkMath.Basic.Nat`
     と
     `open DkMath.Basic.Nat`
     を追加した。
   - さらに
     `ABC009`
     で
     `RpowExtras.rpow_mul_nat`
     が未解決になったため、
     owner がまだ
     `ABC.Core`
     にあることを認め、
     `import DkMath.ABC.Core`
     を追加して explicit import に直した。
   - 局所検証として
     `DkMath.ABC.ABC001`,
     `DkMath.ABC.ABC002`,
     `DkMath.ABC.ABC009`
     を進捗付き build で通した。
   - `Main`
     build 自体はその後も継続しており、
     本記録時点では新しい `error:` は出ていない。
3. 結論:
   - `Main`
     の direct import 化により、
     これまで transitive に隠れていた
     `coprime_succ`
     と
     `RpowExtras`
     の owner 依存が露出した。
   - これらを explicit import / explicit qualification に直したことで、
     public entry から見た hidden import の掃除が実際に進み始めた。
4. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC001`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC002`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC009`
   - 以上は成功した。
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
     は実行継続中で、
     本記録時点では追加の `error:` は観測されていない。
5. 失敗事例:
   - `Main`
     build 初回では
     `ABC001`
     の
     `coprime_succ`
     未解決で停止した。
   - その修正後、
     次の停止点として
     `ABC002`
     の同名未解決、
     続いて
     `ABC009`
     の
     `RpowExtras.rpow_mul_nat`
     未解決が現れた。
   - いずれも hidden import が表に出たものとして処理し、
     explicit owner import に直して解消した。
6. 次の課題:
   - `Main`
     build を最後まで観察し、
     次に露出する hidden import があれば同じ方針で owner import へ寄せる。
   - 並行して、
     `RpowExtras`
     のように
     `Core`
     に残る補助 namespace は、
     将来的に専用 module へ切り出す候補として整理する。

### 日時: 2026/04/21 17:53 JST (`ABC連番` チェイン切断パターンのメモ化)

1. 目的:
   - 連番 chain の hidden import 探索を続けるだけでなく、
     どの種類の依存が切りやすいかを文書として固定する。
   - 次サイクルで
     「どこから切るか」
     を迷わないよう、
     観測済みパターンと具体候補を 1 枚へまとめる。
2. 実施:
   - `ABC001`-`ABC040`
     の import 列を機械抽出し、
     直列 predecessor 以外の direct import がどこに現れているかを調べた。
   - その結果、
     既に serial chain を横切っている seed として
     `Square`,
     `RatioBound`,
     `Core`,
     `CountPowersDividing2n1`,
     `PadicValNat`,
     `ABC025_bound2`
     を確認した。
   - `ABC090.lean`
     に comment block 内の残骸があることも確認したが、
     これは chain-cut 本体とは別件の cleanup 候補として分離した。
   - 新規文書
     `chain-cut-patterns-001.md`
     を作成し、
     次の 3 パターンを整理した。
     - owner import 露出型
     - shared utility 横刺し型
     - thin base + thematic band 型
   - あわせて具体候補として
     `RpowExtras`
     専用 module 化、
     `ABC024`-`ABC028`
     の utility-first 化、
     `ABC001`-`ABC003`
     の base seam 固定
     を記録した。
3. 結論:
   - `ABC連番`
     の直列 chain は一気に壊すより、
     すでに direct import が現れている箇所を seam として使うのが妥当である。
   - 特に
     `ABC009`
     の
     `RpowExtras`,
     `ABC024`-`ABC028`
     の p-adic utility 群、
     `ABC001`-`ABC003`
     の base band
     が、次に切りやすい帯として見えた。
4. 検証:
   - 今回は調査と文書化が中心であり、
     追加 build は行っていない。
5. 失敗事例:
   - なし。
6. 次の課題:
   - `Main`
     build の hidden import 探索を継続しつつ、
     文書で第一候補に挙げた
     `RpowExtras`
     専用 module 化を実際に試す。
   - その後に、
     `ABC024`-`ABC028`
     を utility-first に寄せられるかを局所検証する。

### 日時: 2026/04/21 17:54 JST (`Main` build の hidden import 探索が一巡し、公開入口まで再通過)

1. 目的:
   - 直前サイクルで露出した hidden import 修正が、
     本当に
     `DkMath.ABC.Main`
     まで効いているかを確認する。
2. 実施:
   - 継続していた
     `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
     の完走を確認した。
   - build ログを確認し、
     `ABC010`-`ABC040`, `ABC090`, `ABC038Bridge`
     まで再通過していることを確認した。
3. 結論:
   - `coprime_succ`
     系と
     `RpowExtras`
     系の explicit owner import 修正により、
     現時点の
     `Main`
     build は再び通る状態へ戻った。
   - hidden import 探索は、
     public entry を壊さずに進められることを確認した。
4. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上は成功した。
5. 失敗事例:
   - なし。
6. 次の課題:
   - 次サイクルは予定どおり、
     `RpowExtras`
     の専用 module 化を first cut として試す。
   - その後、
     `ABC024`-`ABC028`
     の utility-first 化候補を点検する。

### 日時: 2026/04/21 18:00 JST (`RpowExtras` を専用 module 化し、`ABC009 -> Core` 依存を切断)

1. 目的:
   - `chain-cut-patterns-001.md`
     で first cut 候補にした
     `RpowExtras`
     専用 module 化を実際に試す。
   - これにより
     `ABC009`
     が
     `Core`
     を direct import しなくて済むかを確認する。
2. 実施:
   - 新規 file
     `DkMath/ABC/RpowExtras.lean`
     を作成し、
     `RpowExtras.rpow_mul_nat`,
     `RpowExtras.one_lt_rpow_two`,
     `RpowExtras.denom_pos`
     を移設した。
   - `ABC/Core.lean`
     に
     `import DkMath.ABC.RpowExtras`
     を追加し、
     旧来の
     `namespace RpowExtras`
     ブロックを削除した。
   - `ABC009.lean`
     の import を
     `DkMath.ABC.Core`
     から
     `DkMath.ABC.RpowExtras`
     へ置き換えた。
   - これにより
     `ABC009`
     は middle-band のためだけに
     `Core`
     を引く必要がなくなった。
3. 結論:
   - `RpowExtras`
     は
     `Core`
     の catch-all から切り出せる独立 utility であることを確認した。
   - `ABC009 -> Core`
     依存を 1 本切れたので、
     chain-cut memo に書いた
     owner import 露出型
     が実際に有効なことを示せた。
4. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.RpowExtras`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Core`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC009`
   - 以上は成功した。
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
     は実行継続中で、
     本記録時点では新しい `error:` は観測されていない。
5. 失敗事例:
   - なし。
6. 次の課題:
   - `Main`
     build の完走を確認し、
     この切断が public entry まで波及して問題ないことを確定する。
   - 次の chain-cut 候補として、
     `ABC024`-`ABC028`
     の utility-first 化を試す。

### 日時: 2026/04/21 21:05 JST (`ABC024` の empty relay import を外し、`ABC024`-`ABC028` 帯の first cut を確認)

1. 目的:
   - `chain-cut-patterns-001.md`
     で候補化していた
     `ABC024`-`ABC028`
     の utility-first 化を小さく試す。
   - 特に
     `ABC024`
     が実質 empty relay の
     `ABC023`
     を踏まずに、
     owner import へ直接寄せられるかを確認する。
2. 実施:
   - `ABC023.lean`
     を再確認し、
     実体が
     `import DkMath.ABC.ABC022`
     だけの empty relay であることを確認した。
   - `ABC024.lean`
     の import を
     `import DkMath.ABC.ABC023`
     から、
     `import DkMath.ABC.ABC022`,
     `import DkMath.ABC.RatioBound`,
     `import DkMath.ABC.CountPowersDividing2n1`
     へ置換した。
   - `ABC024`
     内で実際に使っているのが
     `rpow_layer_cake`,
     `natCeil_le_add_one_real`,
     `count_powers_dividing_2n1`
     であることを検索で確認し、
     内容本体は変更しなかった。
3. 結論:
   - `ABC024`
     は serial predecessor に依存せず、
     layer-cake / ceil / counting の owner を直接 import する形へ切り替え可能だった。
   - これにより
     `ABC024`-`ABC028`
     帯について、
     utility-first cut
     が抽象案ではなく実際に効くことを示せた。
   - 次は
     `ABC025`
     以降で、
     `ABC024`
     由来の layer-cake 部と
     `ABC025`
     自身の telescoping kernel をどう分離するかを見る段階である。
4. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC024`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC025`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC028`
   - 以上は成功した。
   - 既知の `ABC021.lean` の `sorry` 警告のみ replay された。
5. 失敗事例:
   - なし。
6. 次の課題:
   - `ABC025`
     から
     `ABC024`
     依存をどこまで utility import 化できるかを棚卸しする。
   - `ABC024`-`ABC028`
     帯の public seed を
     `ABC025`
     に置くべきか、
     あるいは counting / layer-cake を別 utility に逃がすべきかを見極める。

### 日時: 2026/04/22 00:24 JST (`ABC025 -> ABC024` serial edge を切り、`Main` build まで hidden import を追跡)

1. 目的:
   - 前サイクルで露出した seam をさらに進め、
     `ABC025`
     が本当に
     `ABC024`
     を必要としているかを確定する。
   - あわせて
     `Main`
     build を回し、
     次の hidden import 停止点まで owner import 化を進める。
2. 実施:
   - `ABC025.lean`
     を検索し、
     `ABC024`
     由来の symbol を使っていないことを確認した上で
     `import DkMath.ABC.ABC024`
     を削除した。
   - `ABC028`
     build で
     `markov_card_bound`
     の hidden import が露出したため、
     owner である
     `DkMath.ABC.ABC019`
     を
     `ABC028.lean`
     に direct import した。
   - 続く
     `Main`
     build では
     `ABC033`
     が停止点となり、
     `three_pow_ge_linear`
     の owner
     `DkMath.ABC.Core`
     と
     `rpow_layer_cake`
     の owner
     `DkMath.ABC.ABC022`
     を
     `ABC033.lean`
     に追加した。
3. 結論:
   - `ABC025 -> ABC024`
     の serial edge は不要だった。
   - `ABC024`-`ABC028`
     帯では、
     predecessor chain を切ったあとも
     hidden import を owner import に置き換えていけば
     public chain まで回復できることを確認した。
   - さらに
     `ABC031`-`ABC040`
     帯でも
     `ABC033`
     で同型の hidden import が露出したため、
     thematic band ごとの owner import 整理という方針が補強された。
4. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC025`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC028`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC033`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上は成功した。
   - 既知の
     `ABC021.lean`
     と
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry` 警告のみ replay された。
5. 失敗事例:
   - `ABC028`
     の first build では
     `markov_card_bound`
     未解決で停止した。
   - `Main`
     の first build では
     `ABC033`
     に
     `three_pow_ge_linear`,
     `rpow_layer_cake`
     の hidden import が露出した。
   - いずれも owner import の追加で解消した。
6. 次の課題:
   - `ABC024`-`ABC028`
     帯について、
     `ABC025`
     自身が抱えている telescoping / counting kernel を
     さらに utility 化できるかを点検する。
   - `ABC031`-`ABC040`
     帯では、
     `ABC033`
     を起点に
     `Core`
     / `ABC022`
     由来の utility を direct import へ寄せる方針で
     次の seam を探す。

### 日時: 2026/04/22 04:51 JST (`ABC033 -> ABC032` serial edge を切り、実依存を `ABC025` へ戻した)

1. 目的:
   - `ABC031`-`ABC040`
     帯の次の seam として、
     `ABC033`
     が本当に
     `ABC032`
     を必要としているかを確定する。
   - 直前 file 依存ではなく、
     実際の thematic kernel owner へ寄せられるかを確認する。
2. 実施:
   - `ABC032.lean`
     の定義を確認し、
     `abc_main` / `K_eps`
     しか持っていないことを確認した。
   - `ABC033.lean`
     を検索し、
     それらを使っていないことを確認して
     `import DkMath.ABC.ABC032`
     を削除した。
   - first build では
     `ABC.Telescoping.sum_pow_padicValNat_le_geom_log2_div_log3`
     未解決で停止したため、
     owner を検索して
     `DkMath.ABC.ABC025`
     にあることを確認し、
     `ABC033.lean`
     に
     `import DkMath.ABC.ABC025`
     を追加した。
   - 既存の
     `ABC022`
     / `Core`
     explicit import と合わせて、
     `ABC033`
     を owner import 群で閉じる形に整理した。
3. 結論:
   - `ABC033 -> ABC032`
     の serial edge は不要だった。
   - `ABC033`
     は直前の
     `ABC032`
     ではなく、
     `ABC025`
     の telescoping kernel と
     `ABC022`
     / `Core`
     utility に依存していた。
   - これは
     `ABC031`-`ABC040`
     帯に
     chain drift
     があることを示しており、
     predecessor chain より
     thematic kernel import
     を優先すべきだという方針をさらに補強した。
4. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC033`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上は成功した。
   - 既知の
     `ABC021.lean`
     と
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry` 警告のみ replay された。
5. 失敗事例:
   - `ABC033`
     の first build では
     `ABC.Telescoping.sum_pow_padicValNat_le_geom_log2_div_log3`
     未解決で停止した。
   - これは
     `ABC032`
     に依存していたのではなく、
     `ABC025`
     の transitive import に依存していたことを示していた。
   - owner import を
     `ABC025`
     に差し替えることで解消した。
6. 次の課題:
   - `ABC034` 以降についても、
     本当に直前 file の API だけを使っているのか、
     あるいは
     `ABC033`
     やさらに前の kernel に drift しているのかを点検する。
   - 可能なら
     `ABC033`
     周辺の Chernoff kernel を thin utility module に再配置する構想も検討する。

### 日時: 2026/04/22 05:09 JST (`ABC090 -> ABC040` empty relay edge を切り、最小環境 import に落とした)

1. 目的:
   - `ABC031`-`ABC040`
     帯の整理と並行して、
     その先で public chain を受けている
     `ABC090`
     の import が本当に必要かを確認する。
   - 空 shell file が serial relay を引いているだけなら、
     最小環境 import へ落として chain を短くする。
2. 実施:
   - `ABC090.lean`
     を確認し、
     実質的に空の shell file であることを確認した。
   - top-level の
     `import DkMath.ABC.ABC040`
     を削除した。
   - first build では、
     option / namespace 解決に必要な環境まで失われたため停止した。
   - そのため
     `ABC040`
     の代わりに最小環境として
     `import DkMath.ABC.Basic`
     を追加した。
3. 結論:
   - `ABC090 -> ABC040`
     の serial edge は不要だった。
   - `ABC090`
     は thematic kernel にも依存しておらず、
     最小環境 import だけで十分な shell file だった。
   - これは
     empty relay
     を経由しているだけの file 群について、
     `ABC.Basic`
     への縮約という別種の cut が有効なことを示している。
4. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC090`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上は成功した。
   - 既知の
     `ABC021.lean`
     と
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry` 警告のみ replay された。
5. 失敗事例:
   - `ABC090`
     から import を完全に外した first build では、
     `linter.style.*`,
     `BigOperators`,
     `Real`,
     `MeasureTheory`
     などの環境が未解決となった。
   - これは
     `ABC040`
     が theorem owner ではなく、
     単に環境提供の役を transitively 果たしていたことを示していた。
   - `ABC.Basic`
     を direct import することで解消した。
6. 次の課題:
   - `ABC034`-`ABC039`
     の実依存が
     truly serial
     なのか、
     あるいは
     `ABC033`
     / `ABC025`
     / utility 群への drift を含んでいるのかをさらに点検する。
   - あわせて
     `ABC040`
     自体が空 relay のまま残るべきか、
     あるいは別整理対象として扱うかを判断する。

### 日時: 2026/04/22 05:49 JST (`ABC038 -> ABC037` serial edge を切り、`ABC039` の branch 依存を露出)

1. 目的:
   - `ABC034`-`ABC039`
     帯が本当に直列なのかをさらに確認する。
   - 特に
     `ABC038`
     が
     `ABC037`
     を必要としているのか、
     それとももっと前の owner に直接依存しているだけなのかを切り分ける。
2. 実施:
   - `ABC038.lean`
     を検索し、
     `bad_set_density_bound_quality`
     や
     `construct_HΛ_for_quality`
     を使っていないことを確認した。
   - `ABC038.lean`
     の import を
     `DkMath.ABC.ABC037`
     から
     `DkMath.ABC.ABC036`
     へ置換した。
   - `ABC038`
     単体 build は成功した。
   - 続く
     `ABC039`
     build では
     `bad_set_density_bound_quality`
     未解決で停止したため、
     owner を確認して
     `DkMath.ABC.ABC037`
     にあることを特定し、
     `ABC039.lean`
     に direct import を追加した。
3. 結論:
   - `ABC037 -> ABC038`
     の serial edge は不要だった。
   - 一方で
     `ABC039`
     は
     `ABC038`
     の quality 側 API と、
     `ABC037`
     の density 側 API の両方を使っていた。
   - したがって
     `ABC031`-`ABC040`
     帯は一本の predecessor chain ではなく、
     quality branch と density branch が途中で分岐して再合流する構造だと分かった。
4. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC038`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC039`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上は成功した。
   - 既知の
     `ABC021.lean`
     と
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry` 警告のみ replay された。
5. 失敗事例:
   - `ABC039`
     の first build では
     `bad_set_density_bound_quality`
     未解決で停止した。
   - これは
     `ABC038`
     を通して transitively 見えていた
     `ABC037`
     owner の symbol だった。
   - `ABC039`
     に
     `import DkMath.ABC.ABC037`
     を追加することで解消した。
6. 次の課題:
   - `ABC034`-`ABC037`
     の前半についても、
     直前 file 依存が本物か、
     それとも
     `ABC033`
     owner 群への drift を含むかを点検する。
   - `quality branch` と `density branch` を意識した
     thin utility band
     の再配置案を検討する。

### 日時: 2026/04/22 06:18 JST (`ABC035 -> ABC036` serial edge を切り、single-prime / union-bound 分岐を確認)

1. 目的:
   - `ABC034`-`ABC037`
     前半の直列 import が本物かを確認する。
   - 特に
     `ABC036`
     が
     `ABC035`
     の union-bound layer を必要としているのか、
     それとも
     `ABC034`
     の single-prime Chernoff kernel にだけ依存しているのかを切り分ける。
2. 実施:
   - `ABC036.lean`
     を検索し、
     `chernoff_single_prime_explicit`,
     `union_bound_chernoff`,
     `union_bound_chernoff_pow`
     を使っていないことを確認した。
   - 一方で
     `chernoff_single_prime_uniform_rpow`
     は直接使っていることを確認した。
   - `ABC036.lean`
     の import を
     `DkMath.ABC.ABC035`
     から
     `DkMath.ABC.ABC034`
     へ置換した。
3. 結論:
   - `ABC035 -> ABC036`
     の serial edge は不要だった。
   - `ABC034`
     は
     single-prime Chernoff kernel の owner として機能し、
     `ABC035`
     はその上に乗る union-bound branch だと見なすのが自然だと分かった。
   - したがって
     `ABC031`-`ABC040`
     帯は
     density / quality
     だけでなく、
     `ABC034`
     を起点にした
     single-prime branch と union-bound branch
     も区別して見るべき構造になっている。
4. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC036`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC037`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上は成功した。
   - 既知の
     `ABC021.lean`
     と
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry` 警告のみ replay された。
5. 次の課題:
   - `ABC034`
     自体の owner をさらに分解できるか、
     つまり
     `ABC033`
     から single-prime Chernoff kernel を薄い utility module として切り出せるかを検討する。
   - `ABC035`
     が
     `ABC034`
     の上に乗る
     union-bound branch
     として独立した seed file になれるかを点検する。

### 日時: 2026/04/22 06:58 JST (`ABC033` の Chernoff kernel を utility module 化)

1. 目的:
   - `ABC034`
     が依存している
     single-prime Chernoff kernel
     を、
     番号付き file
     `ABC033`
     から切り離して thematic utility に落とす。
   - これにより
     `ABC033 -> ABC034`
     の serial edge を切り、
     `ABC034`
     帯の seed を
     non-numbered owner module
     に載せ替える。
2. 実施:
   - `ABC033.lean`
     の内容を新 file
     `DkMath.ABC.ChernoffSinglePrime`
     として切り出した。
   - 旧
     `ABC033.lean`
     は
     `import DkMath.ABC.ChernoffSinglePrime`
     のみを持つ
     compatibility relay
     に縮小した。
   - `ABC034.lean`
     の import を
     `DkMath.ABC.ABC033`
     から
     `DkMath.ABC.ChernoffSinglePrime`
     へ置換した。
   - first build では
     relay 化した
     `ABC033.lean`
     の header comment が壊れて失敗したため、
     comment delimiter を修正して再 build した。
3. 結論:
   - `ABC033 -> ABC034`
     の serial edge は不要だった。
   - `ABC033`
     は theorem owner というより、
     Chernoff single-prime kernel の実装コンテナだったので、
     非連番 utility module 化するのが依存構造に合っていた。
   - この帯では
     `single-prime branch`
     を番号付き predecessor chain から切り出し、
     thematic utility
     へ昇格させるパターンが有効だと確認できた。
4. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ChernoffSinglePrime`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC033`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC034`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上は成功した。
   - 既知の
     `ABC021.lean`
     と
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry` 警告のみ replay された。
5. 失敗事例:
   - relay 化した
     `ABC033.lean`
     の comment header が
     `/- ... -/`
     ではなく
     `- ... -/`
     に崩れ、
     `unexpected token '-'`
     で停止した。
   - header を修正した後は build が通った。
6. 次の課題:
   - `ChernoffSinglePrime`
     の中で、
     truly common な
     notation / constants / Markov lemma
     と
     MGF / engine 部分
     をさらに二層に割れるかを点検する。
   - `ABC035`
     以降の union-bound branch が、
     新 utility owner を前提に
     さらに薄くなるかを確かめる。

### 日時: 2026/04/22 06:58 JST (`ChernoffSinglePrime` を `basic + engine` に分割)

1. 目的:
   - utility 化した
     `ChernoffSinglePrime`
     の中をさらに薄くし、
     notation/constants/Markov
     と
     MGF / engine
     の owner を分ける。
   - これにより
     Chernoff 系 utility の再利用境界を明確にし、
     `ABC034` / `ABC035` / `ABC036`
     以降が
     どこまで basic layer だけで済むかを見やすくする。
2. 実施:
   - 新 file
     `DkMath.ABC.ChernoffBasic`
     を追加した。
   - ここへ
     `Vp`, `Excess`, `pge3`, `const_C`, `const_X`, `primesUpTo`,
     `prime_mem_primesUpTo_of_dvd_odd`,
     `card_filter_le_exp_markov`,
     `t_bound_log2_div_log3`,
     `absorb_constant_4_to_5`
     などを移した。
   - `ChernoffSinglePrime.lean`
     は
     `ChernoffBasic`
     を import する形にして、
     `mgf_padic_excess_bound_uniform`,
     `mgf_padic_excess_bound_explicit`,
     `mgf_padic_excess_bound`,
     `chernoff_engine`
     のみを保持する file へ縮小した。
3. 結論:
   - `ChernoffSinglePrime`
     は
     MGF / engine owner、
     `ChernoffBasic`
     は
     notation/constants/Markov owner
     として分離できた。
   - したがって
     `thin base + thematic utility`
     の整理は、
     `ABC0**`
     から utility module を起こす段だけでなく、
     utility module 自体を
     `basic + engine`
     に分解する段まで進められると確認できた。
4. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ChernoffBasic`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ChernoffSinglePrime`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC034`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上は成功した。
   - 途中で
     `ChernoffBasic`
     の style warning を 2 箇所修正し、
     最後に
     `DkMath.ABC.ChernoffBasic`
     を再 build して warning が消えたことも確認した。
   - 既知の
     `ABC021.lean`
     と
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry` 警告のみ replay された。
5. 次の課題:
   - `ABC034`
     がまだ local に持っている
     single-prime Chernoff proof 本体を、
     `ChernoffSinglePrime`
     の convenience theorem としてどこまで吸い上げられるかを検討する。
   - `ABC035`
     の union-bound branch についても、
     `ChernoffBasic`
     への依存と
     `ChernoffSinglePrime`
     への依存を切り分け、
     branch の境界をさらに明確化する。

### 日時: 2026/04/22 07:00 JST (`ABC034` の single-prime convenience 層を utility owner へ移設)

1. 目的:
   - `ChernoffBasic`
     と
     `ChernoffSinglePrime`
     の二層化を受けて、
     まだ
     `ABC034`
     に残っている
     single-prime convenience theorem
     を owner 側へ吸い上げる。
   - これにより
     `ABC034`
     を
     relay file
     へ降格し、
     numbered chain
     ではなく
     thematic utility
     が convenience 層まで持つ形を確定させる。
2. 実施:
   - `DkMath.ABC.ChernoffSinglePrime`
     に
     `chernoff_single_prime_uniform`
     と
     `chernoff_single_prime_uniform_rpow`
     を移した。
   - 各 proof で局所的に書いていた
     `4 -> 5`
     の吸収は、
     すでに
     `ChernoffBasic`
     にある
     `absorb_constant_4_to_5`
     を使う形へ整理した。
   - `ABC034.lean`
     は全文を縮小し、
     `import DkMath.ABC.ChernoffSinglePrime`
     と
     `#print`
     だけを持つ compatibility relay にした。
3. 結論:
   - single-prime branch の convenience 層は
     `ABC034`
     ではなく
     `ChernoffSinglePrime`
     が owner になった。
   - したがって
     `ABC034`
     は
     branch seed
     ですらなく、
     互換入口としてだけ残すのが自然だと確認できた。
   - これは
     `ABC0**`
     の chain cut が、
     import 置換だけでなく
     theorem owner の移設と relay 化まで進められることを示す。
4. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC034`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC035`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC036`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上は成功した。
   - `Main`
     build では
     `ABC038Bridge`
     まで含めて通ることを確認した。
   - 既知の
     `ABC021.lean`
     と
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry` 警告のみ replay された。
5. 次の課題:
   - `ABC035`
     の union-bound convenience 層も、
     `ChernoffSinglePrime`
     と同様に
     thematic owner
     へ寄せられるかを点検する。
   - `ABC034` / `ABC035` / `ABC036`
     の branch 分離を踏まえ、
     Chernoff 系帯の
     convenience theorem
     をどこまで非連番 utility へ吸い上げられるかを整理する。

### 日時: 2026/04/22 07:08 JST (`ABC035` の union-bound convenience 層を utility owner へ移設)

1. 目的:
   - `ABC034`
     を relay 化した流れを一段進め、
     `ABC035`
     に残っている
     explicit specialization / union-bound convenience 層も
     非連番 utility owner
     へ移す。
   - これにより
     Chernoff 帯を
     `basic -> single-prime -> union-bound`
     の thematic band として見える形にし、
     `ABC033` / `ABC034` / `ABC035`
     を連続して relay 化する。
2. 実施:
   - 新 file
     `DkMath.ABC.ChernoffUnionBound`
     を追加した。
   - ここへ
     `chernoff_single_prime_explicit'`,
     `chernoff_single_prime_explicit`,
     `union_bound_chernoff`,
     `union_bound_chernoff'`,
     `union_bound_chernoff_pow`,
     `union_bound_chernoff_pow'`
     を移した。
   - `ChernoffUnionBound`
     は
     `ChernoffSinglePrime`
     を import して、
     explicit specialization と union-bound 層の owner を持つ構成にした。
   - `ABC035.lean`
     は全文を縮小し、
     `import DkMath.ABC.ChernoffUnionBound`
     と
     `#print`
     だけを持つ compatibility relay にした。
3. 結論:
   - Chernoff 帯の
     union-bound branch
     も
     番号 file
     ではなく
     thematic utility
     が owner になる形に整理できた。
   - これにより
     `ABC033`, `ABC034`, `ABC035`
     はいずれも
     utility owner
     に接続する relay として扱える。
   - `thin base + thematic utility`
     のパターンは、
     単発の切り出しではなく、
     branch を上へ登りながら連鎖的に適用できると確認できた。
4. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ChernoffUnionBound`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC035`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上は成功した。
   - 既知の
     `ABC021.lean`
     と
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry` 警告のみ replay された。
5. 次の課題:
   - `ABC036`
     以降の
     density / quality branch
     についても、
     `ChernoffUnionBound`
     を下位 owner としてさらに utility 化できるかを点検する。
   - とくに
     `bad_set_density_bound_param`
     が
     `ABC036`
     に残るべきか、
     それとも
     density utility
     として切り出せるかを調べる。

### 日時: 2026/04/22 07:16 JST (`ABC036` の density 層を utility owner へ移設)

1. 目的:
   - `ABC033` / `ABC034` / `ABC035`
     に続いて、
     density branch
     の owner も
     番号 file
     から外す。
   - `Bad_ε`
     と
     `bad_set_density_bound_param`
     を中心とする層を
     非連番 utility
     に昇格させ、
     downstream を
     relay 経由ではなく
     direct owner import
     に寄せる。
2. 実施:
   - 新 file
     `DkMath.ABC.ChernoffDensity`
     を追加した。
   - ここへ
     `Bad_ε`,
     `bad_iff_exists_excess`,
     `exp_one_gt_one`,
     `decidable_Bad_ε`,
     `p_lt_X_to_p_lt_X_succ`,
     `bad_set_density_bound_param`,
     `bad_set_density_bound'`
     を移した。
   - `ChernoffDensity`
     は
     `ChernoffUnionBound`
     を import して、
     bad-set / density 層の owner を持つ構成にした。
   - `ABC036.lean`
     は全文を縮小し、
     `import DkMath.ABC.ChernoffDensity`
     と
     `#print`
     だけを持つ compatibility relay にした。
   - downstream として
     `ABC037.lean`
     と
     `ABC038.lean`
     の import を
     `ABC036`
     から
     `ChernoffDensity`
     へ切り替えた。
3. 結論:
   - density branch も
     `ChernoffBasic -> ChernoffSinglePrime -> ChernoffUnionBound -> ChernoffDensity`
     という thematic band の一部として整理できた。
   - これにより
     `ABC036`
     も
     owner file
     ではなく relay file になった。
   - さらに
     chain cut
     は relay 化だけでなく、
     downstream を
     direct owner import
     へ順次付け替える段まで含めて進められると確認できた。
4. 検証:
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ChernoffDensity`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC036`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC037`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.ABC038`
   - `./lean-build.sh -v --log-level=info DkMath.ABC.Main`
   - 以上は成功した。
   - 既知の
     `ABC021.lean`
     と
     `ZsigmondyCyclotomicResearch.lean`
     の `sorry` 警告のみ replay された。
5. 次の課題:
   - `ABC037`
     に残っている
     quality-specific density 補題
     を、
     `ChernoffDensity`
     の上位 utility
     としてさらに分離できるかを点検する。
   - `ABC038`
     の
     quality / bridge branch
     についても、
     density owner
     と
     quality owner
     の境界をどこまで direct import で明示できるかを整理する。
