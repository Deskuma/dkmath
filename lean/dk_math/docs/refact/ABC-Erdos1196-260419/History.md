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
