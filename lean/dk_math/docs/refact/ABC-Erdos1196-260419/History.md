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
