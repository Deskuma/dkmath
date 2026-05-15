# History

cid: 6a048079-4b50-83ab-84be-eea6a384ee8d

- 時刻の打刻は `date` コマンドを使用して時間(時分秒)まで正確に行うこと。
- 新規履歴は **ファイル末尾** に追加すること。

## History Log

Archive

過去ログは、以下にアーカイブしてあります。

- History
  - [Archive 000](History-000.md) ※まだありません（テンプレート）

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

---

### 日時: 2026/05/15 17:21 JST (CapacityKernel core と LogCapacityKernel bridge 追加)

1. 目的:
   - Markov kernel を直接置くのではなく、DkMath capacity kernel の正規化像として扱う Lean API の初期層を追加する。
2. 実施:
   - `DkMath.Kernel.Capacity` に `CapacityKernel`, `outgoingCost`, `outgoingCost_nonneg`, `outgoingCost_le_capacity` を追加した。
   - `DkMath.Kernel.Normalize` に `normalizedWeight`, `normalizedOutgoing`, `normalizedOutgoing_le_one`, `normalizedWeight_subProbability` を追加した。
   - `DkMath.NumberTheory.PrimitiveSet.LogCapacityKernel` に `PrimePowerWitnessProvider.logCapacityKernel` と R/log normalized sub-probability theorem を追加した。
   - `DkMath.Kernel`, `DkMath.NumberTheory.PrimitiveSet`, `DkMath` の aggregator import を更新した。
3. 結論:
   - DK-1/DK-2 の一般 capacity-kernel 層と、DK-4 の最初の prime-power log-capacity bridge が no-sorry で接続された。
4. 検証:
   - `lake build DkMath.Kernel.Capacity`
   - `lake build DkMath.Kernel.Normalize`
   - `lake build DkMath.NumberTheory.PrimitiveSet.LogCapacityKernel`
   - `lake build DkMath.Kernel`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `lake build DkMath`
5. 失敗事例:
   - 初回は `∑ b in ...` notation が新規 kernel module 内で parse されず失敗したため、core 側は explicit `Finset.sum` 形式へ寄せた。
6. 次の課題:
   - `CapacityKernel` の normalized weights を既存 `RealWeightProvider` / hitting API へ接続する DK-3 bridge を追加する。
   - von Mangoldt shadow 層として `Λ(p^k)=log p` に対応する theorem-facing 補題を設計する。

---
