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

### 日時: 2026/05/15 17:51 JST (DKMK-002 SubProbability bridge 追加)

1. 目的:
   - `CapacityKernel` の normalized weights を既存の `RealWeightProvider` / `SubProbability` API へ接続する。
2. 実施:
   - `DkMath.Kernel.SubProbability` を追加し、`normalizedRealWeightProvider` を定義した。
   - `normalizedRealWeightProvider_totalWeight` と `normalizedRealWeightProvider_subProbability` を追加し、positive-capacity parent から real sub-probability provider を得る橋を作った。
   - `PrimePowerWitnessProvider.logCapacityKernelRealWeightProvider` を追加し、local log-capacity kernel から既存 `RealWeightProvider ℕ` を供給できるようにした。
   - `logCapacityKernelRealWeightProvider_subProbability` を追加し、R/log route を provider-facing theorem として固定した。
3. 結論:
   - DK-3 の最小 bridge が no-sorry で通り、capacity kernel の normalized shadow が既存 real provider API に接続された。
4. 検証:
   - `lake build DkMath.Kernel.SubProbability`
   - `lake build DkMath.NumberTheory.PrimitiveSet.LogCapacityKernel`
   - `lake build DkMath.Kernel`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `lake build DkMath`
   - `rg -n "sorry|admit" lean/dk_math/DkMath/Kernel lean/dk_math/DkMath/NumberTheory/PrimitiveSet/LogCapacityKernel.lean`
5. 失敗事例:
   - なし。
6. 次の課題:
   - DK-5 として `VonMangoldtShadow.lean` を追加し、prime-power witness cost と von Mangoldt 型 weight の一致を theorem-facing にする。
   - 必要に応じて `CapacityKernel` core の import 最適化を検討する。

---

### 日時: 2026/05/15 18:16 JST (DKMK-003 VonMangoldtShadow 追加)

1. 目的:
   - prime-power witness 由来の `log p` channel cost を、解析的 von Mangoldt 関数へ直接進まずに theorem-facing な shadow として固定する。
2. 実施:
   - `DkMath.NumberTheory.PrimitiveSet.VonMangoldtShadow` を追加した。
   - `PrimePowerLabel.vonMangoldtLogCost` を定義し、`q = p^k` の witness が cost `Real.log p` を持つことを補題化した。
   - `PrimePowerWitnessProvider.witnessLogCost` と `vonMangoldtShadowCost` を定義し、selected sub-index 上で `W.label` の base prime log と一致することを示した。
   - `normalizedVonMangoldtShadowWeight` を定義し、`LogCapacityKernel` の cost/provider weight がこの shadow cost/weight と一致する補題を追加した。
   - `DkMath.NumberTheory.PrimitiveSet` aggregator に import を追加した。
3. 結論:
   - `log p(q)` を DkMath capacity-kernel cost としてだけでなく、Markov route 側の von-Mangoldt-like shadow として参照できる入口が no-sorry で入った。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.VonMangoldtShadow`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `lake build DkMath`
   - `rg -n "sorry|admit" lean/dk_math/DkMath/NumberTheory/PrimitiveSet/VonMangoldtShadow.lean lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean`
5. 失敗事例:
   - なし。
6. 次の課題:
   - `GlobalLogCapacityKernel` として、固定 `(n,I)` の local kernel から `n ↦ I(n)` 型の global kernel へ拡張する設計を検討する。
   - その後、Markov/sub-Markov translation layer で既存 route の `Λ(q)/log n` 表現へ接続する。

---

### 日時: 2026/05/15 20:13 JST (DKMK-004A/004 GlobalLogCapacityKernel 追加)

1. 目的:
   - DKMK-004A として cost/weight 対応表を project docs に明示する。
   - DKMK-004 として local `(n,I)` log-capacity kernel を、状態 `n > 1` 上の global kernel へ拡張する。
2. 実施:
   - `DkMath_Markov_kernel-to-ck.md` に `CapacityKernel.cost = witnessLogCost = vonMangoldtShadowCost = log(basePrimeOf)` などの対応表を追加した。
   - `DkMath.NumberTheory.PrimitiveSet.GlobalLogCapacityKernel` を追加した。
   - 親状態 `LogCapacityState := { n : ℕ // 1 < n }` を導入し、`log_capacity_pos` を補題化した。
   - `PrimePowerWitnessProvider.globalLogCapacityKernel` を定義し、外部入力 `IOf : ℕ → Finset ℕ` と `hIOf` から `CapacityKernel LogCapacityState ℕ` を構成した。
   - global kernel 由来の `RealWeightProvider` と、その `SubProbability` theorem を追加した。
3. 結論:
   - local kernel の集合ではなく、`n > 1` 状態空間上の global capacity kernel として R/log shadow route を扱える入口が no-sorry で入った。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.GlobalLogCapacityKernel`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `lake build DkMath`
   - `rg -n "sorry|admit" lean/dk_math/DkMath/NumberTheory/PrimitiveSet/GlobalLogCapacityKernel.lean lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean`
5. 失敗事例:
   - なし。
6. 次の課題:
   - Markov/sub-Markov translation layer として、global normalized shadow provider を既存 route の Markov-kernel 風表現へ接続する。
   - full divisor/channel set を選んだ場合の equality route と、selected set の inequality route を切り分ける。

---

### 日時: 2026/05/15 20:25 JST (DKMK-005 SubMarkovShadow 追加)

1. 目的:
   - selected channel route の inequality 側を、Markov 風に読める sub-Markov shadow 語彙として切り出す。
2. 実施:
   - `DkMath.NumberTheory.PrimitiveSet.SubMarkovShadow` を追加した。
   - `SubMarkovShadow.providerAt`, `totalWeightAt`, `SubProbability`, `providerAt_subProbability`, `totalWeightAt_le_one` を追加した。
   - positive-capacity な `CapacityKernel` から `SubMarkovShadow` を作る `SubMarkovShadow.ofCapacityKernel` と、その sub-probability theorem を追加した。
   - `PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow` を追加し、global log-capacity kernel の normalized shadow を sub-Markov shadow として参照できるようにした。
   - project docs に DKMK-005 の selected set / inequality route の位置づけを追記した。
3. 結論:
   - global normalized von-Mangoldt shadow provider を、full equality route とは分離した sub-Markov translation layer として no-sorry で扱えるようになった。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SubMarkovShadow`
   - `lake build DkMath.NumberTheory.PrimitiveSet.GlobalLogCapacityKernel`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `lake build DkMath`
   - `rg -n "sorry|admit" lean/dk_math/DkMath/NumberTheory/PrimitiveSet/SubMarkovShadow.lean lean/dk_math/DkMath/NumberTheory/PrimitiveSet/GlobalLogCapacityKernel.lean lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean`
5. 失敗事例:
   - なし。
6. 次の課題:
   - full channel set を選んだ場合の outgoing equality route を、sub-Markov inequality route から分離して設計する。
   - `IOf n = T.index n` 型の canonical/full channel shadow をどの module に置くか検討する。

---
