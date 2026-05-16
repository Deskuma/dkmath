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

### 日時: 2026/05/16 00:11 JST (DKMK-006A FullPrimePowerChannelSet 追加)

1. 目的:
   - full channel / equality route へ進む前に、full channel set であることの interface を分離する。
2. 実施:
   - `DkMath.NumberTheory.PrimitiveSet.FullChannelSet` を追加した。
   - `FullPrimePowerChannelSet` に `channels`, `subset_index`, `full` を持たせ、`channels_eq_index` と `mem_channels_iff` を補題化した。
   - `FullPrimePowerChannelSet.canonical` として `T.toDivisorTransitionKernel.index` 自身を full set として使う入口を追加した。
   - `PrimePowerWitnessProvider.fullGlobalLogCapacityKernel` と `fullGlobalLogCapacitySubMarkovShadow` を追加し、full channel interface から global kernel/shadow を作れるようにした。
   - project docs に DKMK-006A の位置づけを追記し、ここでは equality はまだ主張しないことを明記した。
3. 結論:
   - selected inequality route と full equality route の境界として、full channel 仕様層が no-sorry で入った。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.FullChannelSet`
   - `lake build DkMath.NumberTheory.PrimitiveSet.GlobalLogCapacityKernel`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `lake build DkMath`
   - `rg -n "sorry|admit" lean/dk_math/DkMath/NumberTheory/PrimitiveSet/FullChannelSet.lean lean/dk_math/DkMath/NumberTheory/PrimitiveSet/GlobalLogCapacityKernel.lean lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean`
5. 失敗事例:
   - なし。
6. 次の課題:
   - full channel set 上で `Σ vonMangoldtShadowCost = log n` を得るための構造仮定を設計する。
   - `T.index n` が本当に全 prime-power divisor を重複なく列挙していることを、既存 kernel 側でどこまで表現済みか確認する。

---

### 日時: 2026/05/16 00:25 JST (DKMK-006B FullChannelLogCostComplete と MarkovShadow 追加)

1. 目的:
   - full channel set 上の log-cost equality を仮定 interface として分離し、等号が得られた場合に Markov shadow へ昇格する橋を追加する。
2. 実施:
   - `DkMath.NumberTheory.PrimitiveSet.MarkovShadow` を追加し、`SubMarkovShadow` に total outgoing weight `= 1` を加えた equality 側の語彙を定義した。
   - `MarkovShadow.ofCapacityKernel` を追加し、positive-capacity kernel と `outgoingCost = capacity` から Markov shadow を作れるようにした。
   - `DkMath.NumberTheory.PrimitiveSet.FullChannelEquality` を追加した。
   - `FullChannelLogCostComplete` を定義し、full channel set 上で `Σ vonMangoldtShadowCost = log n` となることを仮定 interface として固定した。
   - `fullGlobalLogCapacityKernel_outgoingCost_eq_capacity`, `fullGlobalLogCapacityKernel_normalizedOutgoing_eq_one`, `fullGlobalLogCapacityMarkovShadow` を追加した。
   - project docs に DKMK-006B の equality interface と Markov shadow への昇格を追記した。
3. 結論:
   - full equality 本体の証明をまだ要求せずに、等号が供給された場合の Markov route への接続が no-sorry で入った。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.MarkovShadow`
   - `lake build DkMath.NumberTheory.PrimitiveSet.FullChannelEquality`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `lake build DkMath`
   - `rg -n "sorry|admit" lean/dk_math/DkMath/NumberTheory/PrimitiveSet/MarkovShadow.lean lean/dk_math/DkMath/NumberTheory/PrimitiveSet/FullChannelEquality.lean lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean`
5. 失敗事例:
   - 初回は `FullChannelLogCostComplete.outgoing_eq` 内で `C.subset_index` を state `s.1` に特殊化せず、`vonMangoldtShadowCost` の `hI` 型と合わずに失敗した。
6. 次の課題:
   - `FullChannelLogCostComplete` を証明するため、`T.index n` が全 exponent slot を埋めることを表す構造仮定を設計する。
   - `Σ log p = log n` の有限 prime-power channel 版を既存 `ValuationBudget` / `RealLog` route とどう接続するか検討する。

---

### 日時: 2026/05/16 01:00 JST (DKMK-006C FullExponentSlot 追加)

1. 目的:
   - `FullChannelLogCostComplete` を証明する前段として、full channel が全 exponent slot を埋めることを表す interface を追加する。
2. 実施:
   - `DkMath.NumberTheory.PrimitiveSet.FullExponentSlot` を追加した。
   - `NatBaseMultiplicityCompleteOn` を追加し、base-prime multiplicity が `n.factorization` と完全一致する equality 側の条件を定義した。
   - `natBaseMultiplicityBudgetOn_of_complete` を追加し、exact multiplicity が既存の selected-channel budget を含むことを示した。
   - `FullExponentSlotChannelSet` を追加し、`q ∈ C.channels n ↔ ∃ p k, p prime ∧ 1 ≤ k ∧ k ≤ n.factorization p ∧ q = p^k` という full exponent-slot 仕様を記録した。
   - `FullExponentSlotCoverage` を追加し、witness reader `basePrimeOf` の各 prime fiber が `n.factorization p` 個ちょうどあることを interface 化した。
   - project docs に DKMK-006C の位置づけを追記した。
3. 結論:
   - selected route の `≤` multiplicity から、full equality route に必要な `=` multiplicity へ進むための構造語彙が no-sorry で入った。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.FullExponentSlot`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `lake build DkMath`
   - `rg -n "sorry|admit" lean/dk_math/DkMath/NumberTheory/PrimitiveSet/FullExponentSlot.lean lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean`
5. 失敗事例:
   - なし。
6. 次の課題:
   - `FullExponentSlotCoverage` と `RealLog` / `ValuationBudget` の有限積-log 補題を接続し、`FullChannelLogCostComplete` を導く橋を設計する。
   - 必要なら label `q` ではなく explicit slot `(p,k)` 上の finite sum を経由する。

---

### 日時: 2026/05/16 01:25 JST (DKMK-006D FullChannelLogSum 追加)

1. 目的:
   - `FullExponentSlotCoverage` から `FullChannelLogCostComplete` を導く有限和/log の橋を追加する。
2. 実施:
   - `DkMath.NumberTheory.PrimitiveSet.FullChannelLogSum` を追加した。
   - `sum_log_base_eq_sum_image_multiplicity_mul_log` を追加し、有限 log 和を base-prime fiber ごとの multiplicity 和へ分解した。
   - `sum_factorization_mul_log_eq_log_nat` を追加し、`Σ v_p(n) log p = log n` を `Nat.prod_factorization_pow_eq_self` と `Real.log_prod` から証明した。
   - `fullExponentSlotCoverage_image_basePrime_eq_factorization_support` を追加し、coverage の下で base-prime image と `factorization.support` が一致することを示した。
   - `fullExponentSlotCoverage_sum_log_base_eq_log_nat` と `fullChannelLogCostComplete_of_fullExponentSlotCoverage` を追加した。
   - project docs に DKMK-006D の位置づけを追記した。
3. 結論:
   - `FullExponentSlotCoverage` が供給されれば、full-channel log-cost equality と Markov-shadow bridge まで no-sorry で到達できるようになった。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.FullChannelLogSum`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `lake build DkMath`
   - `rg -n "sorry|admit" lean/dk_math/DkMath/NumberTheory/PrimitiveSet/FullChannelLogSum.lean lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean`
5. 失敗事例:
   - なし。
6. 次の課題:
   - `FullExponentSlotCoverage` 自体を canonical/full channel enumeration から供給できるか確認する。
   - 必要なら explicit slot `(p,k)` 形式の補助 interface を追加し、coverage 証明の入力をさらに具体化する。

---

### 日時: 2026/05/16 01:50 JST (DKMK-006E FullExponentSlotBridge 追加)

1. 目的:
   - `FullExponentSlotChannelSet` から `FullExponentSlotCoverage` を導き、full exponent-slot 仕様から Markov shadow までの橋を接続する。
2. 実施:
   - `DkMath.NumberTheory.PrimitiveSet.FullExponentSlotBridge` を追加した。
   - `basePrimeOf_eq_of_prime_pow_mem` を追加し、indexed label が `q = p^k` と表される場合、witness-provider の base reader が `p` を返すことを示した。
   - `fullExponentSlotCoverage_of_fullExponentSlotChannelSet` を追加し、`FullExponentSlotChannelSet` から exact multiplicity coverage を構成した。
   - `fullChannelLogCostComplete_of_fullExponentSlotChannelSet` を追加し、DKMK-006D の log-sum bridge と合成した。
   - `fullGlobalLogCapacityMarkovShadow_of_fullExponentSlotChannelSet` を追加し、full exponent-slot 仕様から Markov shadow を直接作れる入口を置いた。
   - project docs に DKMK-006E の位置づけを追記した。
3. 結論:
   - full channel set が exponent slot 全体であることを示せば、coverage 仮定を別途置かずに Markov equality route へ到達できるようになった。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.FullExponentSlotBridge`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `lake build DkMath`
   - `rg -n "sorry|admit" lean/dk_math/DkMath/NumberTheory/PrimitiveSet/FullExponentSlotBridge.lean lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean`
5. 失敗事例:
   - なし。
6. 次の課題:
   - canonical/full channel enumeration が `FullExponentSlotChannelSet` を満たすことを、具体的な `T.index n` または専用 channel constructor から供給する。

---

### 日時: 2026/05/16 02:12 JST (DKMK-006F FullExponentSlotCanonical 追加)

1. 目的:
   - concrete reference model として、canonical exponent-slot enumeration を持つ prime-power divisor transition kernel を追加する。
2. 実施:
   - `DkMath.NumberTheory.PrimitiveSet.FullExponentSlotCanonical` を追加した。
   - `canonicalExponentSlotLabels n` を `n.factorization.support` 上の `p^k`, `1 ≤ k ≤ n.factorization p` の finite union として定義した。
   - `canonicalExponentSlotLabels_mem_iff` を追加し、canonical label set の membership を exponent-slot 仕様で特徴づけた。
   - `canonicalExponentSlotDivisorTransitionKernel` と `canonicalExponentSlotKernel` を追加した。
   - `canonicalExponentSlotWitnessProvider` と `canonicalExponentSlotFullChannelSet` を追加した。
   - `canonicalExponentSlotFullChannelSet_fullExponentSlotChannelSet` を追加し、canonical full channel set が `FullExponentSlotChannelSet` を満たすことを示した。
   - `canonicalExponentSlotMarkovShadow` を追加し、DKMK-006E の bridge により canonical route が Markov shadow へ到達する入口を置いた。
   - project docs に DKMK-006F の位置づけを追記した。
3. 結論:
   - explicit canonical exponent-slot route は、label enumeration から Markov shadow まで no-sorry で閉じた。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.FullExponentSlotCanonical`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `lake build DkMath`
   - `rg -n "sorry|admit" lean/dk_math/DkMath/NumberTheory/PrimitiveSet/FullExponentSlotCanonical.lean lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean`
5. 失敗事例:
   - `PrimePowerWitnessProvider` は data を返すため、membership 証明から直接 `rcases` して `PrimePowerLabel` を構成すると Prop elimination 制約に当たる。`canonicalExponentSlotLabel_exists` を Prop として示し、`Classical.choose` で witness を選ぶ形に切り替えた。
6. 次の課題:
   - 既存の外部 `T.index n` と `canonicalExponentSlotLabels n` の一致、または bridge 条件を設計する。
   - canonical route を theorem-facing な reference model として、既存 selected/full channel route へどう接続するか整理する。

---

### 日時: 2026/05/17 00:10 JST (DKMK-006G FullExponentSlotIndexBridge 追加)

1. 目的:
   - 任意の外部 `PrimePowerDivisorTransitionKernel` を canonical exponent-slot route へ接続する比較 interface を追加する。
2. 実施:
   - `DkMath.NumberTheory.PrimitiveSet.FullExponentSlotIndexBridge` を追加した。
   - `CanonicalExponentSlotIndex` を追加し、`T.toDivisorTransitionKernel.index n = canonicalExponentSlotLabels n` を interface 化した。
   - `CanonicalExponentSlotIndex.mem_iff` を追加し、外部 `T.index n` の membership を exponent-slot 仕様へ展開できるようにした。
   - `canonicalExponentSlotKernel_canonicalExponentSlotIndex` を追加し、DKMK-006F の reference model 自身がこの interface を満たすことを示した。
   - `fullExponentSlotChannelSet_of_canonicalExponentSlotIndex` を追加し、canonical index 条件から `FullExponentSlotChannelSet` を供給した。
   - `fullChannelLogCostComplete_of_canonicalExponentSlotIndex` と `fullGlobalLogCapacityMarkovShadow_of_canonicalExponentSlotIndex` を追加し、任意の witness provider を Markov shadow route へ接続した。
   - project docs に DKMK-006G の位置づけを追記した。
3. 結論:
   - 外部 kernel 側で `T.index n = canonicalExponentSlotLabels n` さえ示せば、その full log-capacity route は Markov shadow へ到達できるようになった。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.FullExponentSlotIndexBridge`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `lake build DkMath`
   - `rg -n "sorry|admit" lean/dk_math/DkMath/NumberTheory/PrimitiveSet/FullExponentSlotIndexBridge.lean lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean`
5. 失敗事例:
   - なし。
6. 次の課題:
   - 既存の具体的な `T.index n` が canonical index 条件を満たすか確認する。
   - 等号ではなく同型・weight-preserving bridge が必要なケースの interface を検討する。

---
