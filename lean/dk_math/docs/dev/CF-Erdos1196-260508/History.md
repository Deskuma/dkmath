# History

cid: 69fcadff-fc5c-83a2-bd6b-5657e7fcf58a

- 時刻の打刻は `date` コマンドを使用して時間(時分秒)まで正確に行うこと。
- 新規履歴は **ファイル末尾** に追加すること。

## History Log

Archive

過去ログは、以下にアーカイブしてあります。

- [000](History-000.md)

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

### 日時: 2026/05/08 10:29 JST (調査分析と実装計画の固定)

1. 目的:
   - `Discussion.md` と前回作業 `CF-Erdos1196-260418` の記録を読み、現在のワークスペースを再調査して今回の実装計画を固定する。
2. 実施:
   - `docs/__AGENT.md` を確認し、作業ごとの `History.md` 追記と単体 build 方針を確認した。
   - `Discussion.md` を読み、今回の会話で次の一手が `ValuationFlow/Hitting.lean` と整理されていることを確認した。
   - 前回 `ImplementsPlan.md` と `History.md` 末尾を確認し、前回は Mass / Branch / ValuationFlow / ABC bridge / ABC038Bridge 公開導線まで進んだことを確認した。
   - 現在の Lean ファイル一覧と主要ファイルを調べ、`DkMath/CosmicFormula/Mass/*`, `DkMath/NumberTheory/ValuationFlow/{Basic,Primitive}.lean`, `DkMath/ABC/{MassBridge,ValuationFlowBridge}.lean` が存在することを確認した。
   - `ImplementsPlan.md` を新規作成し、今回の第一目標を finite hitting core として固定した。
3. 結論:
   - 前回 Phase A-D の再実装は不要。
   - 今回は `DkMath/NumberTheory/ValuationFlow/Hitting.lean` を第一着手点とし、finite non-overlapping hitting の質量上界を no-sorry で作る。
   - primitive set / divisibility antichain vocabulary は次段階で `PrimitiveSet` 名前空間に分離する。
4. 検証:
   - この段階では文書作成のみであり、Lean build は未実施。
5. 失敗事例:
   - sandbox 上の一部 `rg` / `tail` / `git status` が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 必要な読み取りは権限昇格付きで再実行して確認した。
6. 次の課題:
   - Phase A として `DkMath/NumberTheory/ValuationFlow/Hitting.lean` を作成する。
   - `hitSetMass_le_sourceSetMass_of_injective_assignment` 相当の有限補題を実装し、単体 build で確認する。

### 日時: 2026/05/08 10:33 JST (Phase A finite hitting core)

1. 目的:
   - Erdos #1196 の primitive hitting 層へ進む前段として、有限 hit set の質量上界を Lean に固定する。
2. 実施:
   - `DkMath/NumberTheory/ValuationFlow/Hitting.lean` を新規作成した。
   - `hitSetMass` と `sourceSetMass` を `MassSpace` 上の `Finset` 和として定義した。
   - `MassControlledAssignment` を追加し、hit から source への injective assignment と各 hit の質量支配を package 化した。
   - `hitSetMass_le_sourceSetMass_of_injective_assignment` と alias `nonoverlapping_hitSetMass_le_sourceSetMass` を証明した。
   - 初回 build で `DecidableEq` の unused lint 警告が出たため、基本補題と assignment 補題の section を分離して修正した。
3. 結論:
   - finite non-overlapping hitting の最小質量上界は no-sorry で実装できた。
   - この補題を後続の primitive chain / divisibility antichain bridge の受け皿にする。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.ValuationFlow.Hitting`
   - build 成功。
5. 失敗事例:
   - 初回 build は成功したが、`hitSetMass_empty` などに不要な `[DecidableEq α]` が入った lint 警告が出た。
   - section を分離し、再 build で警告なしの成功を確認した。
6. 次の課題:
   - Phase B として `DkMath/NumberTheory/PrimitiveSet/Basic.lean` を作成し、finite primitive set を divisibility antichain として定義する。

### 日時: 2026/05/08 10:36 JST (Phase B primitive set vocabulary)

1. 目的:
   - finite primitive set を divisibility antichain として扱うための基本語彙を追加する。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/Basic.lean` を新規作成した。
   - `PrimitiveOn S := ∀ a b ∈ S, a ∣ b -> a = b` を定義した。
   - `PrimitiveOn.eq_of_dvd`, `PrimitiveOn.pair_eq_of_dvd`, `PrimitiveOn.not_dvd_of_ne`, `PrimitiveOn.dvd_iff_eq` を追加した。
   - `primitiveOn_empty`, `primitiveOn_singleton`, `primitiveOn_pair`, `primitiveOn_pair_two_three` を追加した。
   - 初回 build で `simp at` の flexible lint 警告が出たため、`simp only [Finset.mem_singleton]` と `simp only [Finset.mem_insert, Finset.mem_singleton]` に置き換えた。
3. 結論:
   - Erdos #1196 の primitive 条件を有限 `Finset ℕ` 上の divisibility antichain として参照できるようになった。
   - `0` の扱いは定義コメントに明示し、定義側では除外しない方針にした。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.Basic`
   - build 成功。
5. 失敗事例:
   - 初回 build は成功したが、`simp at hx hy` が flexible lint にかかった。
   - membership simplification を `simp only` で固定して解消した。
6. 次の課題:
   - Phase C として `DkMath/NumberTheory/PrimitiveSet/HittingBridge.lean` を追加し、primitive set と divisibility chain の交差が高々一点であることを finite hitting 側へ接続する。

### 日時: 2026/05/08 10:39 JST (Phase C primitive hitting bridge)

1. 目的:
   - finite primitive set が同一 divisibility chain を高々一度しか hit しないことを Lean に固定し、Phase A の hitting mass bound へ接続する。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/HittingBridge.lean` を新規作成した。
   - `DivisibilityChain C := ∀ a b ∈ C, a ∣ b ∨ b ∣ a` を定義した。
   - `primitiveOn_inter_chain_card_le_one` を証明し、`PrimitiveOn S` と `DivisibilityChain C` から `(S ∩ C).card ≤ 1` を得た。
   - pointwise 版 `primitiveOn_eq_of_mem_inter_chain` を追加した。
   - `primitive_chain_hitSetMass_le_single_source` を追加し、`S ∩ C` の全 hit を singleton source に割り当てる形で `hitSetMass <= sourceSetMass` へ接続した。
   - concrete sample として `divisibilityChain_two_four_eight` と `primitive_two_three_hits_two_four_eight_card_le_one` を追加した。
3. 結論:
   - `primitive -> same chain hit at most once -> finite hit mass bound` の最小 bridge が no-sorry で実装できた。
   - これで Erdos #1196 本体の前段となる finite combinatorial spine が一段進んだ。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.HittingBridge`
   - build 成功。
5. 失敗事例:
   - なし。
6. 次の課題:
   - 複数 chain / forest へ拡張するか、または actual descent relation を導入するかを判断する。
   - public import 導線は、NumberTheory 側の集約ファイル方針を確認してから追加する。

### 日時: 2026/05/08 15:19 JST (multi-chain / forest finite layer)

1. 目的:
   - `review/review-001.md` の次ステップ提案に従い、single chain の primitive hitting を finite chain family / forest へ拡張する。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/HittingBridge.lean` に `DescentChain` を追加した。
     現段階では `DivisibilityChain` の abbrev とし、actual descent step relation は後段へ温存した。
   - `DivisibilityChainFamily ι` を追加し、有限 index set と `ι -> Finset ℕ` の chain family を package 化した。
   - `DivisibilityChainFamily.hitMass` と `DivisibilityChainFamily.sourceMass` を追加し、indexed family 上の hit/source mass を定義した。
   - `DivisibilityChainFamily.primitiveOn_inter_chain_card_le_one` を追加し、各 chain で primitive set が高々一度しか hit しないことを family API から参照できるようにした。
   - `DivisibilityChainFamily.primitive_hitMass_le_sourceMass` を追加し、各 chain ごとの singleton source mass bound を indexed sum に束ねた。
   - concrete sample として `sampleBoolChainFamily`, `unitNatMassSpace`, `primitive_two_three_sampleBoolChainFamily_hitMass_le_sourceMass` を追加した。
3. 結論:
   - `primitive -> chain family hit at most once per chain -> indexed hit mass <= indexed source mass` の finite forest layer が no-sorry で実装できた。
   - actual descent relation へ進む前に必要な multi-chain wrapper は最小形で閉じた。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.HittingBridge`
   - build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で新規・更新 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - なし。
6. 次の課題:
   - `DescentStep` / `DescentChain` の actual relation 版を別ファイルに切るか判断する。
   - あるいは finite chain family を `SubConservative` / `Branching` へ接続し、branch から chain source mass bound を供給する API を追加する。

### 日時: 2026/05/08 16:01 JST (Phase D source-controlled forest bridge)

1. 目的:
   - `review/review-002.md` の提案に従い、`DivisibilityChainFamily.primitive_hitMass_le_sourceMass` の `hmass` 仮定を毎回手で渡さず、source-controlled package から供給できるようにする。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/BranchBridge.lean` を新規作成した。
   - `SourceControlledChainFamily M ι` を追加し、`DivisibilityChainFamily ι` に `source : ι -> ℕ` と `mass_le_source` を加えた package とした。
   - `SourceControlledChainFamily.hitMass` と `SourceControlledChainFamily.sourceMass` を追加し、既存 `DivisibilityChainFamily` 側の indexed mass を wrapper として再公開した。
   - empty index 用の simp 補題を追加した。
   - `SourceControlledChainFamily.primitive_hitMass_le_sourceMass` を証明し、`mass_le_source` から既存 family theorem の `hmass` を自動供給する導線を固定した。
   - concrete sample として `sampleSourceControlledBoolChainFamily` と `primitive_two_three_sampleSourceControlledBoolChainFamily_hitMass_le_sourceMass` を追加した。
   - `DkMath/NumberTheory/PrimitiveSet.lean` を新規作成し、`Basic`, `HittingBridge`, `BranchBridge` の小さな公開集約にした。
3. 結論:
   - `primitive -> source-controlled forest -> indexed hit mass <= indexed source mass` が no-sorry で閉じた。
   - actual descent / branch monotonicity はまだ導入していないが、後で `mass_le_source` を供給するだけで既存 hitting theorem に接続できる形になった。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.BranchBridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で新規・関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - なし。
6. 次の課題:
   - `mass_le_source` を actual descent relation または `Branching` / `SubConservative` から供給する API を追加する。
   - `DkMath` top-level へ載せるかは、PrimitiveSet API の次段階が安定してから判断する。

### 日時: 2026/05/08 19:14 JST (Phase E divisibility descent provider)

1. 目的:
   - `review/review-003.md` の提案に従い、`SourceControlledChainFamily.mass_le_source` を整除下降と質量単調性から供給する provider を追加する。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/DescentBridge.lean` を新規作成した。
   - `DvdMonotoneMass M := ∀ a b, a ∣ b -> M.μ a <= M.μ b` を定義した。
   - `DvdControlledChainFamily ι` を追加し、`DivisibilityChainFamily ι` に `source : ι -> ℕ` と `chain_dvd_source` を加えた。
   - `DvdControlledChainFamily.toSourceControlled` を実装し、`DvdMonotoneMass` から `SourceControlledChainFamily.mass_le_source` を供給できるようにした。
   - `DvdControlledChainFamily.primitive_hitMass_le_sourceMass` を追加し、整除下降 provider から primitive forest bound へ直接進める wrapper を作った。
   - concrete sample として `unitNatMassSpace_dvdMonotone`, `sampleDvdControlledBoolChainFamily`, `primitive_two_three_sampleDvdControlledBoolChainFamily_hitMass_le_sourceMass` を追加した。
   - `DkMath/NumberTheory/PrimitiveSet.lean` に `DescentBridge` を import し、公開集約へ載せた。
3. 結論:
   - `h ∣ source_i` と `DvdMonotoneMass` から `mass_le_source` を自動供給する有限 descent provider が no-sorry で閉じた。
   - これにより、`primitive -> divisibility-controlled forest -> source-controlled forest -> indexed hit mass <= indexed source mass` の導線ができた。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.DescentBridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で新規・関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - なし。
6. 次の課題:
   - `PrimeDescentStep` などの actual descent step を追加するか、`Branching` / `SubConservative` から `DvdControlledChainFamily` または `SourceControlledChainFamily` を生成する bridge へ進む。

### 日時: 2026/05/08 19:23 JST (Phase F prime descent step provider)

1. 目的:
   - `review/review-004.md` の提案に従い、`n -> n / p` に対応する actual prime descent step の最小核を追加する。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/PrimeDescent.lean` を新規作成した。
   - `DvdDescentStep`, `ProperDvdDescentStep`, `PrimeDescentStep`, `PrimePowerDescentStep` を定義した。
   - `PrimeDescentStep.toDvdDescentStep` / `PrimeDescentStep.dvd_source` を証明し、prime step が既存の divisibility descent provider に接続できることを示した。
   - `PrimePowerDescentStep.toDvdDescentStep` / `PrimePowerDescentStep.dvd_source` も同様に追加した。
   - `PrimeStepControlledChainFamily` を追加し、chain の各点が source から 1-step prime descent で得られる有限 forest を package 化した。
   - `PrimeStepControlledChainFamily.toDvdControlled` と `PrimeStepControlledChainFamily.primitive_hitMass_le_sourceMass` を追加した。
   - concrete sample として `primeDescentStep_eight_four`, `primeDescentStep_nine_three`, `samplePrimeStepControlledBoolChainFamily`, `primitive_three_four_samplePrimeStepControlledBoolChainFamily_hitMass_le_sourceMass` を追加した。
   - `DkMath/NumberTheory/PrimitiveSet.lean` に `PrimeDescent` を import し、公開集約へ載せた。
3. 結論:
   - `PrimeDescentStep -> DvdControlledChainFamily -> SourceControlledChainFamily -> primitive forest bound` の導線が no-sorry で閉じた。
   - これで有限 skeleton は `n -> n / p` という actual descent step 名まで到達した。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.PrimeDescent`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で新規・関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 初回 build では Bool sample の `if True/False` が残り、`simp` と `subst` が失敗した。
   - `cases b` で Bool を直接分岐し、`simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_singleton]` を使う形へ修正して解消した。
6. 次の課題:
   - 複数 step の prime descent path を導入するか、`Branching` / `SubConservative` と接続するか判断する。
   - Markov kernel や von Mangoldt weight はまだ導入せず、finite descent skeleton の provider を増やす。

### 日時: 2026/05/08 21:25 JST (Phase G multi-step prime path)

1. 目的:
   - `review/review-005.md` の提案に従い、1-step の `PrimeDescentStep` を複数つないだ prime descent path / reachability を追加する。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/PrimePath.lean` を新規作成した。
   - `PrimeReachable n m := Relation.ReflTransGen PrimeDescentStep n m` を定義した。
   - `PrimeReachable.refl`, `PrimeReachable.single`, `PrimeReachable.trans`, `PrimeReachable.dvd_source` を追加し、multi-step prime reachability が source への整除を保つことを証明した。
   - `PrimeReachableControlledChainFamily` を追加し、chain の各点が source から zero-or-more prime steps で到達可能である有限 forest を package 化した。
   - `PrimeReachableControlledChainFamily.toDvdControlled` と `PrimeReachableControlledChainFamily.primitive_hitMass_le_sourceMass` を追加した。
   - concrete sample として `primeDescentStep_four_two`, `primeDescentStep_three_one`, `primeReachable_eight_two`, `primeReachable_nine_one`, `samplePrimeReachableControlledBoolChainFamily`, `primitive_two_five_samplePrimeReachableControlledBoolChainFamily_hitMass_le_sourceMass` を追加した。
   - `DkMath/NumberTheory/PrimitiveSet.lean` に `PrimePath` を import し、公開集約へ載せた。
3. 結論:
   - `PrimeReachable -> DvdControlledChainFamily -> SourceControlledChainFamily -> primitive forest bound` の導線が no-sorry で閉じた。
   - 有限 skeleton は one-step の `n -> n / p` から multi-step の下降路へ拡張された。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.PrimePath`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で新規・関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 初回 build では sample primitive set に `{1, 2}` を使ったため、`1 ∣ 2` により `PrimitiveOn` が成立せず失敗した。
   - sample を primitive な `{2, 5}` に差し替えて解消した。
6. 次の課題:
   - `Branching` / `SubConservative` から reachability または source-controlled forest を生成する bridge へ進むか判断する。
   - まだ Markov kernel や解析重みは導入しない。

### 日時: 2026/05/09 01:21 JST (Phase H list-shaped prime path)

1. 目的:
   - `review/review-006.md` の提案に従い、実際の list-shaped prime descent path から `DivisibilityChain` を生成する provider を追加する。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/PrimePathList.lean` を新規作成した。
   - `AdjacentPrimePath L := List.IsChain PrimeDescentStep L` を定義した。
   - `PairwiseDvdAlongList L` を定義し、list 上の任意二点が割り切り比較可能であることを表現した。
   - `AdjacentPrimePath.toDvdPath` を追加し、prime step list を divisibility descent list へ忘却できるようにした。
   - `mem_tail_dvd_head_of_isChain_dvd` を証明し、divisibility descent list の tail member が head を割ることを示した。
   - `pairwiseDvdAlongList_of_isChain_dvd` と `pairwiseDvdAlongList_of_adjacentPrimePath` を証明した。
   - `divisibilityChain_toFinset_of_adjacentPrimePath` を追加し、list-shaped prime path の node set が `DivisibilityChain` になる導線を固定した。
   - `singletonChainFamilyOfAdjacentPrimePath` を追加し、list path を singleton `DivisibilityChainFamily` として package 化できるようにした。
   - concrete sample として `adjacentPrimePath_eight_four_two`, `divisibilityChain_eight_four_two_toFinset`, `primitive_two_five_hits_eight_four_two_card_le_one` を追加した。
   - `DkMath/NumberTheory/PrimitiveSet.lean` に `PrimePathList` を import し、公開集約へ載せた。
3. 結論:
   - `List.IsChain PrimeDescentStep L -> DivisibilityChain L.toFinset` が no-sorry で閉じた。
   - これにより、実際に並んだ prime descent path から primitive hitting の chain 条件を生成できるようになった。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.PrimePathList`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で新規・関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 初回 build では tail membership が `a = y ∨ a ∈ ys` の形まで展開され、`y :: ys` の membership を要求する補題に直接渡せず失敗した。
   - `simpa only [List.mem_cons]` で tail membership に戻す中間 `have` を追加して解消した。
6. 次の課題:
   - list-shaped path を `PrimeReachableControlledChainFamily` や `DvdControlledChainFamily` へ接続する provider を追加するか判断する。
   - その後に `Branching` / `SubConservative` 接続へ進む。

### 日時: 2026/05/09 01:31 JST (Phase I list path to reachable-controlled forest)

1. 目的:
   - `review/review-007.md` の提案に従い、list-shaped prime path から `PrimeReachableControlledChainFamily` へ直接接続する provider を追加する。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/PrimePathList.lean` に `mem_reachable_from_head_of_adjacentPrimePath` を追加した。
   - 非空 list path `source :: tail` の任意 node が head `source` から `PrimeReachable` であることを再帰で証明した。
   - `singletonPrimeReachableControlledChainFamilyOfAdjacentPrimePath` を追加し、非空 list path を singleton `PrimeReachableControlledChainFamily` として package 化できるようにした。
   - concrete sample として `mem_reachable_eight_four_two_two`, `singletonPrimeReachableFamily_eight_four_two`, `primitive_two_five_singletonPrimeReachableFamily_eight_four_two_hitMass_le_sourceMass` を追加した。
3. 結論:
   - `AdjacentPrimePath (source :: tail) -> PrimeReachableControlledChainFamily Unit` の導線が no-sorry で閉じた。
   - これにより、実際の prime descent path list から primitive forest mass bound へ直接進めるようになった。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.PrimePathList`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で新規・関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 初回 build では recursive equation の `source` 名解決と tail membership の形が合わず失敗した。
   - `Relation.ReflTransGen.refl` を型から推論させ、tail membership は `simpa only [List.mem_cons]` で戻して解消した。
6. 次の課題:
   - finite path skeleton は path -> chain -> reachable-controlled forest -> primitive hit mass bound まで接続された。
   - 次は `Branching` / `SubConservative` 接続へ進むか、positive/lower-bound support の補助層を追加するか判断する。

### 日時: 2026/05/09 02:25 JST (Phase J subconservative branch bridge)

1. 目的:
   - `review/review-008.md` の提案に従い、`Branching` / `SubConservative` から path 上の質量非増加を供給する bridge を追加する。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/SubConservativeBridge.lean` を新規作成した。
   - `child_mass_le_parent_of_subconservative` を追加し、`child ∈ B.children parent` なら `M.μ child <= M.μ parent` を `SubConservative` と各質量の非負性から証明した。
   - `AdjacentBranchPath B L := List.IsChain (fun parent child => child ∈ B.children parent) L` を定義した。
   - `AdjacentBranchPath.mem_mass_le_head` を追加し、subconservative branch path の任意 node が head の質量以下であることを証明した。
   - `singletonSourceControlledChainFamilyOfAdjacentBranchPrimePath` を追加し、prime path かつ branch path である非空 list を singleton `SourceControlledChainFamily` に package 化できるようにした。
   - concrete sample として `sampleBranching_eight_four_two`, `adjacentBranchPath_eight_four_two`, `sampleBranching_eight_four_two_subConservative`, `singletonSourceControlledFamily_eight_four_two_of_subConservative`, `primitive_two_five_singletonSourceControlledFamily_eight_four_two_hitMass_le_sourceMass` を追加した。
   - `DkMath/NumberTheory/PrimitiveSet.lean` に `SubConservativeBridge` を import し、公開集約へ載せた。
3. 結論:
   - `SubConservative -> branch path mass <= source mass -> SourceControlledChainFamily -> primitive hit mass bound` の有限 bridge が no-sorry で閉じた。
   - これで finite path skeleton は Mass API の `Branching` / `SubConservative` と接続された。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.SubConservativeBridge`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で新規・関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 初回 build では theorem 呼び出しで改行付き dot notation が誤解釈され、`SourceControlledChainFamily` 値を関数適用しようとして失敗した。
   - `SourceControlledChainFamily.primitive_hitMass_le_sourceMass hS ...` の通常呼び出しへ直して解消した。
6. 次の課題:
   - finite skeleton は branch mass control まで到達したため、次は positive/lower-bound support 補助層、または複数 path family の package 化へ進むか判断する。
   - Markov kernel / 解析重みはまだ導入しない。

### 日時: 2026/05/09 05:44 JST (Phase K positive/lower-bound support)

1. 目的:
   - `review/review-009.md` の提案に従い、Erdos #1196 の `A ⊂ [x,∞)` 型の有限 support 条件を primitive 条件から分離して追加する。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/Support.lean` を新規作成した。
   - `PositiveOn S := ∀ n ∈ S, 0 < n` を定義した。
   - `LowerBoundOn x S := ∀ n ∈ S, x ≤ n` を定義した。
   - `PositiveOn.pos_of_mem`, `PositiveOn.not_mem_zero`, `LowerBoundOn.le_of_mem`, `LowerBoundOn.mono_left`, `LowerBoundOn.positiveOn_of_one_le` を追加した。
   - top-level alias として `lowerBoundOn_one_implies_positiveOn`, `not_mem_zero_of_positiveOn`, `not_mem_one_of_lowerBoundOn_two` を追加した。
   - empty / singleton / `{2,5}` の concrete support sample を追加した。
   - `DkMath/NumberTheory/PrimitiveSet.lean` に `Support` を import し、公開集約へ載せた。
3. 結論:
   - `PrimitiveOn` は純粋な divisibility antichain のまま保ちつつ、正値性や下限条件を外部仮定として参照できるようになった。
   - これにより、後続の有限 Erdos support 条件で `0` や `1` を除外する補題を直接使える。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.Support`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build / `rg` / `git diff` の一部が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 必要な build と検査は権限昇格付きで再実行し、成功または該当なしを確認した。
6. 次の課題:
   - support 条件を既存の primitive hitting sample や path family sample に必要に応じて接続する。
   - 次段階として multiple path family package を追加し、singleton path から複数 path forest へ拡張するか判断する。

### 日時: 2026/05/09 11:38 JST (Phase L multiple prime path family)

1. 目的:
   - `review/review-010.md` の提案に従い、singleton list path ではなく finite index で束ねた複数の list-shaped prime paths を既存 forest theorem へ渡せるようにする。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/PathFamily.lean` を新規作成した。
   - `AdjacentPrimePathFamily ι` を追加し、`index : Finset ι`, `source : ι -> ℕ`, `tail : ι -> List ℕ`, `isPath : ∀ i ∈ index, AdjacentPrimePath (source i :: tail i)` を package 化した。
   - `AdjacentPrimePathFamily.path` と `AdjacentPrimePathFamily.nodeSet` を追加した。
   - `AdjacentPrimePathFamily.toDivisibilityChainFamily` を追加し、各 list path の node set を既存の `DivisibilityChainFamily` へ忘却できるようにした。
   - `AdjacentPrimePathFamily.toPrimeReachableControlledChainFamily` を追加し、既存の `mem_reachable_from_head_of_adjacentPrimePath` から各 node の source からの到達可能性を供給した。
   - `AdjacentPrimePathFamily.primitive_hitMass_le_sourceMass` を追加し、multiple path family から primitive indexed hit mass bound へ直接進める wrapper を作った。
   - concrete sample として `adjacentPrimePath_nine_three_one`, `sampleAdjacentPrimePathBoolFamily`, `sampleAdjacentPrimePathBoolFamilySourceControlled`, `primitive_two_five_sampleAdjacentPrimePathBoolFamily_hitMass_le_sourceMass` を追加した。
   - `DkMath/NumberTheory/PrimitiveSet.lean` に `PathFamily` を import し、公開集約へ載せた。
3. 結論:
   - `finite family of nonempty prime paths -> PrimeReachableControlledChainFamily -> DvdControlledChainFamily -> SourceControlledChainFamily -> primitive hit mass bound` の導線が no-sorry で閉じた。
   - これにより singleton path だけでなく、複数 descent path を indexed forest として扱えるようになった。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.PathFamily`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - 初回 build 後に lint 警告を修正し、再 build で警告なしの成功を確認した。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 初回 build では `change` tactic が不要である lint 警告と、sample theorem の長い行に対する style 警告が出た。
   - `change` を削除し、sample の source-controlled family を別定義へ切り出して解消した。
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗したため、権限昇格付きで再実行した。
6. 次の課題:
   - `AdjacentPrimePathFamily` と `AdjacentBranchPath` / `SubConservative` を組み合わせ、複数 path family に対して branch 側から source mass control を供給する bridge を追加するか判断する。
   - あるいは `ErdosFinitePrimitiveInput` のような primitive + lower-bound support の入力 package を追加し、有限 Erdos theorem 文を整理する。

### 日時: 2026/05/09 11:46 JST (Phase M branch-controlled prime path family)

1. 目的:
   - `review/review-011.md` の提案に従い、multiple prime path family に `AdjacentBranchPath` / `SubConservative` による source mass control を載せる。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/BranchPathFamily.lean` を新規作成した。
   - `AdjacentBranchPrimePathFamily ι B` を追加し、`AdjacentPrimePathFamily ι` に各 indexed path が branch relation に従う条件 `isBranchPath` を加えた。
   - `AdjacentBranchPrimePathFamily.toSourceControlledChainFamily` を追加し、`SubConservative M B` と `AdjacentBranchPath.mem_mass_le_head` から `SourceControlledChainFamily M ι` を生成できるようにした。
   - `AdjacentBranchPrimePathFamily.primitive_hitMass_le_sourceMass` を追加し、branch subconservativity から multiple path family の primitive indexed hit mass bound へ直接進める wrapper を作った。
   - concrete sample として `sampleBranching_eight_nine_paths`, `adjacentBranchPath_eight_four_two_sampleBranching_eight_nine_paths`, `adjacentBranchPath_nine_three_one_sampleBranching_eight_nine_paths`, `sampleAdjacentBranchPrimePathBoolFamily`, `sampleAdjacentBranchPrimePathBoolFamilySourceControlled`, `primitive_two_five_sampleAdjacentBranchPrimePathBoolFamily_hitMass_le_sourceMass` を追加した。
   - `DkMath/NumberTheory/PrimitiveSet.lean` に `BranchPathFamily` を import し、公開集約へ載せた。
3. 結論:
   - `finite family of prime paths + branch path condition + SubConservative -> SourceControlledChainFamily -> primitive hit mass bound` の導線が no-sorry で閉じた。
   - Phase L の multiple path forest が、Phase J の branch subconservative mass control と接続された。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.BranchPathFamily`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 初回 build では `AdjacentBranchPrimePathFamily` が `extends AdjacentPrimePathFamily` により自動生成する projection `toAdjacentPrimePathFamily` と、手書きの同名定義が衝突した。
   - 手書き定義を削除し、自動 projection を使う形へ修正して解消した。
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗したため、権限昇格付きで再実行した。
6. 次の課題:
   - 次は `ErdosFinitePrimitiveInput` のような primitive + lower-bound support の入力 package を追加し、有限 Erdos theorem 文を整理するか判断する。
   - その後、Markov kernel / 解析重みへ進む前に、現在の finite skeleton の theorem-facing API を点検する。
