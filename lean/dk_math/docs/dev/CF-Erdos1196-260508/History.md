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

### 日時: 2026/05/09 11:58 JST (Phase N finite Erdos primitive input)

1. 目的:
   - `review/review-012.md` の提案に従い、primitive 条件と lower-bound support 条件を theorem-facing な有限 Erdos 入力 package としてまとめる。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/ErdosFinite.lean` を新規作成した。
   - `ErdosFinitePrimitiveInput x` を追加し、`support : Finset ℕ`, `primitive : PrimitiveOn support`, `lowerBound : LowerBoundOn x support` を package 化した。
   - `ErdosFinitePrimitiveInput.positiveOn_of_one_le`, `not_mem_zero_of_one_le`, `not_mem_one_of_two_le` を追加し、lower-bound support から正値性や `0` / `1` の除外を取り出せるようにした。
   - `ErdosFinitePrimitiveInput.branchPrimePathFamily_hitMass_le_sourceMass` を追加し、finite Erdos input の `primitive` field を `AdjacentBranchPrimePathFamily.primitive_hitMass_le_sourceMass` へ渡す theorem-facing wrapper を作った。
   - concrete sample として `erdosFinitePrimitiveInput_two_five`, `erdosFinitePrimitiveInput_two_five_positiveOn`, `erdosFinitePrimitiveInput_two_five_not_mem_one`, `erdosFinitePrimitiveInput_two_five_branchPath_hitMass_le_sourceMass` を追加した。
   - `DkMath/NumberTheory/PrimitiveSet.lean` に `ErdosFinite` を import し、公開集約へ載せた。
3. 結論:
   - `PrimitiveOn S` と `LowerBoundOn x S` を theorem の入力として一体化できた。
   - 既存の branch-controlled multiple path family bound を、finite Erdos input から直接呼べるようになった。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.ErdosFinite`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 権限昇格付きで再実行し、単体 build と aggregator build の成功を確認した。
6. 次の課題:
   - finite Erdos input を使った theorem-facing API を点検し、hit mass / source mass の表示名や wrapper を追加するか判断する。
   - Markov kernel / 解析重みへ進む前に、現時点の finite skeleton の公開 API を整理する。

### 日時: 2026/05/09 13:14 JST (Phase O finite Erdos public API wrappers)

1. 目的:
   - `review/review-013.md` の提案に従い、Markov kernel / 解析重みへ進む前に `ErdosFinitePrimitiveInput` の theorem-facing API を読みやすく整理する。
2. 実施:
   - `ErdosFinitePrimitiveInput.branchPrimePathFamilySourceControlled` を追加し、branch-controlled prime path family から得られる `SourceControlledChainFamily` に入力側の名前を付けた。
   - `ErdosFinitePrimitiveInput.branchPrimePathFamilyHitMass` を追加し、finite Erdos support が branch-controlled path family を hit する indexed mass を入力側から参照できるようにした。
   - `ErdosFinitePrimitiveInput.branchPrimePathFamilySourceMass` を追加し、対応する indexed source mass を入力側から参照できるようにした。
   - `ErdosFinitePrimitiveInput.hitMass_le_sourceMass_of_branchPrimePathFamily` を追加し、hit/source mass wrapper 名を使った theorem-facing bound を用意した。
   - concrete sample として `erdosFinitePrimitiveInput_two_five_named_hitMass_le_sourceMass` を追加した。
3. 結論:
   - `ErdosFinitePrimitiveInput` から hit mass と source mass を名前付き API として直接参照できるようになった。
   - branch-controlled 版の finite Erdos hit bound が、将来の dvd-monotone 版や Markov 版と区別しやすい名前になった。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.ErdosFinite`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 権限昇格付きで再実行し、単体 build と aggregator build の成功を確認した。
6. 次の課題:
   - finite skeleton の公開 API は一段整理されたため、次は dvd-monotone / prime-reachable 版の input wrapper を追加するか判断する。
   - あるいは Markov kernel / 解析重みの前に、現在の finite theorem 群を review して最小の rename / alias を追加する。

### 日時: 2026/05/09 14:33 JST (Phase P prime path family input wrappers)

1. 目的:
   - `review/review-014.md` の提案に従い、branch-controlled 版に加えて、dvd-monotone / prime-reachable route の theorem-facing input wrapper を追加する。
2. 実施:
   - `ErdosFinitePrimitiveInput.primePathFamilySourceControlled` を追加し、`AdjacentPrimePathFamily` から `PrimeReachableControlledChainFamily -> DvdControlledChainFamily -> SourceControlledChainFamily` へ進む route に入力側の名前を付けた。
   - `ErdosFinitePrimitiveInput.primePathFamilyHitMass` を追加し、finite Erdos support が prime path family を hit する indexed mass を入力側から参照できるようにした。
   - `ErdosFinitePrimitiveInput.primePathFamilySourceMass` を追加し、対応する indexed source mass を入力側から参照できるようにした。
   - `ErdosFinitePrimitiveInput.hitMass_le_sourceMass_of_primePathFamily` を追加し、`DvdMonotoneMass M` を仮定する prime path family 版の finite Erdos bound を用意した。
   - concrete sample として `erdosFinitePrimitiveInput_two_five_primePath_hitMass_le_sourceMass` を追加した。
3. 結論:
   - branch/subconservative route と prime-reachable/dvd-monotone route の両方を `ErdosFinitePrimitiveInput` から名前付き API として呼べるようになった。
   - 将来 Markov route を追加する際にも、route ごとに hit/source mass wrapper を並べる設計が取りやすくなった。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.ErdosFinite`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 権限昇格付きで再実行し、単体 build と aggregator build の成功を確認した。
6. 次の課題:
   - theorem-facing API は branch route と prime path route が揃ったため、次は finite theorem 群の alias / naming を最終確認する。
   - Markov kernel / 解析重みへ進む場合は、既存の `ErdosFinitePrimitiveInput` wrapper 命名に合わせて route を追加する。

### 日時: 2026/05/09 16:58 JST (Phase Q route API naming aliases)

1. 目的:
   - `review/review-015.md` の提案に従い、Markov kernel へ進む前に finite theorem-facing API の route 命名規則を固定し、必要最小限の alias を追加する。
2. 実施:
   - `ErdosFinitePrimitiveInput` namespace に route-facing API naming convention のコメントを追加した。
   - 命名規則を `<route>SourceControlled`, `<route>HitMass`, `<route>SourceMass`, `hitMass_le_sourceMass_of_<route>` と明文化した。
   - `hitMass_le_sourceMass_of_subconservativeBranchPrimePathFamily` を追加し、branch route の source control が `SubConservative M B` 由来であることを theorem 名から読める alias にした。
   - `hitMass_le_sourceMass_of_dvdMonotonePrimePathFamily` を追加し、prime path route の source control が `DvdMonotoneMass M` 由来であることを theorem 名から読める alias にした。
   - concrete sample として `erdosFinitePrimitiveInput_two_five_subconservativeBranch_alias` と `erdosFinitePrimitiveInput_two_five_dvdMonotonePrime_alias` を追加した。
3. 結論:
   - branch/subconservative route と prime/dvd-monotone route の theorem-facing API に、短い route 名と根拠明示 alias の両方を用意できた。
   - 今後 Markov route を追加する場合も、同じ命名規則へ載せやすくなった。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.ErdosFinite`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 権限昇格付きで再実行し、単体 build と aggregator build の成功を確認した。
6. 次の課題:
   - finite route API は一段固定されたため、次は Markov kernel / weighted path family の最小入口を検討する。
   - 解析重みを入れる前に、有限 Markov skeleton の責務を Mass API と PrimitiveSet API のどちらへ置くか判断する。

### 日時: 2026/05/09 20:45 JST (Phase R finite weighted path-family skeleton)

1. 目的:
   - `review/review-016.md` の提案に従い、解析重みや Markov kernel へ入る前の有限重み付き path-family skeleton を追加する。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/WeightedPathFamily.lean` を新規作成した。
   - `WeightedPathFamily M ι` を追加し、`SourceControlledChainFamily M ι` に `weight : ι -> ℚ` と `weight_nonneg : ∀ i ∈ index, 0 <= weight i` を加えた。
   - `WeightedPathFamily.ofSourceControlled` を追加し、既存の source-controlled forest に非負重みを付けられるようにした。
   - `WeightedPathFamily.weightedHitMass` と `WeightedPathFamily.weightedSourceMass` を追加した。
   - `WeightedPathFamily.primitive_weightedHitMass_le_weightedSourceMass` を証明し、各 chain の primitive hit mass bound を非負重み付き有限和へ持ち上げた。
   - `ErdosFinitePrimitiveInput.weightedBranchPrimePathFamily`, `weightedBranchPrimePathFamilyHitMass`, `weightedBranchPrimePathFamilySourceMass`, `weightedHitMass_le_weightedSourceMass_of_branchPrimePathFamily` を追加し、branch-controlled route の weighted wrapper を用意した。
   - concrete sample として `sampleBoolPathWeight` と `erdosFinitePrimitiveInput_two_five_weightedBranch_hitMass_le_sourceMass` を追加した。
   - `DkMath/NumberTheory/PrimitiveSet.lean` に `WeightedPathFamily` を import し、公開集約へ載せた。
3. 結論:
   - `Σ i, w_i * hitMass_i <= Σ i, w_i * sourceMass_i` 型の有限重み付き primitive hitting bound が no-sorry で閉じた。
   - まだ解析的な Markov kernel や von Mangoldt weight には入らず、有限重み付き route の入口だけを PrimitiveSet 側に追加した。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.WeightedPathFamily`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 権限昇格付きで再実行し、単体 build と aggregator build の成功を確認した。
6. 次の課題:
   - weighted branch route に続き、必要なら prime path / dvd-monotone route の weighted wrapper を追加する。
   - Markov kernel へ進む場合は、今回の `WeightedPathFamily` を有限重み付き和の受け皿として使い、解析重みは別層に分離する。

### 日時: 2026/05/09 20:55 JST (Phase S weighted prime path route wrapper)

1. 目的:
   - `review/review-017.md` の提案に従い、weighted branch route に加えて、prime path / dvd-monotone route の weighted wrapper を追加して API を対称にする。
2. 実施:
   - `ErdosFinitePrimitiveInput.weightedPrimePathFamily` を追加し、`primePathFamilySourceControlled` で得られる source-controlled forest に非負重みを載せられるようにした。
   - `ErdosFinitePrimitiveInput.weightedPrimePathFamilyHitMass` を追加した。
   - `ErdosFinitePrimitiveInput.weightedPrimePathFamilySourceMass` を追加した。
   - `ErdosFinitePrimitiveInput.weightedHitMass_le_weightedSourceMass_of_primePathFamily` を追加し、`DvdMonotoneMass M` から得る prime path route の weighted finite Erdos bound を用意した。
   - concrete sample として `erdosFinitePrimitiveInput_two_five_weightedPrimePath_hitMass_le_sourceMass` を追加した。
3. 結論:
   - weighted route についても branch/subconservative route と prime/dvd-monotone route が揃った。
   - `WeightedPathFamily.ofSourceControlled` を共通受け皿として使い、route ごとの source control をそのまま非負重み付き和へ持ち上げられる形になった。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.WeightedPathFamily`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 権限昇格付きで再実行し、単体 build と aggregator build の成功を確認した。
6. 次の課題:
   - finite weighted route は branch 版と prime path 版が揃ったため、次は Markov kernel の最小 skeleton を検討する。
   - 解析重みを入れる場合も、まず `WeightedPathFamily` に渡す非負重みを構成する別層として設計する。

### 日時: 2026/05/09 21:33 JST (Phase T weighted normalization support)

1. 目的:
   - `review/review-018.md` の提案に従い、Markov kernel 本体へ入る前に、有限重み付き path family の正規化を語る最小補題を追加する。
2. 実施:
   - `WeightedPathFamily.totalWeight` を追加し、finite index 上の総重みを定義した。
   - `WeightedPathFamily.WeightSubProbability` を追加し、`totalWeight <= 1` を有限 sub-probability 条件として定義した。
   - `WeightedPathFamily.totalWeight_nonneg` を追加した。
   - `WeightedPathFamily.weightedSourceMass_le_const_mul_totalWeight` を追加し、各 source mass が一様に `C` 以下なら weighted source mass が `C * totalWeight` 以下であることを証明した。
   - `WeightedPathFamily.weightedSourceMass_le_const_of_subprob` を追加し、sub-probability weight かつ source mass が一様に `C` 以下なら weighted source mass が `C` 以下であることを証明した。
   - concrete sample として `sampleBoolSubprobPathWeight` と `erdosFinitePrimitiveInput_two_five_weightedBranch_sourceMass_le_one` を追加した。
3. 結論:
   - `WeightedPathFamily` に Markov kernel 前段として必要な「総重み」「sub-probability」「一様 source bound からの weighted source bound」が no-sorry で入った。
   - 解析的な重みや実数対数はまだ導入せず、有限有理重みの正規化だけを扱う層として整理できた。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.WeightedPathFamily`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 初回 build では sub-probability sample の `let W` が十分に展開されず、`totalWeight <= 1` が未解決で残った。
   - `weightedBranchPrimePathFamily`, `ofSourceControlled`, `branchPrimePathFamilySourceControlled` まで明示的に展開してから `norm_num` する形へ修正し、build を通した。
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗したため、権限昇格付きで再実行した。
6. 次の課題:
   - 次は `WeightProvider` / `FiniteKernel` のような、`WeightedPathFamily` に重みを供給する最小構造を別層として追加するか判断する。
   - Markov kernel を導入する場合も、まずは有限 index 上の非負重み provider として設計し、解析重みはさらに後段に分離する。

### 日時: 2026/05/09 21:39 JST (Phase U weighted hit mass uniform bound)

1. 目的:
   - `review/review-019.md` の提案に従い、weighted source mass の一様上界と primitive weighted hit bound を合成し、`weightedHitMass <= C` を名前付き theorem として追加する。
2. 実施:
   - `WeightedPathFamily.weightedHitMass_le_const_mul_totalWeight` を追加し、各 source mass が `C` 以下なら primitive weighted hit mass が `C * totalWeight` 以下であることを証明した。
   - `WeightedPathFamily.weightedHitMass_le_const_of_subprob` を追加し、sub-probability weight かつ各 source mass が `C` 以下なら primitive weighted hit mass が `C` 以下であることを証明した。
   - concrete sample として `erdosFinitePrimitiveInput_two_five_weightedBranch_hitMass_le_one` を追加し、`sampleBoolSubprobPathWeight` による branch weighted route の hit mass が `1` 以下であることを確認した。
3. 結論:
   - finite weighted skeleton で `weightedHitMass <= weightedSourceMass <= C` の合成が theorem-facing に使える形になった。
   - Markov kernel 前段として、sub-probability flow が一様 source bound を通じて hit mass bound を与える有限定理が no-sorry で閉じた。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.WeightedPathFamily`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 権限昇格付きで再実行し、単体 build と aggregator build の成功を確認した。
6. 次の課題:
   - 次は `WeightProvider` / `FiniteKernel` のような、`WeightedPathFamily` に重みを供給する最小構造を別層として追加するか判断する。
   - その後、Markov kernel 由来の非負重みを provider として接続する。

### 日時: 2026/05/09 21:51 JST (Phase V finite weight provider skeleton)

1. 目的:
   - `review/review-020.md` の提案に従い、`WeightedPathFamily` に直接重みを持たせるだけでなく、重みの供給元を分離する最小 provider 層を追加する。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/WeightProvider.lean` を新規作成した。
   - `WeightProvider ι` を追加し、`index : Finset ι`, `weight : ι -> ℚ`, `weight_nonneg : ∀ i ∈ index, 0 <= weight i` を package 化した。
   - `WeightProvider.totalWeight`, `WeightProvider.SubProbability`, `WeightProvider.totalWeight_nonneg` を追加した。
   - `WeightProvider.Compatible P F := P.index = F.index` を追加し、provider と `SourceControlledChainFamily` の index 互換性を明示した。
   - `WeightProvider.applyToSourceControlled` を追加し、互換な provider を source-controlled forest に適用して `WeightedPathFamily` を作れるようにした。
   - `WeightProvider.applyToSourceControlled_weightSubProbability` を追加し、provider 側の sub-probability 条件を適用後の weighted family 側へ移送できるようにした。
   - `WeightProvider.weightedHitMass_le_const_of_subprob_applyToSourceControlled` を追加し、provider 適用後の finite hit mass 一様上界を直接呼べるようにした。
   - `ErdosFinitePrimitiveInput.providerBranchPrimePathFamily` と `providerBranchPrimePathFamily_hitMass_le_const_of_subprob` を追加し、branch route に provider 由来の重みを適用する wrapper を用意した。
   - concrete sample として `sampleBoolSubprobWeightProvider`, `sampleBoolSubprobWeightProvider_subProbability`, `erdosFinitePrimitiveInput_two_five_providerBranch_hitMass_le_one` を追加した。
   - `DkMath/NumberTheory/PrimitiveSet.lean` に `WeightProvider` を import し、公開集約へ載せた。
3. 結論:
   - 重みそのものを供給する finite provider と、path/source control を持つ `SourceControlledChainFamily` を分離できた。
   - Markov kernel 由来の重みを将来追加する場合も、まず `WeightProvider` を作って `WeightedPathFamily` に適用する導線ができた。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.WeightProvider`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 初回 build では `applyToSourceControlled_weightSubProbability` で provider 側の `P.index` と適用後 weighted family 側の `F.index` の書き換えが不足し、`P.SubProbability` が目標に合わなかった。
   - `WeightedPathFamily.WeightSubProbability` と `totalWeight` を展開し、`hcompat : P.index = F.index` で明示的に書き換える形へ修正した。
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗したため、権限昇格付きで再実行した。
6. 次の課題:
   - 次は `FiniteKernel` / Markov kernel の最小構造を、`WeightProvider` を生成する層として追加するか判断する。
   - 解析重みはまだ入れず、有限 index 上の非負・sub-probability provider を返す kernel skeleton に留める。

### 日時: 2026/05/09 22:59 JST (Phase W finite kernel skeleton)

1. 目的:
   - `review/review-021.md` の提案に従い、Markov kernel 由来の重みへ進む前段として、状態ごとに `WeightProvider` を生成する有限 kernel skeleton を追加する。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/FiniteKernel.lean` を新規作成した。
   - `FiniteKernel σ ι` を追加し、`index : σ -> Finset ι`, `weight : σ -> ι -> ℚ`, `weight_nonneg : ∀ s i, i ∈ index s -> 0 <= weight s i` を package 化した。
   - `FiniteKernel.providerAt` を追加し、各 state `s` から `WeightProvider ι` を生成できるようにした。
   - `FiniteKernel.totalWeightAt`, `FiniteKernel.SubProbability`, `FiniteKernel.providerAt_subProbability`, `FiniteKernel.totalWeightAt_nonneg` を追加した。
   - `FiniteKernel.applyAtToSourceControlled` を追加し、state `s` で生成した provider を互換な `SourceControlledChainFamily` に適用できるようにした。
   - `FiniteKernel.weightedHitMass_le_const_of_subprob_applyAtToSourceControlled` を追加し、sub-probability kernel から provider 経由の weighted hit mass 一様上界へ接続した。
   - `ErdosFinitePrimitiveInput.kernelBranchPrimePathFamilyAt` と `kernelBranchPrimePathFamilyAt_hitMass_le_const_of_subprob` を追加し、branch route に finite kernel state の重みを適用する theorem-facing wrapper を用意した。
   - concrete sample として `sampleUnitFiniteKernel`, `sampleUnitFiniteKernel_subProbability`, `erdosFinitePrimitiveInput_two_five_kernelBranch_hitMass_le_one` を追加した。
   - `DkMath/NumberTheory/PrimitiveSet.lean` に `FiniteKernel` を import し、公開集約へ載せた。
3. 結論:
   - `state -> WeightProvider -> WeightedPathFamily -> weightedHitMass <= C` の有限 Markov skeleton が no-sorry で閉じた。
   - まだ解析重みや実数対数は導入せず、有限有理重み kernel の抽象だけを PrimitiveSet 側へ追加した。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.FiniteKernel`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 権限昇格付きで再実行し、単体 build と aggregator build の成功を確認した。
6. 次の課題:
   - finite kernel skeleton は入ったため、次は prime path / dvd-monotone route 側にも kernel wrapper を追加するか判断する。
   - その後、有限 kernel の normalization / compatibility API を整理してから解析 weight 層へ進む。

### 日時: 2026/05/10 02:00 JST (Phase X kernel prime path route wrapper)

1. 目的:
   - `review/review-022.md` の提案に従い、finite kernel wrapper を branch route だけでなく prime path / dvd-monotone route 側にも追加して API の対称性を保つ。
2. 実施:
   - `ErdosFinitePrimitiveInput.kernelPrimePathFamilyAt` を追加し、finite kernel state から得た provider を `primePathFamilySourceControlled` に適用できるようにした。
   - `ErdosFinitePrimitiveInput.kernelPrimePathFamilyAt_hitMass_le_const_of_subprob` を追加し、`DvdMonotoneMass M` による prime path route でも kernel-supplied sub-probability weight から weighted hit mass 一様上界を得られるようにした。
   - concrete sample として `erdosFinitePrimitiveInput_two_five_kernelPrimePath_hitMass_le_one` を追加し、`sampleUnitFiniteKernel` を prime path route に適用して hit mass bound `<= 1` を確認した。
3. 結論:
   - finite kernel route についても branch/subconservative route と prime/dvd-monotone route の両方が揃った。
   - `state -> WeightProvider -> WeightedPathFamily -> weightedHitMass <= C` の導線を、二つの source-control route で対称に使えるようになった。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.FiniteKernel`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 権限昇格付きで再実行し、単体 build と aggregator build の成功を確認した。
6. 次の課題:
   - 次は `FiniteKernel.CompatibleAt` のような compatibility alias / simp API を整理するか判断する。
   - その後、状態 `n` と index `q` に意味を持たせる actual finite Markov transition skeleton へ進む。

### 日時: 2026/05/10 10:24 JST (Phase Y finite kernel compatibility API)

1. 目的:
   - `review/review-023.md` の提案に従い、actual transition skeleton へ進む前に `FiniteKernel` 周辺の compatibility API を整理する。
2. 実施:
   - `FiniteKernel.providerAt_index` と `FiniteKernel.providerAt_weight` を `[simp]` 補題として追加した。
   - `FiniteKernel.CompatibleAt K s F := (K.providerAt s).Compatible F` を追加した。
   - `FiniteKernel.compatibleAt_iff_index_eq` を追加し、`CompatibleAt` が `K.index s = F.index` と同値であることを明示した。
   - `FiniteKernel.applyAtToSourceControlledOfCompatibleAt` を追加し、`CompatibleAt` alias を使って `WeightedPathFamily` を生成できるようにした。
   - `FiniteKernel.applyAtToSourceControlledOfCompatibleAt_index` を `[simp]` 補題として追加した。
   - `FiniteKernel.weightedHitMass_le_const_of_subprob_applyAtToSourceControlledOfCompatibleAt` を追加し、`CompatibleAt` alias を使う theorem-facing bound を用意した。
3. 結論:
   - `(K.providerAt s).Compatible F` という長い仮定を `K.CompatibleAt s F` として扱えるようになった。
   - compatibility の中身が `K.index s = F.index` であることも theorem 名から参照でき、今後 actual transition skeleton を追加する際の theorem 文が軽くなる。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.FiniteKernel`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 権限昇格付きで再実行し、単体 build と aggregator build の成功を確認した。
6. 次の課題:
   - 次は状態 `n` と index `q` に意味を持たせる actual finite Markov transition skeleton を検討する。
   - 解析重みはまだ導入せず、まずは有限遷移 `state -> index -> next state` と provider / path family の接続だけを追加する。

### 日時: 2026/05/10 10:31 JST (Phase Z finite transition kernel skeleton)

1. 目的:
   - `review/review-024.md` の提案に従い、解析重みを入れずに `state -> index -> next state` を持つ actual finite transition skeleton を追加する。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/FiniteTransitionKernel.lean` を新規作成した。
   - `FiniteTransitionKernel σ ι` を追加し、`index : σ -> Finset ι`, `next : σ -> ι -> σ`, `weight : σ -> ι -> ℚ`, `weight_nonneg : ∀ s i, i ∈ index s -> 0 <= weight s i` を package 化した。
   - `FiniteTransitionKernel.toFiniteKernel` を追加し、遷移先 `next` を忘却して既存の `FiniteKernel` へ接続できるようにした。
   - `providerAt`, `totalWeightAt`, `SubProbability`, `providerAt_subProbability`, `CompatibleAt`, `compatibleAt_iff_index_eq`, `applyAtToSourceControlled` を追加した。
   - `FiniteTransitionKernel.weightedHitMass_le_const_of_subprob_applyAtToSourceControlled` を追加し、transition kernel から既存 weighted hit mass bound へ進めるようにした。
   - `ErdosFinitePrimitiveInput.transitionBranchPrimePathFamilyAt` と `transitionBranchPrimePathFamilyAt_hitMass_le_const_of_subprob` を追加し、branch route に finite transition kernel state の重みを適用する wrapper を用意した。
   - concrete sample として `sampleUnitTransitionKernel`, `sampleUnitTransitionKernel_subProbability`, `erdosFinitePrimitiveInput_two_five_transitionBranch_hitMass_le_one` を追加した。
   - `DkMath/NumberTheory/PrimitiveSet.lean` に `FiniteTransitionKernel` を import し、公開集約へ載せた。
3. 結論:
   - `state -> index -> next state` を持つ finite transition skeleton が no-sorry で入った。
   - 重み評価は `toFiniteKernel` 経由で既存の `FiniteKernel` / `WeightProvider` / `WeightedPathFamily` theorem に流せるようになった。
   - まだ `next` の数論的意味や解析 weight は入れておらず、有限抽象層として分離した。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.FiniteTransitionKernel`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 権限昇格付きで再実行し、単体 build と aggregator build の成功を確認した。
6. 次の課題:
   - 次は transition kernel の prime path / dvd-monotone route wrapper を追加して branch route と対称化するか判断する。
   - その後、状態を `ℕ`、index を除去因子として解釈する divisor / prime descent transition skeleton へ進む。

### 日時: 2026/05/10 10:40 JST (Phase AA transition prime path route wrapper)

1. 目的:
   - `review/review-025.md` の提案に従い、`FiniteTransitionKernel` の route wrapper を branch/subconservative 側だけでなく prime path / dvd-monotone 側にも追加する。
2. 実施:
   - `ErdosFinitePrimitiveInput.transitionPrimePathFamilyAt` を追加し、finite transition kernel state から得た provider を `primePathFamilySourceControlled` に適用できるようにした。
   - `ErdosFinitePrimitiveInput.transitionPrimePathFamilyAt_hitMass_le_const_of_subprob` を追加し、`DvdMonotoneMass M` による prime path route でも transition kernel の sub-probability weight から weighted hit mass 一様上界を得られるようにした。
   - concrete sample として `erdosFinitePrimitiveInput_two_five_transitionPrimePath_hitMass_le_one` を追加し、`sampleUnitTransitionKernel` を prime path route に適用して hit mass bound `<= 1` を確認した。
3. 結論:
   - finite transition kernel route についても branch route と prime path route の wrapper が揃った。
   - `FiniteTransitionKernel -> FiniteKernel -> WeightProvider -> WeightedPathFamily` の導線を、既存の二つの source-control route で対称に使えるようになった。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.FiniteTransitionKernel`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build と read-only 確認の一部が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 権限昇格付きで再実行し、単体 build、aggregator build、no-sorry 検索、差分確認を完了した。
6. 次の課題:
   - 次は状態を `ℕ`、index を除去因子または素因子候補として解釈する divisor / prime descent transition skeleton を検討する。
   - 解析 weight はまだ導入せず、まず finite transition の遷移意味と既存 descent provider との接続を薄く作る。

### 日時: 2026/05/10 10:49 JST (Phase AB divisor transition skeleton)

1. 目的:
   - `review/review-026.md` の提案に従い、状態と index を自然数に寄せ、遷移 `n -> n / q` の意味を持つ divisor transition skeleton を追加する。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/DivisorTransitionKernel.lean` を新規作成した。
   - `DivisorTransitionKernel` を追加し、`index`, `next`, `weight`, `weight_nonneg` に加えて、`index_dvd : q ∈ index n -> q ∣ n` と `next_eq_div : q ∈ index n -> next n q = n / q` を持たせた。
   - `DivisorTransitionKernel.toFiniteTransitionKernel` を追加し、divisor semantics を忘却して既存の `FiniteTransitionKernel ℕ ℕ` として使えるようにした。
   - `providerAt`, `totalWeightAt`, `SubProbability`, `CompatibleAt`, `compatibleAt_iff_index_eq` を追加し、既存 transition kernel API へ接続した。
   - `index_dvd_source`, `next_eq_div_of_mem`, `next_dvd_source` を追加し、index membership から除去因子と遷移先 divisor を取り出せるようにした。
   - concrete sample として `sampleTenDivisorTransitionKernel` を追加し、`10` から labels `2`, `5` によってそれぞれ `5`, `2` へ進むこと、および sub-probability normalized であることを確認した。
   - `DkMath/NumberTheory/PrimitiveSet.lean` に `DivisorTransitionKernel` を import し、公開集約へ載せた。
3. 結論:
   - finite transition skeleton に `n -> n / q` という数論的意味を持つ薄い層が追加された。
   - 解析重みはまだ導入せず、有限 index、除去因子、quotient next state、既存 weight provider への忘却だけに留めた。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.DivisorTransitionKernel`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - 初回 build で出た unused simp args warning を修正し、再 build では warning なしを確認した。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 権限昇格付きで再実行し、単体 build、aggregator build、no-sorry 検索、差分確認を完了した。
6. 次の課題:
   - 次は `PrimeDescentStep` と `DivisorTransitionKernel` を接続し、prime label `q` の場合に `PrimeDescentStep n (next n q)` を得る skeleton を検討する。
   - その後、prime-power label や von Mangoldt 型 weight への入口をどの層で切るか判断する。

### 日時: 2026/05/10 11:25 JST (Phase AC prime label descent bridge)

1. 目的:
   - `review/review-027.md` の提案に従い、`DivisorTransitionKernel` の prime label を既存の `PrimeDescentStep` と接続する。
2. 実施:
   - `DivisorTransitionKernel.lean` に `PrimeDescent` を import した。
   - `DivisorTransitionKernel.primeDescentStep_of_prime_label` を追加し、`q ∈ T.index n` と `Nat.Prime q` から `PrimeDescentStep n (T.next n q)` を得られるようにした。
   - 証明では `index_dvd_source` から `q ∣ n`、`next_eq_div_of_mem` から `T.next n q = n / q` を取り出し、`PrimeDescentStep` の witness として同じ `q` を使った。
   - concrete sample として `sampleTenDivisorTransitionKernel_primeDescentStep_two` と `sampleTenDivisorTransitionKernel_primeDescentStep_five` を追加した。
3. 結論:
   - divisor transition のうち label が prime であるものを、そのまま一段の prime descent として扱えるようになった。
   - `n -> n / q` の除去因子 skeleton が、既存の prime descent route に接続された。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.DivisorTransitionKernel`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 権限昇格付きで再実行し、単体 build、aggregator build、no-sorry 検索、差分確認を完了した。
6. 次の課題:
   - 次は prime-power label の接続を検討し、`q = p ^ k` の場合に `PrimePowerDescentStep n (T.next n q)` を得る skeleton を追加する。
   - その後、prime-power label が von Mangoldt 型 weight の channel になるよう、weight 層との境界を整理する。

### 日時: 2026/05/10 11:32 JST (Phase AD prime-power label descent bridge)

1. 目的:
   - `review/review-028.md` の提案に従い、`DivisorTransitionKernel` の prime-power label を既存の `PrimePowerDescentStep` と接続する。
2. 実施:
   - `DivisorTransitionKernel.primePowerDescentStep_of_primePow_label` を追加した。
   - 仮定 `q ∈ T.index n`, `Nat.Prime p`, `0 < k`, `q = p ^ k` から `PrimePowerDescentStep n (T.next n q)` を得るようにした。
   - 証明では `index_dvd_source` を `q = p ^ k` で書き換えて `p ^ k ∣ n` を作り、`next_eq_div_of_mem` を同じ等式で書き換えて `T.next n q = n / p ^ k` を作った。
   - concrete sample として `sampleTenDivisorTransitionKernel_primePowerDescentStep_two` と `sampleTenDivisorTransitionKernel_primePowerDescentStep_five` を追加した。
3. 結論:
   - divisor transition のうち label が positive prime power であるものを、一段の prime-power descent として扱えるようになった。
   - `n -> n / q` skeleton は prime label と prime-power label の両方で既存 descent route に接続された。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.DivisorTransitionKernel`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 権限昇格付きで再実行し、単体 build、aggregator build、no-sorry 検索、差分確認を完了した。
6. 次の課題:
   - 次は `IsPrimePowerLabel q := ∃ p k, Nat.Prime p ∧ 0 < k ∧ q = p ^ k` のような finite predicate を切り出すか判断する。
   - その後、prime-power label predicate を weight/channel 層へ渡すための theorem-facing API を整える。

### 日時: 2026/05/10 11:38 JST (Phase AE prime-power label predicate)

1. 目的:
   - `review/review-029.md` の提案に従い、prime-power label を直接 `(p,k)` で渡す API から、後続層が扱いやすい predicate API へ切り出す。
2. 実施:
   - `IsPrimePowerLabel q := ∃ p k, Nat.Prime p ∧ 0 < k ∧ q = p ^ k` を追加した。
   - `DivisorTransitionKernel.primePowerDescentStep_of_isPrimePowerLabel` を追加し、`q ∈ T.index n` と `IsPrimePowerLabel q` から `PrimePowerDescentStep n (T.next n q)` を得られるようにした。
   - 既存の `primePowerDescentStep_of_primePow_label` は witness `(p,k)` を明示する低レベル補題として残し、新 theorem はそれを unpack して再利用する形にした。
   - concrete sample として `sampleTenDivisorTransitionKernel_isPrimePowerLabel_two` と `sampleTenDivisorTransitionKernel_isPrimePowerLabel_five` を追加した。
   - sample の prime-power descent theorem を、新しい `IsPrimePowerLabel` wrapper 経由に切り替えた。
3. 結論:
   - prime-power label の認識を theorem 呼び出し側で `(p,k)` に展開しなくても扱えるようになった。
   - 後続の channel / weight 層は、まず `IsPrimePowerLabel q` だけを要求する形で設計できる。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.DivisorTransitionKernel`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 権限昇格付きで再実行し、単体 build、aggregator build、no-sorry 検索、差分確認を完了した。
6. 次の課題:
   - 次は `PrimePowerIndexOn T n := ∀ q ∈ T.index n, IsPrimePowerLabel q` のような index-level predicate を追加するか判断する。
   - その後、prime-power index predicate を finite transition kernel の channel / weight API に接続する。

### 日時: 2026/05/10 12:13 JST (Phase AF prime-power index predicate)

1. 目的:
   - `review/review-030.md` の提案に従い、個々の label だけでなく、state `n` の index 全体が prime-power label から成ることを表す predicate API を追加する。
2. 実施:
   - `DivisorTransitionKernel.PrimePowerIndexOn T n := ∀ q ∈ T.index n, IsPrimePowerLabel q` を追加した。
   - `DivisorTransitionKernel.PrimePowerIndexed T := ∀ n, T.PrimePowerIndexOn n` を追加した。
   - `primePowerDescentStep_of_primePowerIndexOn` を追加し、state `n` の index-level predicate から任意の indexed transition が `PrimePowerDescentStep` であることを得られるようにした。
   - `primePowerDescentStep_of_primePowerIndexed` を追加し、全状態版 predicate から同じ結論を得られるようにした。
   - concrete sample として `sampleTenDivisorTransitionKernel_primePowerIndexOn_ten` と `sampleTenDivisorTransitionKernel_primePowerIndexed` を追加した。
   - sample の prime-power descent theorem を、全状態版 `PrimePowerIndexed` wrapper 経由に切り替えた。
3. 結論:
   - 後続層は、各 theorem 呼び出しで個別に `IsPrimePowerLabel q` を渡す代わりに、kernel/state 単位の prime-power index 仮定を使えるようになった。
   - finite transition の index が von Mangoldt channel 候補だけから成る、という条件を自然に表現できるようになった。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.DivisorTransitionKernel`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 権限昇格付きで再実行し、単体 build、aggregator build、no-sorry 検索、差分確認を完了した。
6. 次の課題:
   - 次は prime-power indexed kernel を構造体化するか、predicate のまま channel / weight API に渡すか判断する。
   - 構造体化する場合は `PrimePowerDivisorTransitionKernel` として `DivisorTransitionKernel` と `PrimePowerIndexed` を package 化し、既存 divisor transition API を忘却で再利用する。

### 日時: 2026/05/10 12:21 JST (Phase AG prime-power divisor transition package)

1. 目的:
   - `review/review-031.md` の提案に従い、prime-power label だけを持つ divisor transition kernel を一つの型として package 化する。
2. 実施:
   - `PrimePowerDivisorTransitionKernel` を追加し、`toDivisorTransitionKernel : DivisorTransitionKernel` と `primePowerIndexed : toDivisorTransitionKernel.PrimePowerIndexed` をまとめた。
   - `PrimePowerDivisorTransitionKernel.toFiniteTransitionKernel`, `providerAt`, `totalWeightAt`, `SubProbability`, `CompatibleAt` を追加し、既存 divisor / finite transition API へ忘却で接続した。
   - `PrimePowerDivisorTransitionKernel.primePowerDescentStep_of_mem` を追加し、package 化された kernel の任意の indexed transition が `PrimePowerDescentStep` であることを直接得られるようにした。
   - concrete sample として `sampleTenPrimePowerDivisorTransitionKernel` を追加した。
   - sample の prime-power descent theorem を、`PrimePowerDivisorTransitionKernel` package 経由に切り替えた。
3. 結論:
   - prime-power channel 条件を theorem の仮定として毎回渡すだけでなく、型として保持できるようになった。
   - 後続の channel / weight API は、`PrimePowerDivisorTransitionKernel` を入力にすることで「index は prime-power label のみ」という前提を型のフィールドとして利用できる。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.DivisorTransitionKernel`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - 初回 build では sample 側の `simp` が package を展開せず `simp made no progress` となったため、`sampleTenPrimePowerDivisorTransitionKernel` と `sampleTenDivisorTransitionKernel` を明示して修正した。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" ...` で関連 Lean ファイルに該当なしを確認した。
5. 失敗事例:
   - 通常 sandbox では build が `bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` で失敗した。
   - 権限昇格付き build の初回で sample の `simp made no progress` が出た。
   - package 展開を `simp` に明示した後、権限昇格付きで単体 build、aggregator build、no-sorry 検索、差分確認を完了した。
6. 次の課題:
   - 次は `PrimePowerDivisorTransitionKernel` に対する theorem-facing weight/channel API を設計する。
   - まだ実数対数や本物の von Mangoldt weight には入らず、まず finite toy weight または prime-power channel weight provider への接続を検討する。
