# FLT Primitive Packet Descent — History

## History Log

Archive

- [#01](History-01.md)

### Note

`00:00 JST` は、単に「日時不明のログ」を意味する placeholder である。実際の日時がわかり次第、適宜更新する。※コミット時間より判断。

### 日時: 2026/03/27 22:23 JST

1. 目的:
2. 実施:
3. 結論:
4. 検証:
5. 失敗事例:
6. 次の課題:

### 日時: 2026/03/29 00:08 JST

1. 目的:
   - `PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget`
     の concrete 証明を積む場所を、
     `TriominoCosmicBranchA.lean`
     本体から分離して確保する。

2. 実施:
   - 新ファイル
     `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     を追加した。
   - このファイルに
     - `PrimeGe5BranchAExceptionalExistenceMainlineTarget`
     - `primeGe5BranchAPrimitivePacketDescent_of_exceptionalMainline_and_restore`
     を置き、
     local exceptional existence theorem の concrete proof 入口を固定した。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     は
     `TriominoCosmicBranchA`
     直接 import ではなく
     `TriominoCosmicBranchAExceptional`
     を import する形へ切り替えた。

3. 結論:
   - `TriominoCosmicBranchA.lean`
     は target / bridge / route 設計を保持し、
     concrete existence proof 自体は
     `TriominoCosmicBranchAExceptional.lean`
     に積む構成が確立した。
   - これにより、
     local theorem を canonical 入口にする方針を保ったまま、
     今後の証明実装だけを分離して進められる。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `TriominoCosmicBranchAExceptional.lean`
     で
     `PrimeGe5BranchAExceptionalExistenceMainlineTarget`
     の concrete 証明スケッチを起こす。
   - ordinary branch theorem との仮定・中間結論の対応表を作り、
     例外枝専用の最小新補題だけを切り出す。

### 日時: 2026/03/29 00:22 JST

1. 目的:
   - `TriominoCosmicBranchAExceptional.lean`
     の中で、
     local mainline theorem と ordinary branch reference theorem の対応を
     proof-file 内で明示化する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     - `primeGe5BranchAExceptionalBoundaryCorePrimeExistence_on_pack_of_mainline`
     - `primeGe5BranchAExceptionalBoundaryCorePrimeExistence_on_pack_of_split`
     を追加した。
   - 前者で
     `PrimeGe5BranchAExceptionalExistenceMainlineTarget`
     から
     Branch A exceptional pack 上の
     `boundaryCyclotomicPrimeCore .right p (z-y) y`
     の prime existence を直接回収した。
   - 後者では
     `CFBRCBoundaryCorePrimeExistenceOnSplitTarget`
     を Branch A exceptional pack の right branch に評価する形を
     proof file 内に置いた。

3. 結論:
   - 新 proof file 単体でも、
     「通常枝は既存 reference theorem、
      例外枝だけ local mainline」
     という split 構図が読めるようになった。
   - 以後の concrete 証明は、
     global target を無理に先取りせず、
     Branch A exceptional pack 上の right branch を埋める作業として
     このファイル上で素直に進められる。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `PrimeGe5BranchAExceptionalExistenceMainlineTarget`
     の concrete 証明を、
     split reference の right branch 実装としてさらに薄く書き下す。
   - 必要なら
     ordinary theorem の proof skeleton
     に対応する補助補題を
     `TriominoCosmicBranchAExceptional.lean`
     側へ順次移す。

### 日時: 2026/03/29 00:31 JST

1. 目的:
   - exceptional proof file における concrete 証明の主目標を、
     `cyclotomicPrimeCore`
     ではなく
     pack-local な
     `boundaryCyclotomicPrimeCore .right`
     形へ固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `PrimeGe5BranchAExceptionalPackLocalBoundaryExistenceTarget`
     を追加した。
   - さらに
     - `primeGe5BranchAExceptionalExistenceMainline_of_packLocalBoundary`
     - `primeGe5BranchAExceptionalExistenceMainline_iff_packLocalBoundary`
     を追加し、
     mainline target と pack-local boundary target の往復橋を置いた。

3. 結論:
   - proof file で今後直接埋めるべき statement は、
     `PrimeGe5BranchAExceptionalExistenceMainlineTarget`
     そのものではなく、
     `PrimeGe5BranchAExceptionalPackLocalBoundaryExistenceTarget`
     と見てよい状態になった。
   - これにより、
     `boundaryCyclotomicPrimeCore .right p (z-y) y`
     を主目標にして concrete 証明を積み、
     最後に thin bridge で mainline へ戻す方針が固定された。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 失敗事例:
   - 一度、
     pack-local ではなく global target
     `CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget`
     へ直接上げようとして、
     `PrimeGe5CounterexamplePack`
     を要求しない型との不整合で build error が出た。
   - これは proof file の責務に合わせて
     pack-local statement へ戻すことで解消した。

6. 次の課題:
   - `PrimeGe5BranchAExceptionalPackLocalBoundaryExistenceTarget`
     を直接埋める concrete 補題
     `exceptional_right_boundary_core_prime_of_wieferich`
     相当を切る。
   - 必要なら、
     ordinary reference theorem の proof skeleton を模した
     pack-local 補助補題を
     `TriominoCosmicBranchAExceptional.lean`
     側へ追加する。

### 日時: 2026/03/29 00:39 JST

1. 目的:
   - proof file 上の pack-local target に、
     concrete missing theorem として追える名前を与える。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `ExceptionalRightBoundaryCorePrimeOfWieferichTarget`
     を追加した。
   - さらに
     - `primeGe5BranchAExceptionalPackLocalBoundaryExistence_of_namedKernel`
     - `exceptional_right_boundary_core_prime_of_wieferich_of_mainline`
     - `primeGe5BranchAExceptionalExistenceMainline_of_namedKernel`
     を追加し、
     named kernel と pack-local / mainline target の往復橋を置いた。

3. 結論:
   - `review-025`
     で想定していた
     `exceptional_right_boundary_core_prime_of_wieferich`
     相当は、
     proof file 上では
     `ExceptionalRightBoundaryCorePrimeOfWieferichTarget`
     を埋める作業として追えるようになった。
   - 以後、
     concrete 証明本体はこの named kernel を直接返す形で起こし、
     mainline target へは thin bridge で戻せばよい。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalRightBoundaryCorePrimeOfWieferichTarget`
     の concrete 証明 skeleton を
     `intro` / `rcases` レベルで新ファイルに起こす。
   - `primeGe5BranchAExceptionalBoundaryData_default`
     を入口で呼ぶ形にして、
     ordinary reference theorem との差分がどこに残るかを Lean 上で露出させる。

### 日時: 2026/03/29 00:47 JST

1. 目的:
   - named kernel
     `ExceptionalRightBoundaryCorePrimeOfWieferichTarget`
     の proof skeleton を、
     `boundaryData_default`
     を入口に使う形で新ファイルに固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `exceptional_right_boundary_core_prime_of_wieferich_of_split`
     を追加した。
   - この定理では、
     `primeGe5BranchAExceptionalBoundaryData_default`
     で
     `hp`, `hp5`, `gap_pos`, `y_pos`, `gap_coprime_right`,
     `p ∣ (z-y)`, `Wieferich`
     を一括抽出し、
     `CFBRCBoundaryCorePrimeExistenceOnSplitTarget`
     の right branch へそのまま流している。

3. 結論:
   - named kernel の本文は、
     少なくとも skeleton レベルでは
     「pack bundle 抽出 -> split reference の right branch」
     という形で書けばよいと固定された。
   - これにより、
     ordinary reference theorem との差分は
     `hSplit`
     をどう concrete に供給するか、
     そこだけにさらに集約された。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `CFBRCBoundaryCorePrimeExistenceOnSplitTarget`
     の right branch を、
     Branch A exceptional 専用の concrete theorem でどう供給するかを
     新ファイル側でさらに薄く切り出す。

### 日時: 2026/03/29 00:55 JST

1. 目的:
   - `hSplit` の right branch 供給だけを、
     proof file 上で別 target 名として切り出す。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `ExceptionalSplitRightBranchSupplyTarget`
     を追加した。
   - さらに
     - `exceptional_right_boundary_core_prime_of_wieferich_of_rightBranchSupply`
     - `exceptional_split_right_branch_supply_of_namedKernel`
     を追加し、
     named kernel と
     right branch supply の往復橋を置いた。

3. 結論:
   - exceptional proof の missing input は、
     もはや
     `CFBRCBoundaryCorePrimeExistenceOnSplitTarget`
     全体ではなく、
     `ExceptionalSplitRightBranchSupplyTarget`
     として追えるようになった。
   - したがって次に切る concrete 補題は、
     split theorem 全体を返す必要はなく、
     right branch supply だけを返せば十分だと固定された。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalSplitRightBranchSupplyTarget`
     を直接返す concrete 補題を切り、
     proof file 内の新数学をそこへ集約する。

### 日時: 2026/03/29 01:02 JST

1. 目的:
   - `ExceptionalSplitRightBranchSupplyTarget`
     自体の proof skeleton を新ファイルに直置きし、
     今後の concrete 本文の first target をさらに明示化する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `exceptional_split_right_branch_supply_of_split`
     を追加した。
   - この定理も
     `primeGe5BranchAExceptionalBoundaryData_default`
     で bundle を一括抽出し、
     `CFBRCBoundaryCorePrimeExistenceOnSplitTarget`
     の right branch へ流すだけの skeleton である。

3. 結論:
   - proof file で次に directly 埋めるべき theorem 名は、
     `ExceptionalSplitRightBranchSupplyTarget`
     を返す concrete 補題だとさらに明確になった。
   - 以後は、
     `exceptional_split_right_branch_supply_of_split`
     を reference skeleton、
     `exceptional_right_boundary_core_prime_of_wieferich_of_rightBranchSupply`
     を named-kernel bridge として使い分ければよい。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalSplitRightBranchSupplyTarget`
     を directly 返す concrete theorem を、
     skeleton ではなく local arithmetic / CFBRC exceptional input から起こす。

### 日時: 2026/03/29 01:10 JST

1. 目的:
   - `ExceptionalSplitRightBranchSupplyTarget`
     を、pack-local 段と boundary-normalized 段にさらに分離する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `ExceptionalBoundaryDataRightBranchSupplyTarget`
     を追加した。
   - さらに
     `exceptional_split_right_branch_supply_of_boundaryData`
     を追加し、
     boundary-normalized exceptional supply から
     pack-local right branch supply を回収する橋を置いた。

3. 結論:
   - concrete 証明で今後直接狙うべき new math は、
     pack を含む target そのものではなく、
     `ExceptionalBoundaryDataRightBranchSupplyTarget`
     にかなり近い形へ集約できるようになった。
   - これにより、
     pack 解体は `boundaryData_default`,
     exceptional arithmetic / CFBRC 本体は boundary-normalized theorem
     という責務分離がさらに明確になった。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDataRightBranchSupplyTarget`
     を直接返す concrete theorem を切り、
     new math の入口を boundary-normalized exceptional statement に固定する。

### 日時: 2026/03/29 00:00 JST

1. 目的:
   - proof file 上で、
     boundary-normalized exceptional statement に対する
     「次に本文を書く theorem 名」
     を固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `ExceptionalBoundaryDataRightBranchSupplyConcreteTarget`
     を追加した。
   - さらに
     - `exceptional_split_right_branch_supply_of_boundaryConcrete`
     - `exceptional_right_boundary_core_prime_of_wieferich_of_boundaryConcrete`
     - `primeGe5BranchAExceptionalExistenceMainline_of_boundaryConcrete`
     - `primeGe5BranchAPrimitivePacketDescent_of_boundaryConcrete_and_restore`
     を追加し、
     concrete theorem 名から
     pack-local / named kernel / mainline / packet descent
     への thin bridge を一通り揃えた。

3. 結論:
   - 以後、
     proof file で直接本文を書くべきものは
     `ExceptionalBoundaryDataRightBranchSupplyConcreteTarget`
     とみなしてよい。
   - 新数学の入口は引き続き
     boundary-normalized exceptional statement
     だが、
     今回の差分で
     「その入口をどの theorem 名で埋めるか」
     がファイル上でも固定された。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDataRightBranchSupplyConcreteTarget`
     を返す concrete theorem 本体を切る。
   - 必要なら ordinary reference theorem 側との差分入力だけを
     別 target にもう 1 段切る。

### 日時: 2026/03/29 00:00 JST

1. 目的:
   - boundary-normalized concrete theorem の入力を、
     split theorem の right branch と同じ形にさらに揃える。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `ExceptionalBoundaryDataSplitRightConcreteTarget`
     を追加した。
   - この target は
     `d ∣ x`
     と
     `u^(d-1) ≡ 1 [MOD d^2]`
     を
     ひとつの exceptional datum
     `(d ∣ x ∧ ...)`
     として受ける。
   - さらに
     - `exceptional_boundaryData_right_branch_supply_concrete_of_splitRight`
     - `exceptional_right_boundary_core_prime_of_wieferich_of_splitRightConcrete`
     - `primeGe5BranchAExceptionalExistenceMainline_of_splitRightConcrete`
     - `primeGe5BranchAPrimitivePacketDescent_of_splitRightConcrete_and_restore`
     を追加し、
     split-right concrete theorem 名から
     既存の concrete / named kernel / mainline / packet descent
     へ戻る橋を揃えた。

3. 結論:
   - proof file で next body を書くとき、
     必ずしも
     `ExceptionalBoundaryDataRightBranchSupplyConcreteTarget`
     を直接受ける必要はなく、
     split theorem の right branch と完全に平行な
     `ExceptionalBoundaryDataSplitRightConcreteTarget`
     を first body target にしてよい。
   - これにより、
     ordinary 側との差分入力は
     `Or.inr` 相当の exceptional datum
     1 個としてさらに局所化された。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDataSplitRightConcreteTarget`
     を返す concrete theorem 本体を切る。
   - 必要なら、その本文でも
     ordinary reference theorem と共有できる部分と
     exceptional-only arithmetic をさらに分離する。

### 日時: 2026/03/29 00:00 JST

1. 目的:
   - split-right concrete target の本文を、
     「共通入力 + exceptional datum 1 個」
     という形でさらに明示化する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `ExceptionalBoundaryDatum`
     と
     `ExceptionalBoundaryDatumConcreteTarget`
     を追加した。
   - さらに
     - `exceptional_boundaryData_splitRight_concrete_of_datum`
     - `exceptional_boundaryData_right_branch_supply_concrete_of_datum`
     - `exceptional_right_boundary_core_prime_of_wieferich_of_datumConcrete`
     - `primeGe5BranchAExceptionalExistenceMainline_of_datumConcrete`
     - `primeGe5BranchAPrimitivePacketDescent_of_datumConcrete_and_restore`
     を追加し、
     datum 形の concrete theorem 名から
     split-right / boundary concrete / named kernel / mainline / packet descent
     へ戻る橋を揃えた。

3. 結論:
   - proof file の本文は今後、
     必ずしも split-right target そのものを直接受けずとも、
     `ExceptionalBoundaryDatumConcreteTarget`
     を first body target として書いてよい。
   - これにより、
     ordinary 側との差分は theorem 名の上でも
     exceptional datum 1 個にまで局所化された。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDatumConcreteTarget`
     を返す concrete theorem 本体を切る。
   - 必要なら、
     exceptional datum から right boundary-core prime existence を導く
     arithmetic / CFBRC 補題を
     proof file 内でさらに局所化する。

### 日時: 2026/03/29 00:00 JST

1. 目的:
   - datum concrete target の本文入口を、
     theorem 名としてさらに固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `exceptional_boundary_datum_concrete_of_split`
     を追加した。
   - この定理は
     `ExceptionalBoundaryDatumConcreteTarget`
     の canonical proof skeleton であり、
     `rcases hDatum with ⟨hdvd, hWieferich⟩`
     の後に split theorem の right branch
     `Or.inr ⟨hdvd, hWieferich⟩`
     へ流すだけの形を固定する。

3. 結論:
   - proof file で次に directly 本文を書く theorem 名は引き続き
     `ExceptionalBoundaryDatumConcreteTarget`
     だが、
     その本文の canonical skeleton も
     theorem として明示された。
   - 以後の truly new math は、
     split theorem 全体ではなく
     `exceptional_boundary_datum_concrete_of_split`
     の中で
     `hSplit`
     を何で concrete に供給するか、
     その一点にさらに絞って考えられる。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDatumConcreteTarget`
     を返す concrete theorem 本体を、
     `hSplit` 供給の local arithmetic / CFBRC exceptional 補題として切る。

### 日時: 2026/03/29 00:00 JST

1. 目的:
   - `hSplit` 供給を、
     ordinary reference と exceptional datum theorem の合成として固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `cfbrcBoundaryCorePrimeExistence_split_of_reference_and_datum`
     を追加した。
   - この定理は
     - 通常枝 `Or.inl hOrd` では
       `cfbrcBoundaryCorePrimeExistence_reference`
     - 例外枝 `Or.inr hExc` では
       `ExceptionalBoundaryDatumConcreteTarget`
     を起動するだけの split assembler である。

3. 結論:
   - proof file の missing math は、
     もはや
     `CFBRCBoundaryCorePrimeExistenceOnSplitTarget`
     全体ではなく、
     `ExceptionalBoundaryDatumConcreteTarget`
     1 本だと theorem の形でもさらに明確になった。
   - `exceptional_boundary_datum_concrete_of_split`
     の中で必要な `hSplit` は、
     この assembler で供給すればよい。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDatumConcreteTarget`
     を返す concrete theorem 本体を切る。
   - 必要なら、
     datum theorem 自体の本文も
     exceptional-only arithmetic / CFBRC core
     にさらに局所化する。

### 日時: 2026/03/29 00:00 JST

1. 目的:
   - downstream 側から見て、
     datum theorem 1 本で mainline / packet descent が閉じることを
     theorem 名で固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     - `primeGe5BranchAExceptionalExistenceMainline_of_reference_and_datum`
     - `primeGe5BranchAPrimitivePacketDescent_of_reference_and_datum_and_restore`
     を追加した。
   - 前者は
     `cfbrcBoundaryCorePrimeExistence_split_of_reference_and_datum`
     と
     `exceptional_boundary_datum_concrete_of_split`
     の合成で
     proof file mainline を閉じる。
   - 後者はそこから
     restore theorem
     と既存 bridge を使って
     primitive packet descent
     まで流す thin wrapper である。

3. 結論:
   - proof file の missing math は引き続き
     `ExceptionalBoundaryDatumConcreteTarget`
     1 本であり、
     その theorem が立てば downstream は ordinary/reference 側の配線込みで
     自動的に閉じると読めるようになった。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDatumConcreteTarget`
     の concrete theorem 本体を切る。
   - 必要なら、
     その本文の中で使う exceptional-only arithmetic / CFBRC core
     だけを別 theorem に切る。

### 日時: 2026/03/29 00:00 JST

1. 目的:
   - datum concrete 本体に、
     exceptional-only arithmetic / CFBRC core
     としての固有名を与える。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `ExceptionalBoundaryDatumArithmeticCoreTarget`
     を追加した。
   - さらに
     - `exceptional_boundary_datum_concrete_of_arithmeticCore`
     - `exceptional_boundaryData_right_branch_supply_concrete_of_arithmeticCore`
     - `exceptional_right_boundary_core_prime_of_wieferich_of_arithmeticCore`
     - `primeGe5BranchAExceptionalExistenceMainline_of_arithmeticCore`
     - `primeGe5BranchAPrimitivePacketDescent_of_arithmeticCore_and_restore`
     を追加し、
     arithmetic core から
     datum concrete / boundary concrete / named kernel / mainline / packet descent
     へ戻る橋を揃えた。

3. 結論:
   - proof file の missing math は引き続き
     `ExceptionalBoundaryDatumConcreteTarget`
     の concrete 本体だが、
     今後はその本文を
     `ExceptionalBoundaryDatumArithmeticCoreTarget`
     の実装とみなして追ってよい。
   - これにより、
     “bridge ではない本当の新数学”
     に固有名が付き、
     残核の輪郭がさらに明確になった。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDatumArithmeticCoreTarget`
     の concrete theorem 本体を切る。

### 日時: 2026/03/29 00:00 JST

1. 目的:
   - proof file の datum-based wrapper を、
     できるだけ
     `ExceptionalBoundaryDatumArithmeticCoreTarget`
     を canonical 入口として読む形に寄せる。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     - `exceptional_boundary_datum_arithmetic_core_of_split`
     - `exceptional_boundary_datum_arithmetic_core_of_reference_and_datum`
     を追加した。
   - `primeGe5BranchAExceptionalExistenceMainline_of_reference_and_datum`
     は、
     datum concrete から直接 mainline へ戻すのではなく、
     `exceptional_boundary_datum_arithmetic_core_of_reference_and_datum`
     を経由して
     `primeGe5BranchAExceptionalExistenceMainline_of_arithmeticCore`
     へ流す形に直した。
   - `primeGe5BranchAPrimitivePacketDescent_of_reference_and_datum_and_restore`
     も同様に、
     arithmetic core 入口を経由して
     `...of_arithmeticCore_and_restore`
     へ流す形に直した。

3. 結論:
   - downstream は依然として datum theorem から閉じるが、
     proof file 内の canonical 読み筋は
     `ExceptionalBoundaryDatumArithmeticCoreTarget`
     を通る形にさらに揃った。
   - したがって今後の concrete 本文は、
     `exceptional_boundary_datum_arithmetic_core`
     相当の内容として追えばよい、
     という整理が theorem 配線の上でも明示された。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDatumArithmeticCoreTarget`
     の concrete theorem 本体を、
     proof file 上の canonical body として切る。

### 日時: 2026/03/29 00:00 JST

1. 目的:
   - arithmetic core の concrete 本文を、
     `hDatum` の連言をほどいた prepared 形で追えるようにする。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `ExceptionalBoundaryDatumPreparedArithmeticCoreTarget`
     を追加した。
   - さらに
     - `exceptional_boundary_datum_prepared_arithmetic_core_of_split`
     - `exceptional_boundary_datum_arithmetic_core_of_prepared`
     - `exceptional_boundary_datum_prepared_arithmetic_core_of_reference_and_datum`
     を追加し、
     split / assembler から prepared 形へ入り、
     prepared 形から canonical arithmetic core へ戻る橋を揃えた。
   - あわせて
     `primeGe5BranchAPrimitivePacketDescent_of_preparedArithmeticCore_and_restore`
     も追加し、
     prepared arithmetic core から downstream を閉じる配線を置いた。

3. 結論:
   - proof file の次の concrete body は、
     もはや
     `ExceptionalBoundaryDatumArithmeticCoreTarget`
     だけでなく、
     `hdvd`
     と
     `hWieferich`
     が分離された
     `ExceptionalBoundaryDatumPreparedArithmeticCoreTarget`
     として追ってよい。
   - したがって以後の本文は
     `rcases hDatum with ⟨hdvd, hWieferich⟩`
     の前処理を済ませた形から直接書き始められる。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDatumPreparedArithmeticCoreTarget`
     の concrete theorem 本体を切る。

### 日時: 2026/03/29 00:00 JST

1. 目的:
   - prepared arithmetic core の concrete 本文を、
     proof file 上で直接追える theorem 名として固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget`
     を追加した。
   - さらに
     - `exceptional_boundary_datum_prepared_arithmetic_core_of_concrete`
     - `exceptional_boundary_datum_arithmetic_core_of_preparedConcrete`
     - `primeGe5BranchAPrimitivePacketDescent_of_preparedConcrete_and_restore`
     を追加し、
     prepared concrete 名から
     canonical prepared target / arithmetic core / downstream
     へ戻る橋を揃えた。

3. 結論:
   - 次に本文を書くべき場所は、
     抽象 target
     `ExceptionalBoundaryDatumPreparedArithmeticCoreTarget`
     そのものでも追えるが、
     proof file 上では
     `ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget`
     を concrete theorem 名として直接追ってよい。
   - これにより、
     prepared body も theorem 名の上で canonical な着手点を持った。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget`
     の concrete theorem 本体を切る。

### 日時: 2026/03/29 00:00 JST

1. 目的:
   - prepared concrete 本体がまだ重い場合に備えて、
     その中身を
     `exceptional arithmetic`
     と
     `CFBRC existence`
     の 2 part に局所化する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     - `ExceptionalBoundaryDatumPreparedArithmeticPartTarget`
     - `ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget`
     を追加した。
   - さらに
     `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_parts`
     を追加し、
     arithmetic part が
     `Nat.Prime q ∧ ¬ q ∣ x`
     を返し、
     CFBRC existence part がその
     `q`
     の
     `boundaryCyclotomicPrimeCore .right d x u`
     可除性だけを返せば、
     prepared concrete 本体が閉じる形を固定した。

3. 結論:
   - proof file の次の concrete body は引き続き
     `ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget`
     だが、
     必要なら missing math は
     - candidate prime を取る exceptional arithmetic 部
     - boundary core divisibility を返す CFBRC existence 部
     の 2 part として追えるようになった。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDatumPreparedArithmeticPartTarget`
     または
     `ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget`
     の concrete theorem 本体を切る。

### 日時: 2026/03/29 00:00 JST

1. 目的:
   - prepared concrete theorem 名に対して、
     直接本文を書き始める canonical skeleton を固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     - `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_split`
     - `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_reference_and_datum`
     を追加した。
   - 前者では
     `intro d x u hd_prime hd_ge hx hu hcop hdvd hWieferich`
     から
     split theorem の right branch へ直接流す
     canonical skeleton を theorem 名として固定した。
   - あわせて
     - `primeGe5BranchAExceptionalExistenceMainline_of_preparedArithmeticCore`
     - `primeGe5BranchAExceptionalExistenceMainline_of_preparedConcrete`
     も追加し、
     prepared core / prepared concrete から
     mainline へ戻る橋を揃えた。

3. 結論:
   - proof file でいま直接追うべき着手点は、
     抽象 target だけでなく
     `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_split`
     という skeleton theorem 名でも読めるようになった。
   - これにより、
     prepared concrete 本体は
     theorem 名の上でも
     「どこから書き始めるか」
     がさらに明確になった。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget`
     の concrete theorem 本体を切る。

### 日時: 2026/03/29 00:00 JST

1. 目的:
   - まず攻めるべき arithmetic part について、
     proof file 上の concrete 着手点を theorem 名として固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `ExceptionalBoundaryDatumPreparedArithmeticPartConcreteTarget`
     を追加した。
   - さらに
     - `exceptional_boundary_datum_prepared_arithmetic_part_concrete_of_self`
     - `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_arithmeticConcrete_and_cfbrc`
     を追加し、
     arithmetic part の concrete 名から
     2-part assembler を通って
     prepared concrete 本体へ戻る橋を揃えた。

3. 結論:
   - 次に直接攻めるべき local kernel は、
     抽象 target
     `ExceptionalBoundaryDatumPreparedArithmeticPartTarget`
     でも読めるが、
     proof file 上では
     `ExceptionalBoundaryDatumPreparedArithmeticPartConcreteTarget`
     を concrete 着手点として追ってよい。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDatumPreparedArithmeticPartConcreteTarget`
     の concrete theorem 本体を切る。

### 日時: 2026/03/29 00:10 JST

1. 目的:
   - `ExceptionalBoundaryDatumPreparedArithmeticPartConcreteTarget`
     の concrete 本体を実装し、
     prepared concrete の残りを
     `CFBRC existence`
     1 本へさらに局所化する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `exceptional_boundary_datum_prepared_arithmetic_part_concrete`
     を追加した。
   - 証明では
     `x + 1`
     の素因子
     `q`
     を
     `Nat.exists_prime_and_dvd`
     で取り、
     もし
     `q ∣ x`
     なら
     `q ∣ ((x+1)-x) = 1`
     となることから矛盾を出した。
   - さらに
     - `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_cfbrc`
     - `primeGe5BranchAExceptionalExistenceMainline_of_cfbrcPart`
     - `primeGe5BranchAPrimitivePacketDescent_of_cfbrcPart_and_restore`
     を追加し、
     arithmetic concrete を既定値に焼き付けた wrapper を置いた。

3. 結論:
   - prepared concrete の arithmetic part は concrete に閉じた。
   - proof file 上の残る missing math は、
     実質
     `ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget`
     1 本だと読めるようになった。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget`
     の concrete theorem 本体を切る。

### 日時: 2026/03/29 00:24 JST

1. 目的:
   - arithmetic concrete を踏まえて、
     残る `CFBRC existence` 側の target を
     実際の arithmetic witness と整合する形へ補正する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     - `ExceptionalBoundaryDatumPreparedArithmeticWitnessTarget`
     - `exceptional_boundary_datum_prepared_arithmetic_witness_concrete`
     - `exceptional_boundary_datum_prepared_arithmetic_part_of_witness`
     - `ExceptionalBoundaryDatumPreparedCFBRCExistenceOnWitnessTarget`
     を追加した。
   - arithmetic concrete は
     `q ∣ x + 1`
     を本質的に使っていたので、
     その情報を捨てずに
     CFBRC side
     へ渡す witness-aware 版を用意した。
   - あわせて
     - `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_witnessAndCFBRC`
     - `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_cfbrcOnWitness`
     - `primeGe5BranchAExceptionalExistenceMainline_of_cfbrcOnWitness`
     - `primeGe5BranchAPrimitivePacketDescent_of_cfbrcOnWitness_and_restore`
     を追加し、
     arithmetic witness を既定値に焼き付けた wrapper を揃えた。

3. 結論:
   - 従来の
     `ExceptionalBoundaryDatumPreparedCFBRCExistencePartTarget`
     は、
     arithmetic part が選んだ
     `q`
     の出所を保持しないので弱かった。
   - 現在の proof file で truly remaining な local kernel は、
     `q ∣ x + 1`
     まで含む
     `ExceptionalBoundaryDatumPreparedCFBRCExistenceOnWitnessTarget`
     と読むのが正しい。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDatumPreparedCFBRCExistenceOnWitnessTarget`
     の concrete theorem 本体を切る。

### 日時: 2026/03/29 00:36 JST

1. 目的:
   - witness-aware `CFBRC existence`
     をさらに residual sum divisibility へ還元し、
     next body をより直接的な局所核 1 本へ絞る。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     - `sum_range_modEq`
     - `ExceptionalBoundaryDatumPreparedCFBRCResidualOnWitnessTarget`
     - `exceptional_boundary_datum_prepared_cfbrc_existence_on_witness_of_residual`
     を追加した。
   - この橋では、
     `q ∣ x + 1`
     から
     `x + u ≡ u - 1 [MOD q]`
     を作り、
     `boundaryCyclotomicPrimeCore .right d x u`
     の各項を
     `((u - 1)^k * u^(d-1-k))`
     へ項別合同で落とした。
   - さらに
     - `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_residual`
     - `primeGe5BranchAExceptionalExistenceMainline_of_residual`
     - `primeGe5BranchAPrimitivePacketDescent_of_residual_and_restore`
     を追加し、
     residual target から downstream 全体へ戻る wrapper を揃えた。

3. 結論:
   - witness-aware `CFBRC existence`
     の next body は、
     もはや boundary core 自体の divisibility を直接示す形ではなく、
     `u - 1`
     評価の residual sum を
     `q`
     が割ることを示す局所核
     `ExceptionalBoundaryDatumPreparedCFBRCResidualOnWitnessTarget`
     として読める。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDatumPreparedCFBRCResidualOnWitnessTarget`
     の concrete theorem 本体を切る。

### 日時: 2026/03/29 01:05 JST

1. 目的:
   - residual sum divisibility
     を、
     既存の差冪 / `cyclotomicPrimeCore`
     語彙へさらに還元し、
     残る local kernel を
     `u^d - (u - 1)^d`
     の divisibility 1 本として読めるようにする。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     - `ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget`
     - `cyclotomicPrimeCore_one_pred_eq_residual_sum`
     - `exceptional_boundary_datum_prepared_cfbrc_residual_on_witness_of_diffPow`
     を追加した。
   - ここでは
     `prime_dvd_cyclotomicPrimeCore_of_dvd_sub_not_dvd_left`
     を
     `(x,u) := (1, u - 1)`
     で使い、
     `q ∣ u^d - (u - 1)^d`
     から
     `q ∣ cyclotomicPrimeCore d 1 (u - 1)`
     を得た。
   - さらに
     `cyclotomicPrimeCore d 1 (u - 1)`
     が residual sum
     `∑ (u - 1)^k * u^(d-1-k)`
     に一致する補題を追加し、
     residual target に戻した。
   - downstream wrapper として
     - `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_diffPow`
     - `primeGe5BranchAExceptionalExistenceMainline_of_diffPow`
     - `primeGe5BranchAPrimitivePacketDescent_of_diffPow_and_restore`
     を追加した。

3. 結論:
   - witness-aware `CFBRC residual`
     の残核は、
     もはや residual sum そのものではなく、
     `q ∣ u^d - (u - 1)^d`
     の差冪 divisibility 1 本として読める。
   - したがって current proof file の next body は、
     `ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget`
     を concrete に埋める方向で追ってよい。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - 初回実装では
     `1 + (u - 1) = u`
     を
     `u = 0`
     を許したまま private 補題で使ってしまい、
     build error になった。
   - `cyclotomicPrimeCore_one_pred_eq_residual_sum`
     を
     `0 < u`
     前提に直し、
     `Nat.succ_pred_eq_of_pos`
     で明示処理して解消した。

6. 次の課題:
   - `ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget`
     の concrete theorem 本体を切る。

### 日時: 2026/03/29 01:18 JST

1. 目的:
   - 差冪 divisibility target を、
     さらに
     `Nat.ModEq`
     で読む target へ落とし、
     next body を合同条件として追えるようにする。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     - `ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget`
     - `exceptional_boundary_datum_prepared_diffPow_on_witness_of_modEq`
     を追加した。
   - この橋では、
     `Nat.modEq_iff_dvd'`
     を
     `((u - 1)^d ≤ u^d)`
     の下で使い、
     `(u - 1)^d ≡ u^d [MOD q]`
     から
     `q ∣ u^d - (u - 1)^d`
     を回収している。
   - さらに downstream wrapper として
     - `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_diffPowModEq`
     - `primeGe5BranchAExceptionalExistenceMainline_of_diffPowModEq`
     - `primeGe5BranchAPrimitivePacketDescent_of_diffPowModEq_and_restore`
     を追加した。

3. 結論:
   - current proof file の残核は、
     divisibility 版
     `ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget`
     だけでなく、
     合同版
     `ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget`
     としても読める。
   - したがって next body は、
     `u^d - (u - 1)^d`
     の可除性そのものを直接示す代わりに、
     まず
     `(u - 1)^d ≡ u^d [MOD q]`
     を狙う route でもよい。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDatumPreparedDiffPowModEqOnWitnessTarget`
     あるいは
     `ExceptionalBoundaryDatumPreparedDiffPowOnWitnessTarget`
     の concrete theorem 本体を切る。

### 日時: 2026/03/29 01:29 JST

1. 目的:
   - `review-048`
     に合わせて、
     diffPow `ModEq`
     本体をそのまま殴る前に、
     追加で必要な合同入力を theorem 名で分離する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     - `ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget`
     - `exceptional_boundary_datum_prepared_diffPow_modEq_on_witness_of_congruenceKernel`
     を追加した。
   - さらに downstream wrapper として
     - `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_congruenceKernel`
     - `primeGe5BranchAExceptionalExistenceMainline_of_congruenceKernel`
     - `primeGe5BranchAPrimitivePacketDescent_of_congruenceKernel_and_restore`
     を追加し、
     current missing math を
     `congruence kernel`
     1 本として追えるようにした。

3. 結論:
   - 現時点の exceptional datum だけでは
     `(u - 1)^d ≡ u^d [MOD q]`
     は強すぎる可能性があるので、
     proof file では
     additional local congruence kernel
     を first-class に扱うのが自然である。
   - したがって current missing theorem は、
     いったん
     `ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget`
     として追うのがよい。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget`
     の concrete theorem 本体を切る。

### 日時: 2026/03/29 12:58 JST

1. 目的:
   - universal な
     `ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget`
     が強すぎる可能性に備え、
     arithmetic part が実際に選ぶ
     witness prime 1 個だけで downstream を閉じる weaker route を追加する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     - `ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget`
     - `exceptional_boundary_datum_prepared_boundary_core_dvd_of_selected_modEq`
     - `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_selectedCongruenceWitness`
     を追加した。
   - さらに downstream wrapper として
     - `primeGe5BranchAExceptionalExistenceMainline_of_selectedCongruenceWitness`
     - `primeGe5BranchAPrimitivePacketDescent_of_selectedCongruenceWitness_and_restore`
     を追加した。
   - `selected modEq`
     から boundary core divisibility を直接戻す局所補題を入れ、
     universal target を経由せず
     prepared concrete 本体へ入れるようにした。

3. 結論:
   - current proof exploration では、
     「任意の
     `q ∣ x + 1`
     に対して
     `(u - 1)^d ≡ u^d [MOD q]`
     を示す」
     よりも、
     「選んだ witness prime 1 個についてその合同を示す」
     方が自然である。
   - したがって missing theorem の本命候補は、
     universal kernel
     だけでなく
     `ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget`
     としても追える。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - 初回追加時、
     `exceptional_boundary_datum_prepared_boundary_core_dvd_of_selected_modEq`
     に unused variable warning が出たため、
     binder 名を `_...`
     に直して解消した。

6. 次の課題:
   - `ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget`
     の concrete theorem 本体を切る。
   - 併行して、
     universal kernel
     `ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget`
     をまだ保持すべきか、
     selected-witness 版を canonical route に上げるかを判断する。

### 日時: 2026/03/29 13:08 JST

1. 目的:
   - `review-050`
     に合わせて、
     universal congruence kernel から
     selected-witness route への標準橋を置き、
     現在の canonical route 候補が
     selected-witness 版であることをコード上でも明示する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     `exceptional_boundary_datum_prepared_selectedCongruenceWitness_of_congruenceKernel`
     を追加した。
   - この定理では、
     `exceptional_boundary_datum_prepared_arithmetic_witness_concrete`
     で得た
     `q ∣ x + 1`
     つき witness prime を使い、
     stronger な
     `ExceptionalBoundaryDatumPreparedDiffPowCongruenceKernelTarget`
     から
     `ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget`
     を回収する。

3. 結論:
   - universal kernel は、
     依然として stronger theorem として保持できるが、
     proof file の current main route は
     selected-witness 版へ自然に落ちる。
   - したがって next body は、
     universal kernel の concrete 本体よりも
     `ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget`
     の concrete 本体を優先してよい。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDatumPreparedSelectedCongruenceWitnessTarget`
     の concrete theorem 本体を切る。
   - 必要なら、
     selected-witness 版のさらに下に
     `chosen q` 固定の local congruence target
     を置いて missing math をもう 1 段だけ局所化する。

### 日時: 2026/03/29 13:11 JST

1. 目的:
   - selected-witness route の next body を、
     直接の合同
     `(u - 1)^d ≡ u^d [MOD q]`
     ではなく
     `cyclotomicPrimeCore d 1 (u - 1)`
     divisibility まで落とせるかを確認する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchAExceptional.lean]`
     に
     - `ExceptionalBoundaryDatumPreparedSelectedCoreWitnessTarget`
     - `exceptional_boundary_datum_prepared_selectedCongruenceWitness_of_selectedCoreWitness`
     を追加した。
   - さらに downstream wrapper として
     - `primeGe5BranchAExceptionalExistenceMainline_of_selectedCoreWitness`
     - `primeGe5BranchAPrimitivePacketDescent_of_selectedCoreWitness_and_restore`
     を追加した。
   - 変換本体では、
     `DkMath.CFBRC.prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat`
     を
     `x := 1`, `u := u - 1`
     に適用し、
     `q ∣ cyclotomicPrimeCore d 1 (u - 1)`
     から
     `q ∣ u^d - (u - 1)^d`
     を回収して
     `Nat.ModEq`
     へ戻した。

3. 結論:
   - selected-witness route の current missing math は、
     直接の合同よりも
     `ExceptionalBoundaryDatumPreparedSelectedCoreWitnessTarget`
     として追う方が
     既存 `CFBRC` bridge に近く自然である。
   - したがって next body は、
     まず
     `q ∣ cyclotomicPrimeCore d 1 (u - 1)`
     を返す selected witness theorem
     を目標にしてよい。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchAExceptional`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `ExceptionalBoundaryDatumPreparedSelectedCoreWitnessTarget`
     の concrete theorem 本体を切る。
   - 必要なら、
     その下で
     `cyclotomicPrimeCore d 1 (u - 1)`
     を割る witness prime の arithmetic selection 部と
     CFBRC divisibility 部をさらに分離する。
