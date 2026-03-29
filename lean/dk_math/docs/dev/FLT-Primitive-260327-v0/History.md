# FLT Primitive Packet Descent — History

## History Log

Archive

- [#01](History-01.md)

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

### 日時: 2026/03/29 JST

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

### 日時: 2026/03/29 JST

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

### 日時: 2026/03/29 JST

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

### 日時: 2026/03/29 JST

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

### 日時: 2026/03/29 JST

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

### 日時: 2026/03/29 JST

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

### 日時: 2026/03/29 JST

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

### 日時: 2026/03/29 JST

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

### 日時: 2026/03/29 JST

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

### 日時: 2026/03/29 JST

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

### 日時: 2026/03/29 JST

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
