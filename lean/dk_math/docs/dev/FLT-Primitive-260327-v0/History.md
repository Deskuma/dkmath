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
