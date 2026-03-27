# History of FLT-Wieferich-260327-v1

## Log

### 日時: 2026/03/26 15:48 JST

1. 目的:
2. 実施:
3. 結論:
4. 検証:
5. 失敗事例:
6. 備考:
7. 次の課題:

### 日時: 2026/03/27 17:27 JST

1. 目的:
   - `design-001.md` の方針に従い、
     Branch A で既に得られている
     `y^(p-1) ≡ 1 [MOD p^2]`
     witness を
     どの契約へ落とすのが最短かを
     workspace 実体に即して調査する。
   - そのうえで、
     `via_FLT`
     が残る最後の継ぎ目を
     1 箇所へ明示的に隔離する。

2. 実施:
   - `design-001.md` を読み、
     候補 A-E のうち
     最短は
     `PrimeGe5BranchAWieferichRefuterTarget`
     であることを再確認した。
   - 以下の既存ファイルを調査した。
     - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     - `[DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNCore.lean]`
     - `[DkMath/FLT/PrimeProvider/CosmicPetalBridgeGN.lean]`
     - `[DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferichDefault.lean]`
   - 調査の結果、
     workspace に既にある clean machinery は
     `TriominoNoWieferichBridge` /
     `TriominoWieferichBranchBridge` /
     `WieferichDescentB`
     いずれも
     Branch B (`¬ p ∣ z-y`)
     専用であり、
     Branch A witness を直に受ける adapter は未実装だと確認した。
   - `[TriominoCosmicGapInvariant.lean]`
     に
     `BranchAWieferichAdapterTarget`
     を追加した。
     これは実体として
     `PrimeGe5BranchAWieferichRefuterTarget`
     と同じだが、
     gap-invariant 層から見た
     「最後の clean 置換点」
     として意味づけ直した contract である。
   - 既存の
     `branchAWieferichRefuter_via_FLT`
     は
     `branchAWieferichAdapter_via_FLT`
     へ改名し、
     `branchAWieferichRefuter_math`
     はこの adapter を返す形へ整理した。

3. 結論:
   - workspace 内に
     `PrimeGe5BranchAWieferichRefuterTarget`
     の clean concrete 実装は、
     まだ存在しない。
   - ただし欠けているのは本当にその 1 点だけであり、
     既存 no-Wieferich / descent machinery の型は
     Branch B へ偏っている、
     という構図がはっきりした。
   - したがって今後の clean 化は、
     `BranchAWieferichAdapterTarget`
     の concrete 実装 1 本を差し替える方針で進めればよい。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   - `lake build DkMath.FLT.Basic`
   - `lake build`
   を実行し、build 完了まで待って成功を確認した。

5. 失敗事例:
   - `TriominoNoWieferichBridge` /
     `TriominoWieferichBranchBridge` /
     `WieferichDescentB`
     をそのまま Branch A witness へ流用する案は、
     いずれも
     `¬ p ∣ (z-y)`
     を前提にしているため、
     型レベルで接続不能だった。

6. 備考:
   - これは新しい数学核の不在というより、
     Branch A と Branch B の machinery の境界が
     まだ adapter 化されていない、
     という工学的な欠け方である。
   - `branchAWieferichRefuter_math`
     の中身を変えるだけで、
     現在の public default mainline まで追随して clean 化される。

7. 次の課題:
   - `BranchAWieferichAdapterTarget`
     を満たす clean concrete 実装を新設する。
   - 方向としては、
     `PrimeGe5CounterexamplePack` と
     `p ∣ (z-y)` と
     `y^(p-1) ≡ 1 [MOD p^2]`
     だけから、
     既存の no-Wieferich / descent machinery に繋がる
     Branch A 専用 adapter を切る。
   - それが難しければ、
     `PrimeGe5BranchAWieferichRefuterTarget`
     の手前に
     もう 1 段薄い Branch A / Wieferich local kernel を導入して、
     欠けている数学入力をさらに可視化する。
