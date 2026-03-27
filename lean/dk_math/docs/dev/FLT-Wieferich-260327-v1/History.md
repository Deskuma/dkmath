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

### 日時: 2026/03/27 17:43 JST

1. 目的:
   - `consider-002.md` の提案に従い、
     Branch A witness route の clean 化を
     `witness -> refuter`
     で直接狙うのではなく、
     `witness -> local kernel -> refuter`
     へ再整理する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `PrimeGe5BranchAWieferichLocalKernelTarget`
     を追加した。
     契約は
     `gap = p^(p-1) * t^p`,
     `GN = p * s^p`,
     `x = p * (t * s)`,
     `t ⟂ s`,
     `t ⟂ y`,
     `s ⟂ y`,
     `¬ p ∣ s`,
     `y^(p-1) ≡ 1 [MOD p^2]`
     から
     `False`
     を返す形である。
   - 同ファイルに
     `primeGe5BranchAWieferichRefuter_of_localKernel`
     を追加した。
     これは既存の
     `primeGe5BranchAShapeValue_of_factorization`,
     `primeGe5BranchANormalForm_of_witness`,
     `primeGe5BranchANormalForm_coprime_*`,
     `primeGe5BranchANormalForm_prime_not_dvd_s_default`
     だけを使って、
     local kernel から
     `PrimeGe5BranchAWieferichRefuterTarget`
     を回収する thin bridge である。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     には
     `BranchAWieferichLocalKernelAdapterTarget`
     と
     `branchAWieferichAdapter_of_localKernel`
     を追加し、
     gap-invariant 層から見た clean 差し替え先も明示した。

3. 結論:
   - 欠けた数学は、
     もはや
     `PrimeGe5BranchAWieferichRefuterTarget`
     全体ではなく、
     `PrimeGe5BranchAWieferichLocalKernelTarget`
     1 本に局所化できた。
   - これにより
     `BranchAWieferichAdapterTarget`
     は public splice として保ったまま、
     その 1 段手前にある真正の数学核が型として見えるようになった。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   - `lake build DkMath.FLT.Basic`
   - `lake build`
   を実行し、build 完了まで待って成功を確認した。

5. 失敗事例:
   - witness 単独の
     `PrimeGe5BranchAWieferichRefuterTarget`
     を直接 Branch B machinery に落とす案は、
     引き続き型の不一致で進展しなかった。

6. 備考:
   - 今回の変更は数学を進めたというより、
     欠けた数学入力の場所を
     `PrimeGe5BranchAWieferichLocalKernelTarget`
     として固定した段階である。
   - 既存 default mainline への配線はそのままで、
     clean 化の照準だけがさらに狭まった。

7. 次の課題:
   - `PrimeGe5BranchAWieferichLocalKernelTarget`
     の clean concrete 実装を探す。
   - もしそれでも広すぎるなら、
     この local kernel を
     arithmetic / descent
     の 2 段にさらに分割する。

### 日時: 2026/03/27 18:33 JST

1. 目的:
   - `review-003.md` の指摘どおり、
     `PrimeGe5BranchAWieferichLocalKernelTarget`
     が truly new kernel ではなく
     既存
     `PrimeGe5BranchANormalFormArithmeticKernelTarget`
     の API 変種に近いことを、
     Lean 上の bridge 定理として固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `primeGe5BranchAWieferichLocalKernel_of_arithmeticKernel`
     を追加した。
     これは
     `PrimeGe5BranchANormalFormArithmeticKernelTarget`
     から
     `PrimeGe5BranchAWieferichLocalKernelTarget`
     を回収する橋であり、
     `gcd(gap,GN)=p`
     は既存既定抽出
     `primeGe5BranchANormalForm_gcd_gap_GN_eq_p_default`
     で供給する。
   - 同ファイルに
     `primeGe5BranchANormalFormArithmeticKernel_of_wieferichLocalKernel`
     も追加した。
     こちらは
     `PrimeGe5BranchAWieferichLocalKernelTarget`
     から
     arithmetic kernel
     を戻す橋であり、
     `y^(p-1) ≡ 1 [MOD p^2]`
     は既存
     `primeGe5BranchANormalForm_y_wieferich_mod_p_sq`
     で再生成している。

3. 結論:
   - 現段階の
     `PrimeGe5BranchAWieferichLocalKernelTarget`
     は、
     工学的には witness route の checkpoint として有益だが、
     数学的には
     `PrimeGe5BranchANormalFormArithmeticKernelTarget`
     とほぼ往復可能であることが明示された。
   - したがって obstruction の場所は
     local kernel そのものへ移ったというより、
     依然として arithmetic/descent 側の本体にある、
     という読みが Lean 上でも固定された。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   - `lake build DkMath.FLT.Basic`
   - `lake build`
   を実行し、build 完了まで待って成功を確認した。

5. 備考:
   - warning は既存の
     `TriominoCosmicBranchA.lean`
     の final `sorry`
     と、
     研究層・`ABC021`・`TriominoFLT`
     の既存 `sorry`
     のみで、新規の build failure は無い。
   - この段階で
     `AWieferichLocalKernel`
     は「最後の数学核」ではなく、
     現在の情報量を見える化した API checkpoint と読むのが正確になった。

6. 次の課題:
   - truly new kernel として、
     distinguished-prime descent
     ないし
     `p`-進深さ
     を返す contract を別に切るかを決める。
   - あるいは
     `branchAWieferichRefuter_math`
     を clean 化する際に、
     arithmetic kernel を直接受ける route へ戻してよいかを再評価する。

### 日時: 2026/03/27 18:43 JST

1. 目的:
   - `AWieferichLocalKernel ↔ ArithmeticKernel`
     の整理を踏まえ、
     truly new kernel 候補として
     Branch A distinguished-prime descent
     を型で固定する。
   - あわせて、
     provider 側から見た差し替え口も
     `GapInvariant`
     に明示する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     - `MinimalPrimeGe5CounterexamplePackA`
     - `PrimeGe5BranchADistinguishedPrimeDescentTarget`
     - `minimalPrimeGe5CounterexampleSelectionA_impl`
     - `primeGe5BranchARefuter_on_minimal_of_distinguishedPrimeDescent`
     - `primeGe5BranchARefuter_of_distinguishedPrimeDescent`
     を追加した。
   - これにより、
     Branch A 条件
     `p ∣ (z - y)`
     を保ったまま
     `z` 最小の反例を no-`sorry` で選び、
     distinguished-prime descent が供給されれば
     Branch A refuter
     が閉じることを lower layer で明示した。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     には
     - `BranchADistinguishedPrimeDescentAdapterTarget`
     - `branchAWieferichAdapter_of_distinguishedPrimeDescent`
     を追加し、
     witness-route adapter と並ぶ
     次段 clean 化候補として公開 splice を固定した。

3. 結論:
   - Branch A の truly new kernel 候補は、
     もはや
     `AWieferichLocalKernel`
     ではなく、
     `PrimeGe5BranchADistinguishedPrimeDescentTarget`
     として明示できるようになった。
   - これで
     `q = p`
     が distinguished prime になる Branch A 特有の下降仕様を、
     Branch B の `WieferichDescentB`
     とは別系統で育てる受け皿が整った。
   - 現状の concrete 実装はまだ無いが、
     「次に埋めるべき数学」が
     arithmetic checkpoint ではなく
     distinguished-prime descent
     にあることが型でも記録された。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   - `lake build DkMath.FLT.Basic`
   - `lake build`
   を実行し、build 完了まで待って成功を確認した。

5. 備考:
   - `GapInvariant` 側では、
     `branchAWieferichAdapter_of_distinguishedPrimeDescent`
     は Wieferich witness を単に無視して
     Branch A refuter へ落とす thin wrapper である。
   - これは
     distinguished-prime descent
     が witness route より本質的に強い出口であることの反映でもある。

6. 次の課題:
   - `PrimeGe5BranchADistinguishedPrimeDescentTarget`
     の concrete 数学を探す。
     候補は
     - smaller counterexample pack の構成
     - `p`-進深さを使う descent
     の 2 系統。
   - あるいは、
     既存 `WieferichDescentB`
     の argument pattern を参考に、
     Branch A 版の
     `DistinguishedPrimeDescentA`
     を別ファイルへ切り出す。

### 日時: 2026/03/27 18:51 JST

1. 目的:
   - `distinguished-prime descent`
     を単なる構想でなく、
     Branch A 側の concrete な次段 kernel として
     さらに見える化する。
   - 具体的には、
     最小 Branch A 反例上の refuter と
     global Branch A refuter の関係を
     no-`sorry` で固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     で
     `MinimalPrimeGe5CounterexamplePackA`
     と
     `PrimeGe5BranchADistinguishedPrimeDescentTarget`
     を使い、
     - `minimalPrimeGe5CounterexampleSelectionA_impl`
     - `primeGe5BranchARefuter_on_minimal_of_distinguishedPrimeDescent`
     - `primeGe5BranchARefuter_of_distinguishedPrimeDescent`
     を追加した。
   - これにより
     `p ∣ (z-y)`
     を保つ Branch A 最小反例選択と、
     distinguished-prime descent
     からの global refuter 回収が
     lower layer で閉じるようになった。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     には
     `BranchADistinguishedPrimeDescentAdapterTarget`
     と
     `branchAWieferichAdapter_of_distinguishedPrimeDescent`
     を追加し、
     provider 側から見た splice point
     としてもこの route を明示した。

3. 結論:
   - Branch A で truly new な数学を置く場所は、
     `AWieferichLocalKernel`
     ではなく、
     `MinimalPrimeGe5CounterexamplePackA`
     と
     `PrimeGe5BranchADistinguishedPrimeDescentTarget`
     の組であることが
     Lean 上でも明確になった。
   - 特に
     `primeGe5BranchARefuter_of_distinguishedPrimeDescent`
     により、
     今後の concrete 実装は
     minimal Branch A counterexample 上の descent
     を与えるだけで
     global refuter
     に持ち上がる。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   - `lake build DkMath.FLT.Basic`
   - `lake build`
   を実行し、build 完了まで待って成功を確認した。

5. 備考:
   - `branchAWieferichAdapter_of_distinguishedPrimeDescent`
     は witness を無視して Branch A refuter に落とす thin wrapper であり、
     distinguished-prime descent
     が witness route より強い出口であることを反映している。
   - この段階では concrete descent 数学はまだ無いが、
     どこへ置けば良いかはかなり明確になった。

6. 次の課題:
   - `PrimeGe5BranchADistinguishedPrimeDescentTarget`
     の concrete 実装を探す。
   - 候補は、
     - smaller counterexample pack を直接構成する route
     - `p`-進深さを介した descent route
     の 2 本。
   - 必要なら
     `CosmicPetalBridgeGNCore` の
     `WieferichDescentB`
     と対応する Branch A 版 contract を
     別ファイルへ切り出す。

### 日時: 2026/03/27 19:09 JST

1. 目的:
   - `distinguished-prime descent`
     をさらに concrete にし、
     「最小反例上の descent」
     よりも一段強い
     「smaller Branch A counterexample を直接返す」
     契約まで押し下げる。
   - これにより、
     最終的な concrete 数学が目指す型を
     さらに明確にする。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `PrimeGe5BranchASmallerCounterexampleTarget`
     を追加した。
     これは
     Branch A normal form
     から
     `p ∣ (z' - y')`
     を保つより小さい counterexample pack
     を直接返す target である。
   - 同ファイルに
     `primeGe5BranchADistinguishedPrimeDescent_of_smallerCounterexample`
     を追加し、
     上記 stronger contract
     から
     `PrimeGe5BranchADistinguishedPrimeDescentTarget`
     を得る橋を置いた。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     には
     `BranchASmallerCounterexampleAdapterTarget`
     と
     `branchAWieferichAdapter_of_smallerCounterexample`
     を追加し、
     provider 側から見ても
     stronger route
     が splice point
     として表現できるようにした。

3. 結論:
   - Branch A の concrete 未完核は、
     単なる
     `distinguished-prime descent`
     ではなく、
     さらに強い
     `PrimeGe5BranchASmallerCounterexampleTarget`
     として記述できることが明確になった。
   - したがって今後の数学探索では、
     「より小さい Branch A counterexample をどう直接作るか」
     を本題として考えればよい。
   - `distinguished-prime descent`
     はその stronger contract
     から機械的に回収できる。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   - `lake build DkMath.FLT.Basic`
   を実行し、build 完了まで待って成功を確認した。

5. 備考:
   - `BranchASmallerCounterexampleAdapterTarget`
     は、
     witness route を使う provider 側から見た
     strongest splice point
     として機能する。
   - 既存の
     `PrimeGe5BranchADistinguishedPrimeDescentTarget`
     は、
     以後は middle contract
     として読める。

6. 次の課題:
   - `PrimeGe5BranchASmallerCounterexampleTarget`
     の concrete 実装を探す。
   - 候補は、
     - smaller counterexample pack を直接構成する arithmetic route
     - `p`-進深さや distinguished prime を介した descent route
     の 2 本。
   - 必要なら、
     Branch A 専用の
     `SmallerCounterexampleA`
     contract / helper file
     を別に切って探索を分離する。

### 日時: 2026/03/27 20:05 JST

1. 目的:
   - `design-004` に沿って、
     smaller counterexample
     より一段手前の
     smaller normal-form packet
     を返す契約を導入する。
   - これにより、
     concrete 数学の探索対象を
     `x' y' z'`
     直書きではなく
     Branch A packet
     の再構成へ寄せる。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `PrimeGe5BranchANormalFormPacket`
     を追加した。
     これは
     `pack`, `hp_dvd_gap`, `hgap`, `hsGN`, `hsx`
     をひとまとめに持つ構造体である。
   - 同ファイルに
     `counterexamplePack_of_branchANormalFormPacket`
     を追加し、
     packet から
     `PrimeGe5CounterexamplePack`
     を取り出す橋を固定した。
   - さらに
     `PrimeGe5BranchASmallerPacketTarget`
     を追加し、
     `primeGe5BranchASmallerCounterexample_of_smallerPacket`
     で
     `PrimeGe5BranchASmallerCounterexampleTarget`
     を機械的に回収する形にした。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     には
     `BranchASmallerPacketAdapterTarget`
     と
     `branchAWieferichAdapter_of_smallerPacket`
     を追加し、
     provider 側から見た strongest splice point
     も packet route
     で表現できるようにした。

3. 結論:
   - Branch A の concrete 未完核は、
     `smaller counterexample`
     ではなく
     `smaller normal-form packet`
     を返す問題としてまず考えるのが自然だと
     Lean の型でも明示できた。
   - したがって今後の数学探索では、
     `u' = p^(p-1) * t'^p`,
     `GN = p * s'^p`,
     `x' = p * (t' * s')`
     を保った packet の再構成を本題にできる。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   - `lake build DkMath.FLT.Basic`
   を実行し、build 完了まで待って成功を確認した。

5. 備考:
   - 途中で並列 build により
     `TriominoCosmicBranchA.setup.json`
     が壊れる事象が出たため、
     以後は依存の重なる target は順番に build する方針に戻した。
   - `PrimeGe5BranchASmallerCounterexampleTarget`
     は今後、
     packet route
     から機械的に得られる middle target
     として読める。

6. 次の課題:
   - `PrimeGe5BranchASmallerPacketTarget`
     の concrete 実装を探す。
   - 候補は、
     - valuation peel による packet 再構成
     - cyclotomic / distinguished-prime descent による packet 再構成
     の 2 本。

### 日時: 2026/03/27 20:16 JST

1. 目的:
   - `design-004` の二段構えを型として固定し、
     `SmallerPacketTarget`
     の concrete 実装探索を
     `p ∣ t`
     と
     `¬ p ∣ t`
     の 2 route
     に完全分離する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     - `PrimeGe5BranchAValuationPeelPacketTarget`
     - `PrimeGe5BranchAPrimitivePacketDescentTarget`
     を追加した。
   - 同ファイルに
     `primeGe5BranchASmallerPacket_of_routes`
     を追加し、
     valuation peel route
     と
     primitive/cyclotomic route
     が揃えば
     `PrimeGe5BranchASmallerPacketTarget`
     を場合分けだけで回収できるようにした。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     には
     - `BranchAValuationPeelPacketAdapterTarget`
     - `BranchAPrimitivePacketDescentAdapterTarget`
     - `branchASmallerPacketAdapter_of_routes`
     を追加し、
     provider 側から見ても
     route split
     が splice point
     として読めるようにした。

3. 結論:
   - Branch A packet 探索の concrete 未完核は、
     いまや
     `PrimeGe5BranchASmallerPacketTarget`
     1 本ではなく、
     - `PrimeGe5BranchAValuationPeelPacketTarget`
     - `PrimeGe5BranchAPrimitivePacketDescentTarget`
     の 2 本に分解されている。
   - したがって今後は
     `p ∣ t`
     の Nat / valuation route
     と、
     `¬ p ∣ t`
     の primitive/cyclotomic route
     を独立に攻めればよい。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を実行し、build 完了まで待って成功を確認した。
   - 後者の build で
     `DkMath.FLT.Basic`
     も再ビルドされ、成功を確認した。

5. 備考:
   - これ以降の concrete 数学は、
     `smaller counterexample`
     そのものより
     `smaller packet`
     の生成法を主題にして考えればよい。
   - provider 側でも
     route split
     が visible になったため、
     clean default へ差し込む場所はかなり明確になった。

6. 次の課題:
   - まずは
     `PrimeGe5BranchAValuationPeelPacketTarget`
     を攻める。
     ここは Nat / valuation 層で比較的近い。
   - primitive case は
     `PrimeGe5BranchAPrimitivePacketDescentTarget`
     として別腹で育てる。

### 日時: 2026/03/27 20:31 JST

1. 目的:
   - valuation peel route の seed を、
     concrete equality として先に固定する。
   - 具体的には、
     `s^p - y^(p-1)`
     が gap
     あるいは
     `p^(p-1) * t^p`
     を 1 因子持つことを theorem 化する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     - `primeGe5BranchA_spow_eq_head_add_gap_mul`
     - `primeGe5BranchA_spow_eq_head_add_gapShape_mul`
     を追加した。
   - 前者は
     `GN p (z - y) y = p * s^p`
     と
     `p ∣ (z - y)`
     から
     `s^p = y^(p-1) + (z-y) * B`
     を返す。
   - 後者はこれを
     `z - y = p^(p-1) * t^p`
     で読み替え、
     `s^p = y^(p-1) + (p^(p-1) * t^p) * B`
     を返す。

3. 結論:
   - valuation peel route は、
     もはや抽象的な
     “余分な distinguished-prime 深さ”
     の話ではなく、
     `s^p - y^(p-1)`
     が gap を因子にもつ concrete seed
     を起点に考えられるようになった。
   - 特に
     `p ∣ t`
     の場合は、
     この seed と
     `z - y = p^(p-1) * t^p`
     を組み合わせることで、
     `t` の 1 段 peeling
     を狙う筋道がかなり見えやすくなった。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.Basic`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を実行し、build 完了まで待って成功を確認した。

5. 備考:
   - 途中で
     `exists_eq_mul_left_of_dvd`
     の向きに起因する型エラーが数回出たが、
     いずれも
     `a * p`
     と
     `p * a`
     の並べ替えを明示して解消した。
   - `TriominoCosmicBranchA.lean`
     の unused `simp` warning 1 件もこの作業中に解消した。

6. 次の課題:
   - `PrimeGe5BranchAValuationPeelPacketTarget`
     を、
     いま追加した gap-shape seed
     から具体的に作る。
   - 具体的には
     `p ∣ t`
     なら
     `t = p * t₁`
     と置いて、
     そこから smaller packet
     をどう再構成するかを探る。

### 日時: 2026/03/27 20:46 JST

1. 目的:
   - valuation peel route の入口を、
     さらに target / theorem として固定する。
   - 具体的には、
     `p ∣ t`
     のとき
     `t = p * t₁`
     と
     `s^p - y^(p-1)`
     の高い `p`-冪 tail
     を同時に返す seed
     を明示する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `PrimeGe5BranchAValuationPeelSeedTarget`
     を追加した。
   - 同ファイルに
     - `primeGe5BranchA_gapShape_peel_of_dvd_t`
     - `primeGe5BranchAValuationPeelSeed_default`
     を追加した。
   - `primeGe5BranchA_gapShape_peel_of_dvd_t`
     は
     `p ∣ t`
     から
     `t = p * t₁`
     と
     `p^(p-1) * t^p = p^(2p-1) * t₁^p`
     を返す。
   - `primeGe5BranchAValuationPeelSeed_default`
     はさらに
     `primeGe5BranchA_spow_eq_head_add_gapShape_mul`
     と組み合わせ、
     `s^p = y^(p-1) + p^(2p-1) * (t₁^p * B)`
     を返す concrete seed
     とした。

3. 結論:
   - valuation peel route は、
     いまや
     `PrimeGe5BranchAValuationPeelPacketTarget`
     を直接埋める前に、
     `PrimeGe5BranchAValuationPeelSeedTarget`
     という 1 段下の checkpoint
     を通して考えられるようになった。
   - これにより
     `p ∣ t`
     の route は、
     「gap-shape の distinguished-prime 深さを 1 段剥き、
      `s^p - y^(p-1)` に残る tail を高い `p`-冪として読む」
     という形でかなり具体化した。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.Basic`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を実行し、build 完了まで待って成功を確認した。

5. 備考:
   - `GapInvariant` 側の追加はまだ無い。
     今回の seed は
     Branch A lower layer
     の concrete 数学 checkpoint
     としてまず固定した。
   - 途中で
     `exists_eq_mul_left_of_dvd`
     の向きや
     `k = 1`
     項の正規化でいくつか Lean の式整形を要したが、
     いずれも解消済み。

6. 次の課題:
   - `PrimeGe5BranchAValuationPeelPacketTarget`
     を、
     いま固定した
     `PrimeGe5BranchAValuationPeelSeedTarget`
     からどう構成するかを考える。
   - その際、
     `t₁`
     と
     `t₁^p * B`
     から
     smaller normal-form packet
     の `(t', s', y', z')`
     をどう再組立てするかが次の本題になる。

### 日時: 2026/03/27 20:20 JST

1. 目的:
   - `consider-005.md`
     の方針に従い、
     valuation peel route を
     `seed -> canonical tail -> packet`
     の 3 段で扱えるようにする。
   - まずは
     `GN/p`
     の標準 tail を explicit に返す
     canonical stage
     を lower layer に固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `PrimeGe5BranchAValuationPeelCanonicalTailTarget`
     を追加した。
   - 同ファイルに
     `primeGe5BranchAValuationPeelCanonicalTail_default`
     を追加した。
     これは
     `p ∣ t`
     から
     `t = p * t₁`
     を剥き、
     `GN p (p^(p-1) * t₁^p) y`
     を
     `p * y^(p-1) + (p^(p-1) * t₁^p) * C`
     の形で返す。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     には
     `BranchAValuationPeelCanonicalTailAdapterTarget`
     を追加し、
     provider 側から見た splice point も明示した。

3. 結論:
   - valuation peel route は、
     もはや seed から直接 packet を狙うだけでなく、
     宇宙式の canonical tail
     そのものを露出する中間段を持てるようになった。
   - これにより次は、
     `PrimeGe5BranchAValuationPeelSeedTarget`
     の `B`
     と
     `PrimeGe5BranchAValuationPeelCanonicalTailTarget`
     の `C`
     を比較すればよい、
     という形で不足情報がさらに見えやすくなった。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   - `lake build DkMath.FLT.Basic`
   を順番に実行し、build 完了まで待って成功を確認した。

5. 備考:
   - 今回の canonical stage は、
     まだ
     `GN p (p^(p-1) * t₁^p) y = p * s^p`
     のような stronger equality を要求しない。
     まずは
     `GN/p`
     の標準 tail を explicit に取り出す段階に留めた。
   - これは `consider-005.md` の
     5.1 / 5.2
     に対応する lower-layer 実装である。

6. 次の課題:
   - seed 側の
     `B`
     と canonical tail 側の
     `C`
     を比較する補題を置き、
     `canonical tail -> packet`
     に足りない情報をさらに exact に炙り出す。
   - その比較で余剰項が残るなら、
     valuation peel route は
     `obstruction extraction`
     に留め、
     `PrimeGe5BranchAPrimitivePacketDescentTarget`
     を本命へ押し上げる。

### 日時: 2026/03/27 20:33 JST

1. 目的:
   - `consider-005.md`
     の 5.3 に対応して、
     valuation peel route の
     `seed`
     と
     `canonical tail`
     を同じ
     `t₁`
     上に並べる比較段を
     lower layer に固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `PrimeGe5BranchAValuationPeelTailComparisonTarget`
     を追加した。
   - 同ファイルに
     `primeGe5BranchAValuationPeelTailComparison_of_seed_and_canonical`
     と
     `primeGe5BranchAValuationPeelTailComparison_default`
     を追加した。
   - 比較段の契約は、
     同じ
     `t = p * t₁`
     の下で
     - seed 側:
       `s^p = y^(p-1) + p^(2p-1) * (t₁^p * B)`
     - canonical tail 側:
       `GN p (p^(p-1) * t₁^p) y = p * y^(p-1) + (p^(p-1) * t₁^p) * C`
     を同時に返す形とした。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     には
     `BranchAValuationPeelTailComparisonAdapterTarget`
     を追加した。

3. 結論:
   - valuation peel route は、
     いまや
     `seed`
     と
     `canonical tail`
     の両方を
     同じ `t₁`
     上で比較できる段まで整備された。
   - したがって next step は、
     truly new math を
     `B`
     と
     `C`
     の関係に集中して書けばよい。
     `packet`
     を直接書くより、どこが不足しているかがさらに明瞭になった。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   - `lake build DkMath.FLT.Basic`
   - `lake build`
   を順番に実行し、build 完了まで待って成功を確認した。

5. 備考:
   - 今回の比較段では、
     まだ
     `B = C`
     や
     `C = p^p * B`
     のような stronger statement は要求していない。
     そこが次の concrete 数学核である。

6. 次の課題:
   - `B`
     と
     `C`
     の間に成り立つ exact relation を探す。
   - その relation が packet の再構成まで届かなければ、
     valuation peel route は obstruction extraction とみなし、
     `PrimeGe5BranchAPrimitivePacketDescentTarget`
     を本命 route として押し上げる。

### 日時: 2026/03/27 21:02 JST

1. 目的:
   - `analysis-BC.md`
     の first formal target を実装し、
     valuation peel comparison の
     `B`
     と
     `C`
     を
     `GTail p 2`
     の exact coefficient として読み直した上で、
     mod-level relation
     `p * B ≡ C [MOD p^(p-1) * t₁^p]`
     を lower layer に固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `PrimeGe5BranchAValuationPeelTailExactTarget`
     と
     `PrimeGe5BranchAValuationPeelTailModEqTarget`
     を追加した。
   - 同ファイルに
     - `primeGe5BranchA_gapTail_eq_p_mul_of_gapMul`
     - `primeGe5BranchA_canonicalTail_eq_coeff_of_expansion`
     - `primeGe5BranchA_GTail_two_scaled_modEq`
     - `primeGe5BranchAValuationPeelTailExact_of_comparison`
     - `primeGe5BranchAValuationPeelTailModEq_of_exact`
     - `primeGe5BranchAValuationPeelTailModEq_default`
     を追加した。
   - これにより、
     comparison 段の
     `B`
     と
     `C`
     は
     - `GTail p 2 (z - y) y = p * B`
     - `GTail p 2 (p^(p-1) * t₁^p) y = C`
     と exact に読め、
     `z - y = p^p * (p^(p-1) * t₁^p)`
     を通じて
     `p * B ≡ C [MOD p^(p-1) * t₁^p]`
     が従う形になった。

3. 結論:
   - `analysis-BC.md`
     の「比較段の本当の差分は
     `B`
     と
     `C`
     だけ」という主張は、
     Lean 上で
     `GTail p 2`
     の exact / modEq statement として実装された。
   - valuation peel route は、
     もう単なる heuristic ではなく、
     canonical tail 係数どうしの relation を返す concrete API を持つ。
   - これにより次に攻めるべき不足情報は、
     packet 再構成そのものではなく、
     `p * B ≡ C [MOD ...]`
     から何をさらに extraction できるか、
     あるいはここで valuation peel を obstruction route と見切るか、
     の判断に絞られた。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   - `lake build DkMath.FLT.Basic`
   - `lake build`
   を順番に実行し、build 完了まで待って成功を確認した。

5. 備考:
   - `TriominoCosmicBranchA.lean`
     には既存どおり final kernel の `sorry` が 1 箇所残る。
   - 新規追加部分に関する warning は、
     `primeGe5BranchA_canonicalTail_eq_coeff_of_expansion`
     付近の
     `simpa`/`simp`
     lint だけで、
     build failure は無い。

6. 次の課題:
   - `PrimeGe5BranchAValuationPeelTailModEqTarget`
     から smaller packet 再構成に届く route が見えるかを検討する。
   - もし十分な extraction が得られなければ、
     valuation peel route は
     obstruction extraction
     で止め、
     `PrimeGe5BranchAPrimitivePacketDescentTarget`
     を本命 route として押し上げる。

### 日時: 2026/03/27 21:24 JST

1. 目的:
   - `analysis-BC.md`
     の追記に対応して、
     mod-level relation
     `p * B ≡ C [MOD u]`
     を
     exact error decomposition
     に持ち上げる。
   - nat 上では符号付き差を直接書けないので、
     正しい向き
     `p * B = C + u * E`
     を lower layer 契約として固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `PrimeGe5BranchAValuationPeelTailErrorTarget`
     を追加した。
   - 同ファイルに
     - `primeGe5BranchA_GTail_two_scaled_ge`
     - `primeGe5BranchA_GTail_two_scaled_exists_error`
     - `primeGe5BranchAValuationPeelTailError_of_exact`
     - `primeGe5BranchAValuationPeelTailError_default`
     を追加した。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     には
     `BranchAValuationPeelTailErrorAdapterTarget`
     を追加した。

3. 結論:
   - `analysis-BC.md`
     で議論した
     `C - pB`
     の first-order 差分は、
     Lean では
     `p * B = C + u * E`
     という nat-compatible な exact decomposition として固定できた。
   - これにより valuation peel route は、
     合同情報だけでなく
     error term を持つ concrete API
     まで整備された。
   - 一方で、ここまで来てもまだ smaller packet は直接出ていないので、
     valuation peel の意味づけは引き続き
     `obstruction extraction / first-order control`
     寄りだと読める。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認した。

5. 備考:
   - 途中で
     `Nat.pow_pos`
     と
     `Nat.modEq_iff_dvd'`
     から exact equality への戻し方に Lean 側の修正が要ったが、
     最終的に build failure は解消した。
   - `TriominoCosmicBranchA.lean`
     の残る本質的未完は、
     これまで通り final `sorry` 1 箇所だけである。

6. 次の課題:
   - `PrimeGe5BranchAValuationPeelTailErrorTarget`
     の error term
     `E`
     から packet 再構成へ届く stronger extraction があるかを検討する。
   - それが薄い場合は、
     valuation peel route を
     obstruction extraction
     に留め、
     `PrimeGe5BranchAPrimitivePacketDescentTarget`
     を本命 route として押し上げる。
