# FLT Primitive Packet Descent — History

### 日時: 2026/03/27 22:23 JST

1. 目的:
   - `PrimeGe5BranchAPrimitivePacketDescentTarget`
     を本命 route として開始する。
   - ただし最初から packet descent 全体を 1 本で狙わず、
     primitive route が本当に必要としている追加数論入力を
     1 段切り出す。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `PrimeGe5BranchAPrimitiveWieferichPacketTarget`
     を追加した。
   - この target は
     `PrimeGe5BranchAPrimitivePacketDescentTarget`
     と同じ normal-form 入力に加え、
     `y^(p-1) ≡ 1 [MOD p^2]`
     を explicit witness として受ける。
   - 同ファイルに
     `primeGe5BranchAPrimitivePacketDescent_of_wieferichPacket`
     を追加し、
     primitive packet descent 契約を
     witness 付き primitive core
     1 本へ局所化した。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     には
     `BranchAPrimitiveWieferichPacketAdapterTarget`
     と
     `branchAPrimitivePacketDescentAdapter_of_wieferichPacket`
     を追加した。

3. 結論:
   - primitive route の truly new kernel は、
     少なくとも API 上は
     `¬ p ∣ t`
     だけの packet descent 全体ではなく、
     Wieferich witness を明示入力に取る primitive local core
     として読めるようになった。
   - 以後は
     `PrimeGe5BranchAPrimitiveWieferichPacketTarget`
     の concrete 実装を考えればよく、
     packet descent 契約全体を直接扱う必要は薄くなった。

4. 検証:
   - build はこの追記の次段で
     `DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
     と
     `DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
     を順番に確認する。

5. 次の課題:
   - primitive local core をさらに
     cyclotomic / distinguished-prime / smaller-packet restoration
     のどこで分けるかを決める。
   - 必要なら
     `PrimeGe5BranchAPrimitiveWieferichPacketTarget`
     を 2 段に分けて、
     primitive route の数学核をさらに狭める。

### 日時: 2026/03/27 22:31 JST

1. 目的:
   - `review-001.md`
     に沿って、
     `PrimeGe5BranchAPrimitiveWieferichPacketTarget`
     を
     - distinguished-prime selection
     - smaller-packet restoration
     の 2 段へさらに分ける。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     - `PrimeGe5BranchAPrimitiveDistinguishedPrimeTarget`
     - `PrimeGe5BranchAPrimitivePacketRestoreTarget`
     - `primeGe5BranchAPrimitiveWieferichPacket_of_distinguishedPrime_and_restore`
     を追加した。
   - distinguished-prime target は
     `q ∣ GN p (z-y) y`
     かつ
     `¬ q ∣ (z-y)`
     を返す。
   - restoration target は、
     その `q`
     を受けて smaller packet を返す。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     には provider 側 alias と thin bridge を追加した。

3. 結論:
   - primitive route の truly new kernel は、
     もはや witness 付き packet descent 全体でもなく、
     少なくとも API 上は
     - distinguished prime を 1 つ取る
     - その prime から packet を復元する
     の 2 段に分けて読める。
   - これで次に攻める数学は、
     `q` の取り方と
     packet restoration
     のどちらが本命かを判断しやすくなった。

4. 検証:
   - build はこの追記の次段で
     `DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
     と
     `DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
     を順番に確認する。

5. 次の課題:
   - distinguished-prime target を
     cyclotomic / Zsigmondy existence
     に寄せるか、
     さらに local arithmetic 条件を足すかを決める。
   - restoration target の入力 `q`
     にどの追加条件が必要かを見極める。
