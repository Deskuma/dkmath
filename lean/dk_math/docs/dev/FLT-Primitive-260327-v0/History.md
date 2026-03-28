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

### 日時: 2026/03/27 22:38 JST

1. 目的:
   - `review-002.md`
     に沿って、
     primitive distinguished-prime selection を
     cyclotomic / Zsigmondy 語彙へ一段寄せる。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `PrimeGe5BranchAPrimitiveZsigmondyTarget`
     を追加した。
   - 同ファイルに
     `primeGe5BranchAPrimitiveDistinguishedPrime_of_zsigmondy`
     を追加し、
     Zsigmondy-lite existence 段から
     primitive distinguished-prime target を回収する thin bridge を置いた。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも
     `BranchAPrimitiveZsigmondyAdapterTarget`
     と
     `branchAPrimitiveDistinguishedPrimeAdapter_of_zsigmondy`
     を追加した。

3. 結論:
   - distinguished-prime selection は、
     primitive route internal target としてだけでなく、
     既存の number-theory existence layer
     と接続する名前でも読めるようになった。
   - 以後は
     `PrimitiveBeam` / `ZsigmondyCyclotomic`
     側の existence 補題を、
     `PrimeGe5BranchAPrimitiveZsigmondyTarget`
     にどう包むかを考えればよい。

4. 検証:
   - build はこの追記の次段で
     `DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
     と
     `DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
     を順番に確認する。

5. 次の課題:
   - `PrimeGe5BranchAPrimitiveZsigmondyTarget`
     に、
     既存の `PrimitiveBeam.exists_primitive_prime_factor_as_prop`
     や
     `primitive_prime_dvd_GN_body`
     をどう接続するかを設計する。
   - 必要なら
     `Body = x * GN`
     の変換を Branch A normal form packet 文脈に薄く包む補題を先に置く。

### 日時: 2026/03/28 00:06 JST

1. 目的:
   - primitive route の missing math を、
     `zsigmondy existence`
     と
     `restore from arithmetic`
     の 2 本へさらに明示的に絞る。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     - `primeGe5BranchAPrimitiveWieferichPacket_of_zsigmondy_arithmetic_and_restore`
     - `primeGe5BranchAPrimitivePacketDescent_of_zsigmondy_arithmetic_and_restore`
     を追加した。
   - これにより
     `PrimeGe5BranchAPrimitivePacketDescentTarget`
     は
     - `PrimeGe5BranchAPrimitiveZsigmondyTarget`
     - `PrimeGe5BranchAPrimitiveDistinguishedPrimeArithmeticTarget`
     - `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`
     の 3 段から橋だけで閉じる。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも対応する provider 側 adapter bridge を追加した。

3. 結論:
   - primitive mainline で concrete 実装すべき新しい数学は、
     少なくとも API 上
     - distinguished prime の existence
     - distinguished prime からの arithmetic fallout
     - arithmetic fallout からの packet 復元
     の 3 本へ限定された。
   - 既に default 実装がある arithmetic fallout を除けば、
     実質的な未完核は
     `zsigmondy existence`
     と
     `restore from arithmetic`
     の 2 本だと読める。

4. 検証:
   - build はこの追記の次段で
     `DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
     と
     `DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
     を順番に確認する。

5. 次の課題:
   - `PrimeGe5BranchAPrimitiveZsigmondyTarget`
     を既存の `PrimitiveBeam` / `ZsigmondyCyclotomic`
     補題へどう接続するかを、Branch A の `p ∣ (z-y)` 制約込みで再設計する。
   - `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`
     の構成論を、`q ∣ s`, `q ∤ t`, `q ⟂ y`, `q ≠ p`
     からどこまで進められるかを見極める。

### 日時: 2026/03/28 00:19 JST

1. 目的:
   - `review-004.md`
     と
     `consider-003.md`
     の方針に沿って、
     primitive distinguished-prime selection を
     いきなり `GN`
     側で取るのでなく、
     まず
     `z^p - y^p`
     側の cyclotomic / diff-power prime existence として切り出す。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `PrimeGe5BranchAPrimitiveCyclotomicPrimeTarget`
     を追加した。
   - 同ファイルに
     `primeGe5BranchAPrimitiveZsigmondy_of_cyclotomicPrime`
     を追加し、
     `pow_sub_pow_factor_cosmic_N`
     によって
     `q ∣ (z^p - y^p), ¬ q ∣ (z-y)`
     から
     `q ∣ GN p (z-y) y`
     を回収する薄い橋を置いた。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも
     `BranchAPrimitiveCyclotomicPrimeAdapterTarget`
     と
     `branchAPrimitiveZsigmondyAdapter_of_cyclotomicPrime`
     を追加した。

3. 結論:
   - primitive selection 段は、
     数学的には
     `GN`
     側 distinguished prime の存在そのものではなく、
     まず
     `z^p - y^p`
     側で
     `q ∤ (z-y)`
     な prime divisor を取る段として読めるようになった。
   - したがって
     `PrimitiveBeam` / `ZsigmondyCyclotomic`
     の既存 existence 補題に寄せる場合も、
     まず
     `PrimeGe5BranchAPrimitiveCyclotomicPrimeTarget`
     を concrete 化し、
     その後
     `GN`
     側 distinguished-prime へ移すのが自然になった。

4. 検証:
   - build はこの追記の次段で
     `DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
     と
     `DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
     を順番に確認する。

5. 次の課題:
   - `PrimeGe5BranchAPrimitiveCyclotomicPrimeTarget`
     を、
     Branch A の `p ∣ (z-y)` 制約と両立する concrete existence theorem
     でどう埋めるかを決める。
   - 既存の `PrimitiveBeam.exists_primitive_prime_factor_as_prop`
     を直接使えない点
     （`¬ p ∣ a-b` 前提）
     を踏まえ、
     Branch A 専用の existence wrapper が必要かを判断する。

### 日時: 2026/03/28 00:31 JST

1. 目的:
   - `review-005.md`
     の整理に合わせて、
     primitive mainline の concretely missing kernel が
     本当に
     - `PrimeGe5BranchAPrimitiveCyclotomicPrimeTarget`
     - `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`
     の 2 本だけだと、
     theorem 名でも読めるようにする。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `primeGe5BranchAPrimitivePacketDescent_of_cyclotomicPrime_and_restore`
     を追加した。
   - この theorem は
     - `primeGe5BranchAPrimitiveZsigmondy_of_cyclotomicPrime`
     - `primeGe5BranchAPrimitiveDistinguishedPrimeArithmetic_default`
     - `primeGe5BranchAPrimitivePacketDescent_of_zsigmondy_arithmetic_and_restore`
     を合成するだけの canonical wrapper である。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも
     `branchAPrimitivePacketDescentAdapter_of_cyclotomicPrime_and_restore`
     を追加した。

3. 結論:
   - primitive packet descent は、
     中間 API をすべて隠せば
     `cyclotomic prime existence`
     と
     `restore-from-arithmetic`
     の 2 本だけがあれば橋で閉じる。
   - したがって arithmetic fallout は完全に solved middle layer と見てよく、
     実質的な未完核 2 本という戦況が
     code 上でも固定された。

4. 検証:
   - build はこの追記の次段で
     `DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
     と
     `DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
     を順番に確認する。

5. 次の課題:
   - `PrimeGe5BranchAPrimitiveCyclotomicPrimeTarget`
     の concrete 実装に必要な
     Branch A 専用 existence wrapper の宣言案を切る。
   - `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`
     が truly constructive に見えるか、
     さらに中間 packet / local kernel を挟むべきかを判断する。
