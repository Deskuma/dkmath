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

### 日時: 2026/03/28 00:44 JST

1. 目的:
   - `review-006.md`
     に沿って、
     primitive selection 側をさらに縮め、
     `PrimeGe5BranchAPrimitiveCyclotomicPrimeTarget`
     自体も
     Branch A 専用の最小 existence wrapper
     1 本から閉じる形にする。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `PrimeGe5BranchACyclotomicExistenceTarget`
     を追加した。
     これは
     `PrimeGe5CounterexamplePack p x y z`
     と
     `p ∣ (z-y)`
     だけから
     `∃ q, Prime q ∧ q ∣ (z^p - y^p) ∧ ¬ q ∣ (z-y)`
     を返す最小 wrapper である。
   - 同ファイルに
     - `primeGe5BranchAPrimitiveCyclotomicPrime_of_existence`
     - `primeGe5BranchAPrimitivePacketDescent_of_existence_and_restore`
     を追加した。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも対応する adapter alias / bridge を追加した。

3. 結論:
   - primitive packet descent は、
     code 上ついに
     - `PrimeGe5BranchACyclotomicExistenceTarget`
     - `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`
     の 2 本だけがあれば閉じるところまで縮んだ。
   - selection 側の truly missing kernel は、
     もはや
     `GN`
     や
     normal-form
     の局所データを一切含まない、
     Branch A 専用の diff-side existence wrapper
     1 本に押し込められた。

4. 検証:
   - build はこの追記の次段で
     `DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
     と
     `DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
     を順番に確認する。

5. 次の課題:
   - `PrimeGe5BranchACyclotomicExistenceTarget`
     の concrete 実装を、
     Branch A 条件
     `p ∣ (z-y)`
     のもとでどう与えるかを設計する。
   - 既存の `PrimitiveBeam` 系補題を直接使えない理由を
     仮定ごとに整理し、
     追加すべき Branch A 専用 existence theorem の最小 statement を決める。

### 日時: 2026/03/28 00:56 JST

1. 目的:
   - selection 側の concrete theorem 候補として、
     Branch A が既に lower layer で持っている
     Wieferich witness
     `y^(p-1) ≡ 1 [MOD p^2]`
     を明示入力に取る existence target を用意する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `PrimeGe5BranchACyclotomicExistenceOnWieferichTarget`
     を追加した。
   - 同ファイルに
     - `primeGe5BranchACyclotomicExistence_of_wieferich`
     - `primeGe5BranchAPrimitivePacketDescent_of_wieferichExistence_and_restore`
     を追加し、
     `primeGe5BranchAWieferichOnY_default`
     を使って最小 existence wrapper へ戻す橋を置いた。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも対応する adapter alias / bridge を追加した。

3. 結論:
   - selection 側の concrete theorem 候補は、
     もはや
     `PrimeGe5BranchACyclotomicExistenceTarget`
     1 本に固定する必要はなく、
     Branch A 既存 witness を explicit に受ける
     `PrimeGe5BranchACyclotomicExistenceOnWieferichTarget`
     というより自然な statement でも扱えるようになった。
   - したがって次段では、
     Branch A 専用 existence theorem の最小形を
     - witness なしの最小 wrapper
     - witness 付きの concrete-ready wrapper
     のどちらで置くかを比較できる。

4. 検証:
   - build はこの追記の次段で
     `DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
     と
     `DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
     を順番に確認する。

5. 次の課題:
   - Branch A 専用 existence theorem を、
     `PrimeGe5BranchACyclotomicExistenceOnWieferichTarget`
     の形で先に立てるのが自然かを判断する。
   - restore 側との対称性も見ながら、
     primitive route の concrete theorem 候補を
     1 つに固定する。

### 日時: 2026/03/28 12:44 JST

1. 目的:
   - selection 側の theorem statement を、
     最小 wrapper と concrete-ready wrapper の二択から
     実装本命に固定する。
   - primitive route では、
     Branch A が既に持つ Wieferich witness を明示入力に取る
     concrete-ready 形を canonical に読む方針をコード上でも残す。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `primeGe5BranchAPrimitivePacketDescent_of_concreteSelection_and_restore`
     を追加した。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも対応する
     `branchAPrimitivePacketDescentAdapter_of_concreteSelection_and_restore`
     を追加した。
   - どちらも中身は既存の
     `...of_wieferichExistence_and_restore`
     への thin wrapper だが、
     naming と docstring で
     「primitive route の concrete-ready mainline は witness 付き selection」
     だと固定した。

3. 結論:
   - selection 側の statement は、
     API 最小形としては
     `PrimeGe5BranchACyclotomicExistenceTarget`
     を残しつつ、
     concrete 実装探索の canonical 入口は
     `PrimeGe5BranchACyclotomicExistenceOnWieferichTarget`
     と見てよい段になった。
   - したがって今後の primitive route では、
     「最小 wrapper を証明するか」
     ではなく、
     「witness 付き existence theorem をどう concrete に立てるか」
     を first target に据えられる。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 次の課題:
   - `PrimeGe5BranchACyclotomicExistenceOnWieferichTarget`
     の concrete theorem を、
     Branch A 条件と既存 cyclotomic / Zsigmondy 語彙の間で
     どう定式化するかを決める。
   - restore 側は現状の
     `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`
     を維持し、
     selection 側だけを本命 statement に固定して前進する。

### 日時: 2026/03/28 13:50 JST

1. 目的:
   - Branch A primitive route の selection 側 concrete theorem を、
     公開 diff-side existence のままではなく
     `cyclotomicPrimeCore`
     側の存在論としても読めるようにする。
   - これにより、既存 `CFBRC/Bridge` 語彙への接続点を
     theorem 名として固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `PrimeGe5BranchACyclotomicCoreExistenceOnWieferichTarget`
     を追加した。
   - 同ファイルに
     - `primeGe5BranchACyclotomicExistenceOnWieferich_of_coreExistence`
     - `primeGe5BranchAPrimitivePacketDescent_of_coreExistence_and_restore`
     を追加し、
     `cyclotomicPrimeCore p (z-y) y`
     を割る prime の存在から
     公開 diff-side existence と primitive packet descent へ戻す橋を置いた。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも対応する adapter alias / bridge を追加した。

3. 結論:
   - selection 側の concrete theorem は、
     公開 API としては
     `PrimeGe5BranchACyclotomicExistenceOnWieferichTarget`
     を保ちつつ、
     証明本体は
     `PrimeGe5BranchACyclotomicCoreExistenceOnWieferichTarget`
     を first target に置く、
     という二層構造で読むのが自然になった。
   - したがって今後の concrete 実装探索では、
     まず
     `cyclotomicPrimeCore`
     上で prime を取る theorem を狙い、
     そこから diff-side existence へ戻す方針で進められる。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 次の課題:
   - `PrimeGe5BranchACyclotomicCoreExistenceOnWieferichTarget`
     の concrete theorem を、
     `CFBRC/Bridge`
     や primitive prime existence とどう接続するかを詰める。
   - selection 側は
     `core existence -> diff existence -> packet descent`
     の spine で進め、
     restore 側は現状の target を維持する。

### 日時: 2026/03/28 14:15 JST

1. 目的:
   - `CFBRC/Bridge` の標準 existence API が
     `¬ p ∣ (z-y)`
     側に立っていることを反映し、
     Branch A (`p ∣ (z-y)`) 固有の missing theorem を
     例外枝 target として明示する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget`
     を追加した。
   - 同ファイルに
     - `primeGe5BranchACyclotomicCoreExistenceOnWieferich_of_cfbrcExceptional`
     - `primeGe5BranchAPrimitivePacketDescent_of_cfbrcExceptional_and_restore`
     を追加し、
     CFBRC 例外枝 theorem から
     `core existence -> diff existence -> packet descent`
     へ戻す橋を固定した。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも対応する provider alias / bridge を追加した。

3. 結論:
   - Branch A primitive route の selection 側で本当に missing なのは、
     もはや一般の diff-side existence でも
     一般の core-existence でもなく、
     `p ∣ (z-y)` という例外枝のもとで
     `cyclotomicPrimeCore p (z-y) y`
     に prime が立つ
     CFBRC 専用 theorem だと整理できた。
   - したがって今後の concrete 実装探索では、
     `PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget`
     を first missing theorem と見なしてよい。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 次の課題:
   - `PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget`
     の statement を、
     existing `CFBRC/Bridge` / `PrimitiveBeam`
     語彙へどこまで正規化できるかを詰める。
   - もしそれ以上の一般化が重いなら、
     Branch A 専用 exceptional theorem としてそのまま concrete 実装へ入る。

### 日時: 2026/03/28 16:03 JST

1. 目的:
   - Branch A 専用 exceptional theorem を、
     `z,y,p`
     固有の statement のままではなく
     `x := z-y`, `u := y`, `d := p`
     の CFBRC boundary-normalized 座標でも読めるようにする。
   - これにより、
     `CFBRC/Bridge` / `PrimitiveBeam`
     既存語彙への接続候補をさらに明示化する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget`
     を追加した。
   - 同ファイルに
     - `primeGe5BranchACFBRCExceptionalExistence_of_boundaryExceptional`
     - `primeGe5BranchAPrimitivePacketDescent_of_boundaryExceptional_and_restore`
     を追加し、
     boundary-normalized exceptional theorem から
     Branch A 専用 exceptional theorem、
     さらに primitive packet descent へ戻す橋を固定した。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも対応する provider alias / bridge を追加した。

3. 結論:
   - selection 側の first missing theorem は引き続き
     `PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget`
     だが、
     それは now
     `CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget`
     という boundary-normalized 形でも読める。
   - したがって次段では、
     既存 `CFBRC/Bridge`
     や `PrimitiveBeam`
     の theorem 群をこの normalized target にどこまで接続できるかを
     より直接に検討できる。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 次の課題:
   - `CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget`
     の concrete theorem が、
     既存 `CFBRC/Bridge` / `PrimitiveBeam`
     語彙の薄い補強で済むかを見極める。
   - それでも一般化が重い場合は、
     この normalized target を final missing theorem の実装形として採用する。

### 日時: 2026/03/28 16:11 JST

1. 目的:
   - selection 側の first missing theorem を、
     boundary-normalized exceptional statement
     として mainline 上でも canonical に読む wrapper を固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `primeGe5BranchAPrimitivePacketDescent_of_firstMissingSelection_and_restore`
     を追加した。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも対応する
     `branchAPrimitivePacketDescentAdapter_of_firstMissingSelection_and_restore`
     を追加した。
   - どちらも
     `...of_boundaryExceptional_and_restore`
     への thin wrapper だが、
     naming と docstring で
     `CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget`
     を selection 側の canonical first missing theorem と読む方針を固定した。

3. 結論:
   - Branch A primitive route の selection 側は、
     Branch A 専用版・CFBRC exceptional 版・boundary-normalized 版
     の 3 層を持つが、
     concrete 実装探索の既定入口は now
     `CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget`
     と見てよい。
   - したがって今後は、
     「どの statement を first target にするか」
     を迷う段ではなく、
     この normalized target をどう concrete に埋めるかに集中できる。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 次の課題:
   - `CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget`
     を、既存 `CFBRC/Bridge` / `PrimitiveBeam`
     の薄い補強で済ませられるかを実際に試す。
   - それが薄く済まないなら、
     この normalized target 自体を concrete theorem として直接実装する。

### 日時: 2026/03/28 16:26 JST

1. 目的:
   - canonical first missing theorem
     `CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget`
     を、
     既存 `CFBRC/Bridge`
     標準 theorem に最も近い stronger target 経由でも読めるようにする。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `CFBRCExceptionalPrimitiveBoundaryOnWieferichTarget`
     を追加した。
   - 同ファイルに
     - `cfbrcExceptionalBoundaryOnWieferich_of_primitiveBoundary`
     - `primeGe5BranchAPrimitivePacketDescent_of_primitiveBoundaryExceptional_and_restore`
     を追加し、
     primitive 条件つきの stronger theorem から
     current first missing theorem と primitive packet descent へ戻す橋を置いた。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも対応する provider alias / bridge を追加した。

3. 結論:
   - selection 側の first missing theorem は引き続き
     `CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget`
     だが、
     既存 `CFBRC/Bridge`
     の
     `exists_primitive_prime_factor_dvd_boundaryCore_of_prime_exp_boundary_of_coprime`
     に最も近い形として
     `CFBRCExceptionalPrimitiveBoundaryOnWieferichTarget`
     を別に持てるようになった。
   - したがって次段では、
     「薄い補強で済むか」を試すときの concrete theorem 候補として、
     primitive 条件つき stronger target も比較対象にできる。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 次の課題:
   - `CFBRCExceptionalPrimitiveBoundaryOnWieferichTarget`
     が既存 `CFBRC/Bridge` の theorem 群の
     「例外枝差し替え」だけで書けるかを検討する。
   - そこまで薄く済まないなら、
     `CFBRCExceptionalPrimeExpBoundaryOnWieferichTarget`
     を concrete theorem として直接実装する方針へ戻る。

### 日時: 2026/03/28 17:04 JST

1. 目的:
   - selection 側の primitive boundary theorem を、
     通常枝は既存 `CFBRC/Bridge`、
     例外枝だけ新 theorem、
     という split 形で mainline 上に固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     - `CFBRCPrimitiveBoundarySelectionOnSplitTarget`
     - `cfbrcExceptionalPrimitiveBoundaryOnWieferich_of_split`
     - `cfbrcPrimitiveBoundarySelectionOnSplit_of_exceptional`
     - `primeGe5BranchAPrimitivePacketDescent_of_splitSelection_and_restore`
     を追加した。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも
     - `CFBRCPrimitiveBoundarySelectionOnSplitAdapterTarget`
     - `branchAPrimitivePacketDescentAdapter_of_splitSelection_and_restore`
     を追加した。

3. 結論:
   - primitive selection 側は、
     「通常枝は `exists_primitive_prime_factor_dvd_boundaryCore_of_prime_exp_boundary_of_coprime`」
     と
     「例外枝は `CFBRCExceptionalPrimitiveBoundaryOnWieferichTarget`」
     の split 合成として読めるようになった。
   - これにより、
     current missing math が本当に例外枝 1 本だけだと
     theorem としても明示された。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 次の課題:
   - `CFBRCExceptionalPrimitiveBoundaryOnWieferichTarget`
     を、
     split theorem の例外枝として concrete に埋める。
   - その際、
     `CFBRC/Bridge` / `PrimitiveBeam`
     の通常枝 theorem と対照的に見える statement を保つ。

### 日時: 2026/03/28 17:18 JST

1. 目的:
   - split theorem の右枝を、
     既存 `CFBRC/Bridge`
     theorem 名に最も近い concrete theorem 候補名で固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `CFBRCExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferichTarget`
     を追加した。
   - 同ファイルに
     - `cfbrcExceptionalPrimitiveBoundaryOnWieferich_of_coreExceptional`
     - `cfbrcExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferich_of_exceptional`
     - `primeGe5BranchAPrimitivePacketDescent_of_coreExceptional_and_restore`
     を追加し、
     既存 exceptional target との alias bridge と packet-descent bridge を置いた。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも
     対応する adapter alias / bridge を追加した。

3. 結論:
   - selection 側の right branch は、
     単に internal target としてでなく、
     `exists_primitive_prime_factor_dvd_boundaryCore_of_prime_exp_boundary_of_coprime`
     に対応する
     exceptional concrete theorem 候補名でも読めるようになった。
   - これで次段では、
     どの theorem 名で concrete 実装を立てるかで迷わずに済む。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 次の課題:
   - `CFBRCExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferichTarget`
     自体を concrete に埋められるかを試す。
   - もし naming だけでは足りないなら、
     この target の statement をもう少し
     `CFBRC/Bridge`
     の仮定順・語彙順へ寄せる。

### 日時: 2026/03/28 17:31 JST

1. 目的:
   - right branch だけでなく split theorem 全体も、
     `CFBRC/Bridge`
     naming に揃えた concrete theorem 候補名で読めるようにする。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `CFBRCPrimitiveBoundaryCoreOfPrimeExpSelectionOnSplitTarget`
     を追加した。
   - 同ファイルに
     - `cfbrcPrimitiveBoundaryCoreOfPrimeExpSelectionOnSplit_of_coreExceptional`
     - `cfbrcPrimitiveBoundaryCoreOfPrimeExpSelectionOnSplit_of_split`
     - `primeGe5BranchAPrimitivePacketDescent_of_coreSplitSelection_and_restore`
     を追加した。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも
     対応する adapter alias / bridge を追加した。

3. 結論:
   - selection 側は now
     - right branch の concrete theorem 候補
       `CFBRCExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferichTarget`
     - split theorem 全体の concrete theorem 候補
       `CFBRCPrimitiveBoundaryCoreOfPrimeExpSelectionOnSplitTarget`
     の 2 層で読める。
   - これにより、
     concrete 実装探索を
     `CFBRC/Bridge`
     theorem 名とほぼ平行な naming で進められるようになった。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 次の課題:
   - `CFBRCExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferichTarget`
     と
     `CFBRCPrimitiveBoundaryCoreOfPrimeExpSelectionOnSplitTarget`
     のうち、
     どちらを direct concrete theorem として先に立てるのが自然かを見極める。
   - 必要なら
     exceptional 側の statement を
     `BoundarySide.right`
     を明示した既存 theorem の仮定順へさらに寄せる。

### 日時: 2026/03/28 17:44 JST

1. 目的:
   - concrete theorem 候補が
     right branch と split 全体の二層で揃った状態から、
     first direct target を 1 本に固定する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `CFBRCPrimitiveBoundaryCoreOfPrimeExpDirectConcreteTarget`
     を追加した。
   - 同ファイルに
     `primeGe5BranchAPrimitivePacketDescent_of_directConcreteSelection_and_restore`
     を追加し、
     direct concrete 既定入口から packet descent へ行く thin bridge を置いた。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも
     対応する adapter alias / bridge を追加した。

3. 結論:
   - `review-016`
     の判断どおり、
     first に direct concrete 実装を狙う既定入口は
     `CFBRCExceptionalPrimitiveBoundaryCoreOfPrimeExpOnWieferichTarget`
     系だと名前の上でも固定された。
   - split 全体の concrete theorem 候補は保持するが、
     mainline の “first direct target”
     はもう right branch に決め打ちできる。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 次の課題:
   - `CFBRCPrimitiveBoundaryCoreOfPrimeExpDirectConcreteTarget`
     を concrete に埋める。
   - 必要なら、
     この target の仮定順と命名を
     `CFBRC/Bridge`
     の通常枝 theorem とさらに平行に揃える。

### 日時: 2026/03/28 18:02 JST

1. 目的:
   - first direct concrete target
     `CFBRCPrimitiveBoundaryCoreOfPrimeExpDirectConcreteTarget`
     を、そのまま証明するのでなく
     `prime existence`
     と
     `primitive kernel`
     の 2 段へ分解する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     - `CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget`
     - `CFBRCExceptionalPrimitiveKernelOnWieferichTarget`
     - `cfbrcExceptionalBoundaryCorePrimeExistenceOnWieferich_of_directConcrete`
     - `cfbrcPrimitiveBoundaryCoreOfPrimeExpDirectConcrete_of_existence_and_kernel`
     - `primeGe5BranchAPrimitivePacketDescent_of_directConcreteParts_and_restore`
     を追加した。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも
     対応する provider alias / bridge を追加した。

3. 結論:
   - direct concrete target の missing math は、
     いまや
     - `boundaryCyclotomicPrimeCore` を割る prime の existence
     - その prime が低次 boundary 差分を割らない primitive kernel
     の 2 本へ分解された。
   - したがって次に詰めるべき数学が
     existence 側か primitive 側かを、
     theorem の形で直接判定できるようになった。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 次の課題:
   - `CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget`
     が既存 `CFBRC/Bridge` / `PrimitiveBeam`
     語彙へどこまで寄せられるかを試す。
   - 同時に
     `CFBRCExceptionalPrimitiveKernelOnWieferichTarget`
     が単なる既存 primitive 条件の再包装かどうかを見極める。

### 日時: 2026/03/28 18:16 JST

1. 目的:
   - direct concrete target のうち existence 側も、
     通常枝と Wieferich 例外枝の split で読めるようにする。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `CFBRCBoundaryCorePrimeExistenceOnSplitTarget`
     を追加した。
   - 同ファイルに
     - `cfbrcExceptionalBoundaryCorePrimeExistenceOnWieferich_of_split`
     - `cfbrcBoundaryCorePrimeExistenceOnSplit_of_exceptional`
     - `primeGe5BranchAPrimitivePacketDescent_of_splitExistence_kernel_and_restore`
     を追加した。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも
     対応する provider alias / bridge を追加した。

3. 結論:
   - existence 側 missing math も、
     theorem の形で
     「通常枝は既存 `CFBRC/Bridge`、例外枝だけ新 theorem」
     と読めるようになった。
   - これにより、
     existence 側の本当の missing math も
     right branch 1 本だけだとさらに明確になった。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 次の課題:
   - `CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget`
     を、
     既存 `CFBRC/Bridge`
     theorem の例外枝差し替えだけでどこまで書けるかを試す。
   - primitive kernel 側がもし既存 theorem の再包装なら、
     selection 側の truly new kernel は existence 1 本だけになる。

### 日時: 2026/03/28 18:31 JST

1. 目的:
   - `CFBRCExceptionalPrimitiveKernelOnWieferichTarget`
     が既存 primitive 条件定理の再包装だけで済むかを確定し、
     selection 側の truly new kernel を existence 右枝 1 本へさらに絞る。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `cfbrcExceptionalPrimitiveKernelOnWieferich_default`
     を追加した。
   - 同定理では
     `q ∣ boundaryCyclotomicPrimeCore .right d x u`
     と
     `¬ q ∣ x`
     から
     `q ∣ ((x+u)^d-u^d)`
     を戻し、
     `prime_exp_not_dvd_diff_imp_primitive`
     を直接適用している。
   - さらに
     - `cfbrcPrimitiveBoundaryCoreOfPrimeExpDirectConcrete_of_existence`
     - `primeGe5BranchAPrimitivePacketDescent_of_directConcreteExistence_and_restore`
     - `primeGe5BranchAPrimitivePacketDescent_of_splitExistence_and_restore`
     を追加し、
     primitive kernel を explicit 仮定から外した wrapper を入れた。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも対応する provider adapter を追加した。

3. 結論:
   - `CFBRCExceptionalPrimitiveKernelOnWieferichTarget`
     は new kernel ではなく、
     既存 `CFBRC/Bridge` + `GcdNext`
     の primitive 条件定理で default 実装できると確定した。
   - したがって selection 側の truly new missing math は、
     さらに強く
     `CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget`
     1 本だと読めるようになった。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 次の課題:
   - `CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget`
     を、既存 `CFBRC/Bridge`
     の ordinary branch と最も平行な形へさらに正規化できるかを見る。
   - そのうえで、
     この target 自体の concrete theorem をどこに置くか
     (`CFBRC/Bridge` か `BranchA` 局所か)
     を決める。

### 日時: 2026/03/28 18:44 JST

1. 目的:
   - existence 右枝 1 本へ絞れた missing kernel を、
     既存 `CFBRC/Bridge`
     の ordinary branch theorem とできるだけ平行な concrete 名で読む。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     `CFBRCExceptionalPrimeFactorDvdBoundaryCoreOfPrimeExpBoundaryOnWieferichTarget`
     を追加した。
   - 同ファイルに
     - `cfbrcExceptionalPrimeFactorDvdBoundaryCoreOfPrimeExpBoundaryOnWieferich_of_existence`
     - `cfbrcExceptionalBoundaryCorePrimeExistenceOnWieferich_of_parallelExceptional`
     - `primeGe5BranchAPrimitivePacketDescent_of_parallelExceptionalExistence_and_restore`
     を追加した。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも対応する provider alias / adapter を追加した。

3. 結論:
   - truly new kernel は引き続き existence 右枝 1 本だが、
     その theorem 名は
     `exists_primitive_prime_factor_dvd_boundaryCore_of_prime_exp_boundary_of_coprime`
     の exceptional parallel として読めるところまで正規化された。
   - これで次の論点は、
     「この concrete theorem を `CFBRC/Bridge` 側へ置くか、
     Branch A 局所に留めるか」
     へさらに絞られた。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を順番に実行し、build 完了まで待って成功を確認する。

5. 次の課題:
   - `CFBRCExceptionalPrimeFactorDvdBoundaryCoreOfPrimeExpBoundaryOnWieferichTarget`
     を direct concrete theorem の canonical 名として採用するかを決める。
   - その上で、
     `CFBRC/Bridge`
     側へ最小補強として移す余地があるかを見る。
