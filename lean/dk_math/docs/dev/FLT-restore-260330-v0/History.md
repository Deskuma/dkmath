# History

- 時刻の打刻は時間(時分秒)まで正確に行うこと。
- 新規履歴は最終末尾に追加すること。

## History Log

Archive

- None

### 日時: 2026/03/30 13:18 JST

1. 目的:
   - `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`
     の数学的構造を精密に解析し、証明可能性を判定する。
   - 偽枝チェック（前回 `BodyCoreWitness` で有効だったパターン）。
   - 証明戦略がある場合は、分割計画を立てる。

2. 実施:
   - `TriominoCosmicBranchA.lean` から target の full signature を精読。

     ```
     ∀ {p x y z t s}, Pack p x y z →
       p ∣ (z-y) → z-y = p^(p-1)*t^p → GN = p*s^p → x = p*(t*s) →
       Coprime(t,s) → Coprime(t,y) → Coprime(s,y) →
       ¬p∣s → ¬p∣t → y^(p-1) ≡ 1 [MOD p²] →
       ∀ {q}, Prime q → q∣s → ¬q∣t → Coprime(q,y) → q≠p →
       ∃ pkt' : NormalFormPacket p, pkt'.z < z
     ```

   - 上流の dependency chain を 全て調査:
     - `PrimitiveZsigmondyTarget` → cyclotomic existence → **証明済み**
     - `DistinguishedPrimeArithmeticTarget` → **`..._default` で証明済み**
     - `PrimitivePacketRestoreFromArithmeticTarget` → **未証明** ← ここ
   - `NormalFormPacket` の構造を確認:
     - `x', y', z', t', s'` + `Pack p x' y' z'`
     - `p ∣ (z'-y')`, `z'-y' = p^{p-1}*t'^p`, `GN(p,z'-y',y') = p*s'^p`
     - `x' = p*(t'*s')`, `z' < z`
   - 偽枝チェック: 前回式の「前提が `u=1` で壊れる」パターンは非該当。
     - 前提に FLT 反例の存在が含まれるため、Wiles の定理により前提自体が偽。
     - したがって反例による偽判定は不可能（FLT 反例が存在しないため）。
   - 数学的構造分析を実施（下記 §3 結論参照）。

3. 結論:

   **§A. target は偽ではない（前回の `BodyCoreWitness` とは異なる）**
   - `BodyCoreWitness` は `(d,x,u)=(5,5,1)` という具体反例で偽と確定した。
   - 一方 `RestoreFromArithmetic` の前提は FLT 反例の存在を含む。
     Wiles の定理により FLT 反例は存在しないため、
     前提が偽 → 命題は vacuously true。
   - ただし我々は FLT の Lean 形式化中なので、Wiles は使えない。
   - 具体的な偽反例を提示することは構造的に不可能。

   **§B. target は FLT の infinite descent の深い核を encode している**
   - 既存の architecture:

     ```
     SmallerPacket = ValuationPeel (p∣t) ∨ PrimitivePacketDescent (¬p∣t)
     PrimitivePacketDescent ← WieferichPacket ← DistinguishedPrime + Restore
     DistinguishedPrime ← Zsigmondy ← CyclotomicExistence [✅ 証明済み]
     Restore ← Arithmetic [✅ 証明済み] + RestoreFromArithmetic [❌ ここ]
     ```

   - `RestoreFromArithmetic` は「原始素因子 witness q から、より小さい反例を再構成する」部分。
   - これは classical FLT descent の本丸そのもの。

   **§C. witness q の構造的性質（新発見）**
   - `q ∣ s` → `q ∣ x` （∵ `x = p*t*s`）
   - `q ∤ t` → `q ∤ (z-y)` （∵ `z-y = p^{p-1}*t^p`, `q ≠ p`）
   - `Coprime(q,y)` → `q ∤ y`
   - `x^p + y^p = z^p`, `q ∣ x`, `q ∤ y` → `z^p ≡ y^p [MOD q]` → `q ∤ z`
   - **`q ∤ (z-y)` かつ `z^p ≡ y^p [MOD q]` のとき:**
     - `(z·y⁻¹)^p ≡ 1 [MOD q]` で `z·y⁻¹ ≢ 1 [MOD q]`
       （もし `z ≡ y [MOD q]` なら `q ∣ (z-y)` で矛盾）
     - ゆえに `z·y⁻¹` は `(ℤ/qℤ)*` における非自明な p 乗根
     - **これは `p ∣ (q-1)` すなわち `q ≡ 1 [MOD p]` を要求する**
   - さらに `v_q(x^p) = p·v_q(s) ≥ p` なので `z^p ≡ y^p [MOD q^p]`
   - つまり `z·y⁻¹` は `(ℤ/q^pℤ)*` における p 乗根でもある

   **§D. 証明戦略候補**

   (D1) **円分整数環 ℤ[ζ_p] 経由**（古典的 Kummer 理論）
   - `q ≡ 1 [MOD p]` なので `q` は ℤ[ζ_p] で完全分解する
   - `x^p + y^p = ∏(x + ζ^{2j+1}y)` のイデアル分解から smaller solution を抽出
   - 必要: Mathlib の cyclotomic field / number field 基盤
   - 障害: 正則素数仮定が必要（一般の p では class number 問題）

   (D2) **Cosmic Formula の構造的 descent**（本プロジェクト独自）
   - GN = p*s^p の内部構造と q の関係から新しい pack を構成
   - `GTail` の再帰構造を使って因子を分離する
   - 障害: NormalFormPacket の全フィールドを同時に満たす構成が必要

   (D3) **target の分割・弱化**
   - RestoreFromArithmetic を更に細かい sub-target に分割する
   - 例: まず `∃ x' y' z', x'^p + y'^p = z'^p ∧ z' < z` だけを示し、
     normal form は別の補題で保証する
   - `PrimeGe5BranchASmallerCounterexampleTarget` への reduce も候補

   (D4) **前提からの直接矛盾**
   - 前提の組み合わせが inconsistent であることを示す
     （= 本当に smaller packet を構成するのではなく、`False.elim` で閉じる）
   - `q ≡ 1 [MOD p]` と他の条件から矛盾が導けるか？
   - 現時点では矛盾は見つかっていない

4. 検証:
   - 上流 chain の sorry 状況を再確認:
     - `BranchAExceptional.lean`: sorry 0
     - `GapInvariant.lean`: sorry 0（コード内）
     - `BranchA.lean`: sorry 1（L3936, comparison route 末端のマーカー）
   - 全体の定理数: 1,316 (前回比 +53)
   - `lake build` は前回セッションで全成功を確認済み

5. 失敗事例:
   - `BodyCoreWitness` 式の即座偽判定は適用不可（前提に FLT 反例を含む）
   - valuation 引数（「各項の v_q = 0 なら和の v_q = 0」）は誤り:
     正の整数の和では `v_q(a+b) ≥ min(v_q(a), v_q(b))` だが
     `v_q(a+b) > min(...)` もありうる（例: `v_3(1+2) = v_3(3) = 1`）

6. 次の課題:
   - `q ≡ 1 [MOD p]` の Lean 補題を実装する（証明可能、有用）
   - D3 route: target を sub-target に分割する設計
   - D4 route: 前提矛盾の可能性をさらに深掘りする
   - ValuationPeel 側の `PacketFromErrorTarget` の未実装状況も確認する

### 日時: 2026/03/30 14:30 JST

1. 目的:
   - `q ≡ 1 [MOD p]` structural lemma を Lean で実装する。
   - FLT 等式から ZMod q での計算を経由し、orderOf 理論で `p ∣ (q-1)` を形式化する。

2. 実施:
   - `TriominoCosmicBranchA.lean` に §R (Restore structural lemmas) セクションを新設。
   - 以下の 5 定理 + 1 構造体を sorry なしで実装：
   - (a) `flt_zpow_congr_mod_of_dvd_x`: `q ∣ x` → `z^p ≡ y^p [MOD q]`
   - (b) `flt_not_dvd_z_of_dvd_x_not_dvd_y`: `q ∣ x`, `q ∤ y` → `q ∤ z`
   - (c) `flt_zmod_ne_of_not_dvd_gap`: ZMod q 上の非等式
   - (d) `restore_witness_cong_one_mod_p` (本丸): `p ∣ (q - 1)`
   - (e) `RestoreWitnessProperties` (構造体): witness q の全性質バンドル
   - (f) `restore_witness_properties_default`: 一括構成

3. 結論:
   - 5 定理 + 1 構造体、sorry 0 で全て通った。
   - `lake build` 成功。error 0、新しい warning 0。
   - BranchA.lean: 5033 行 → 5267 行（+234 行）

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA` 成功

5. 失敗事例:
   - Nat 上の `z^p - y^p = x^p` を omega で通そうとして失敗（非線形）
   - `Nat.modEq_iff_dvd'` 経由が不発 → `Nat.ModEq.add_right` + `simpa` が正解
   - 旧 API 名との格闘: natCast_zmod_eq_zero_iff_dvd → natCast_eq_zero_iff
   - `Fact (Nat.Prime q)` が orderOf_eq_prime に必要（haveI で局所設定）

6. 次の課題:
   - `RestoreFromArithmetic` の sub-target 分割設計
   - q-adic valuation 精密化の形式化
   - `(z·y⁻¹)` の `(ℤ/q^pℤ)*` における p 乗根としての性質

### 日時: 2026/03/30 15:24:23 JST

1. 目的:
   - `dev-report.md`
     の方針どおり、
     `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`
     を
     sub-target に分割する。
   - 特に、
     「smaller counterexample の構成」
     と
     「normal-form packet への包装」
     を別 target として切り出す。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     に
     - `PrimeGe5BranchAPrimitiveSmallerCounterexampleFromArithmeticTarget`
     - `PrimeGe5BranchAPrimitivePacketOfSmallerCounterexampleTarget`
     を追加した。
   - さらに
     `primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_smallerCounterexample_and_packet`
     を追加し、
     2 段の sub-target から
     `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`
     を再合成できるようにした。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも
     対応する provider 側 alias
     - `BranchAPrimitiveSmallerCounterexampleFromArithmeticAdapterTarget`
     - `BranchAPrimitivePacketOfSmallerCounterexampleAdapterTarget`
     と、
     再合成橋
     `branchAPrimitivePacketRestoreFromArithmeticAdapter_of_smallerCounterexample_and_packet`
     を追加した。

3. 結論:
   - `RestoreFromArithmetic`
     の未完核は、
     もはや 1 本の巨大 target ではなく、
     - smaller counterexample existence
     - smaller packet packaging
     の 2 段へ局所化された。
   - したがって今後の concrete 証明探索では、
     「どちらの段が真の難所か」を
     個別に追跡できる。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 次の課題:
   - `PrimeGe5BranchAPrimitiveSmallerCounterexampleFromArithmeticTarget`
     の statement をさらに弱化できるか検討する。
   - あるいは
     `PrimeGe5BranchAPrimitivePacketOfSmallerCounterexampleTarget`
     を別ファイル / 別 route へ移して、
     packaging 専用 kernel として育てる。

### 日時: 2026/03/30 15:37:45 JST

1. 目的:
   - `review-003`
     の指摘どおり、
     ここから先の restore work を
     新しい `*.lean` file
     に切り出して進める。
   - `TriominoCosmicBranchA.lean`
     本体は base definitions を保持し、
     restore 固有の今後の構築先だけを別 module に分離する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean]`
     を新規作成した。
   - この file では
     - `PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget`
     - `PrimeGe5BranchAPrimitiveRestorePacketPackagingTarget`
     - `primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_restoreSubtargets`
     を定義し、
     restore の sub-target 2 本と再合成橋を
     canonical 名で受け直せるようにした。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも
     `TriominoCosmicBranchARestore`
     を import 追加した。

3. 結論:
   - 以後の restore 段の concrete 実装は、
     `TriominoCosmicBranchARestore.lean`
     を主たる構築先として進められる。
   - `TriominoCosmicBranchA.lean`
     には base target 群を残しつつ、
     新しい proof exploration の edit surface を
     別 file に分離できた。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 次の課題:
   - `TriominoCosmicBranchARestore.lean`
     で
     `PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget`
     の更なる分割、
     ないし concrete 補題化を進める。

### 日時: 2026/03/30 15:49:37 JST

1. 目的:
   - `review-004`
     の方針どおり、
     restore arithmetic core を
     さらに
     - residue/root 段
     - descent assembly 段
     に分割する。
   - 既に証明済みの
     `RestoreWitnessProperties`
     を canonical datum として固定し、
     真の未完核を assembly 側 1 本へ押し込む。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean]`
     に
     - `PrimeGe5BranchAPrimitiveRestoreResidueRootTarget`
     - `PrimeGe5BranchAPrimitiveRestoreDescentAssemblyTarget`
     - `primeGe5BranchAPrimitiveRestoreResidueRoot_default`
     - `primeGe5BranchAPrimitiveRestoreArithmeticCore_of_residueRoot_and_descentAssembly`
     を追加した。
   - residue/root 段の default 実装は
     `restore_witness_properties_default`
     をそのまま用いた。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも
     対応する provider alias / adapter を追加した。

3. 結論:
   - restore arithmetic core は、
     もはや巨大な 1 本ではなく、
     - residue/root data の抽出
     - datum から smaller counterexample を組む assembly
     の 2 段へ局所化された。
   - しかも前者は default 実装済みなので、
     現在の genuinely new kernel は
     `PrimeGe5BranchAPrimitiveRestoreDescentAssemblyTarget`
     1 本として読める。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 次の課題:
   - `PrimeGe5BranchAPrimitiveRestoreDescentAssemblyTarget`
     の statement をさらに arithmetic-only seed へ削れるか検討する。
   - あるいは
     `RestoreWitnessProperties`
     から smaller counterexample へ行く中間 datum を structure 化する。

### 日時: 2026/03/30 15:58:20 JST

1. 目的:
   - `PrimeGe5BranchAPrimitiveRestoreDescentAssemblyTarget`
     を、
     `review-004`
     の見立てどおり
     - q-adic lift 段
     - smaller-counterexample assembly 段
     にさらに分割する。
   - residue/root から
     `ZMod q`
     上の nontrivial `p`-torsion witness が
     default で回収できることを明示する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean]`
     に
     - `PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed`
     - `PrimeGe5BranchAPrimitiveRestoreQAdicLiftTarget`
     - `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleAssemblyTarget`
     - `primeGe5BranchAPrimitiveRestoreQAdicLift_default`
     - `primeGe5BranchAPrimitiveRestoreDescentAssembly_of_qAdicLift_and_smallerCounterexampleAssembly`
     を追加した。
   - `primeGe5BranchAPrimitiveRestoreQAdicLift_default`
     では
     `restore_witness_cong_one_mod_p`
     の証明内容と同型の
     `ω := z * y⁻¹ ∈ ZMod q`
     を再構成し、
     `ω ^ p = 1` かつ `ω ≠ 1`
     を返すようにした。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも
     - `BranchAPrimitiveRestoreQAdicLiftAdapterTarget`
     - `BranchAPrimitiveRestoreSmallerCounterexampleAssemblyAdapterTarget`
     - `branchAPrimitiveRestoreQAdicLiftAdapter_default`
     - `branchAPrimitiveRestoreDescentAssemblyAdapter_of_qAdicLift_and_smallerCounterexampleAssembly`
     を追加した。

3. 結論:
   - restore arithmetic core は、
     もはや
     - residue/root
     - q-adic lift
     - smaller-counterexample assembly
     の 3 段へ読める。
   - しかも前 2 段は default 実装済みなので、
     現在の genuinely new kernel は
     `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleAssemblyTarget`
     1 本へさらに局所化された。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 次の課題:
   - `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleAssemblyTarget`
     の statement をさらに
     smaller-counterexample seed
     へ削れるか検討する。
   - あるいは
     `PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed`
     から直接得るべき
     arithmetic descent datum
     を structure 化する。

### 日時: 2026/03/30 16:11:49 JST

1. 目的:
   - `review-005`
     の見立てどおり、
     `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleAssemblyTarget`
     を
     - bundled descent datum の作成段
     - datum から smaller counterexample を作る段
     にさらに分割する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean]`
     に
     - `PrimeGe5BranchAPrimitiveRestoreDescentDatum`
     - `PrimeGe5BranchAPrimitiveRestoreDescentDatumTarget`
     - `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromDescentDatumTarget`
     - `primeGe5BranchAPrimitiveRestoreDescentDatum_default`
     - `primeGe5BranchAPrimitiveRestoreSmallerCounterexampleAssembly_of_descentDatum_and_fromDatum`
     を追加した。
   - datum は
     `RestoreWitnessProperties`
     と
     `PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed`
     を 1 つに束ねる structure とした。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも
     - `BranchAPrimitiveRestoreDescentDatumAdapterTarget`
     - `BranchAPrimitiveRestoreSmallerCounterexampleFromDescentDatumAdapterTarget`
     - `branchAPrimitiveRestoreDescentDatumAdapter_default`
     - `branchAPrimitiveRestoreSmallerCounterexampleAssemblyAdapter_of_descentDatum_and_fromDatum`
     を追加した。

3. 結論:
   - restore arithmetic core は、
     もはや
     - residue/root
     - q-adic lift
     - descent datum bundling
     - datum consumer
     の 4 段へ読める。
   - しかも前 3 段は default / bridge で閉じるので、
     現在の genuinely new kernel は
     `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromDescentDatumTarget`
     1 本として読める。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 次の課題:
   - `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromDescentDatumTarget`
     の statement を、
     さらに smaller-counterexample seed へ削れるか検討する。
   - あるいは
     `PrimeGe5BranchAPrimitiveRestoreDescentDatum`
     自体の field を、
     実際の descent 組立てで必要な arithmetic datum に寄せて精密化する。

### 日時: 2026/03/30 16:22:14 JST

1. 目的:
   - `review-006`
     の方針どおり、
     datum consumer
     `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromDescentDatumTarget`
     を
     - descent seed 抽出段
     - seed realization 段
     にさらに分割する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean]`
     に
     - `PrimeGe5BranchAPrimitiveRestoreDescentSeed`
     - `PrimeGe5BranchAPrimitiveRestoreDescentSeedTarget`
     - `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromSeedTarget`
     - `primeGe5BranchAPrimitiveRestoreDescentSeed_default`
     - `primeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromDescentDatum_of_descentSeed_and_fromSeed`
     を追加した。
   - 現段階の `DescentSeed` は、
     `DescentDatum`
     を minimal に包み直す seed として置いた。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも
     - `BranchAPrimitiveRestoreDescentSeedAdapterTarget`
     - `BranchAPrimitiveRestoreSmallerCounterexampleFromSeedAdapterTarget`
     - `branchAPrimitiveRestoreDescentSeedAdapter_default`
     - `branchAPrimitiveRestoreSmallerCounterexampleFromDescentDatumAdapter_of_descentSeed_and_fromSeed`
     を追加した。

3. 結論:
   - restore arithmetic core は、
     もはや
     - residue/root
     - q-adic lift
     - descent datum bundling
     - descent seed extraction
     - seed realization
     の 5 段へ読める。
   - しかも前 4 段は default / bridge で閉じるので、
     現在の genuinely new kernel は
     `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromSeedTarget`
     1 本へさらに局所化された。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 次の課題:
   - `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromSeedTarget`
     の statement を、
     さらに actual smaller-counterexample realization の局所 kernel へ削れるか検討する。
   - あるいは
     `PrimeGe5BranchAPrimitiveRestoreDescentSeed`
     自体の field を、
     seed realization に必要な arithmetic data に寄せて精密化する。

### 日時: 2026/03/30 16:38:51 JST

1. 目的:
   - `review-007`
     の方針どおり、
     seed realization
     `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromSeedTarget`
     を
     - realization-seed 抽出段
     - candidate verification 段
     にさらに分割する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean]`
     に
     - `PrimeGe5BranchAPrimitiveRestoreRealizationSeed`
     - `PrimeGe5BranchAPrimitiveRestoreRealizationSeedTarget`
     - `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleVerificationTarget`
     - `primeGe5BranchAPrimitiveRestoreRealizationSeed_default`
     - `primeGe5BranchAPrimitiveRestoreSmallerCounterexampleFromSeed_of_realizationSeed_and_verification`
     を追加した。
   - `RealizationSeed`
     には
     `DescentSeed`
     と candidate triple
     `x' y' z'`
     を束ねる形を採った。
   - 現段階の default 実装は、
     `x' := x`, `y' := y`, `z' := z`
     を仮候補として包む thin wrapper である。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     にも
     - `BranchAPrimitiveRestoreRealizationSeedAdapterTarget`
     - `BranchAPrimitiveRestoreSmallerCounterexampleVerificationAdapterTarget`
     - `branchAPrimitiveRestoreRealizationSeedAdapter_default`
     - `branchAPrimitiveRestoreSmallerCounterexampleFromSeedAdapter_of_realizationSeed_and_verification`
     を追加した。

3. 結論:
   - restore arithmetic core は、
     もはや
     - residue/root
     - q-adic lift
     - descent datum bundling
     - descent seed extraction
     - realization-seed extraction
     - candidate verification
     の 6 段へ読める。
   - しかも前 5 段は default / bridge で閉じるので、
     現在の genuinely new kernel は
     `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleVerificationTarget`
     1 本へさらに局所化された。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`
   を完了まで待って実行し、成功を確認した。

5. 次の課題:
   - `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleVerificationTarget`
     の statement を、
     candidate triple の個別 field 検証へさらに割れるか検討する。
   - あるいは
     `PrimeGe5BranchAPrimitiveRestoreRealizationSeed`
     の field を、
     verification に必要な partial proof data に寄せて精密化する。

### 日時: 2026/03/30 17:10:00 JST

1. 目的:
   - VSCode クラッシュからの作業継続。
   - `review-008` の判定どおり、
     `RealizationSeed` を `x'/y'` の数学的根拠付き構造体へ精密化する。
   - `VerificationTarget` を 3 分割する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`
     - `RestoreWitnessProperties` に `hqp_dvd_GN : q^p ∣ GN p (z-y) y`
       を追加し（6 フィールド化）、
       対応する補題 `branchA_qpow_dvd_GN` を no-sorry で実装した（6 フィールド化）。
     - `restore_witness_properties_default` に `hsGN` 引数を追加し、
       `hqp_dvd_GN` フィールドへの供給路を確立した。
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean]`
     - `PrimeGe5BranchAPrimitiveRestoreRealizationSeed` に
       `hxMul : x = q * x'`（`q ∣ x` の証拠）と
       `hyEq : y' = y`（y 不変の証拠）を追加した。
     - `primeGe5BranchAPrimitiveRestoreRealizationSeed_default` を更新し、
       `x' := k`（`x = q * k` を展開）、`y' := y` を数学的根拠で固定した。
     - `VerificationTarget` を以下 3 段に分割した：
       - `PrimeGe5BranchAPrimitiveRestoreStrictDescentTarget`（`z' < z`）
       - `PrimeGe5BranchAPrimitiveRestoreGapDivisibilityTarget`（`p ∣ (z' - y')`）
       - `PrimeGe5BranchAPrimitiveRestoreCounterexamplePackTarget`（`Pack p x' y' z'`）
     - 橋定理 `primeGe5BranchAPrimitiveRestoreSmallerCounterexampleVerification_of_three_parts`
       で旧 `VerificationTarget` を統合した。

3. 結論:
   - `x' = x/q`, `y' = y` が `RealizationSeed` に数学的根拠付きで固定された。
   - verification の 3 段分割が完了し、hardest kernel が
     `CounterexamplePackTarget` に局所化された。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA` 成功
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore` 成功
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant` 成功
   - sorry 増加なし（`BranchA.lean` の L3981 のみ）

5. 次の課題:
   - `RealizationSeed` に `hzEq : x'^p + y'^p = z'^p` を追加し、
     3 段を no-sorry で閉じる。

### 日時: 2026/03/30 17:40:00 JST

1. 目的:
   - `review-009` の方針どおり、
     `RealizationSeed` に `hzEq : x'^p + y'^p = z'^p` を追加して
     `z'` の算術的定義式を evidence として持たせる。
   - `hzEq` を前提として
     `StrictDescentTarget`・`GapDivisibilityTarget`・`CounterexamplePackTarget`
     の 3 段を no-sorry で証明する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean]`
     - `PrimeGe5BranchAPrimitiveRestoreRealizationSeed` に
       `hzEq : x'^p + y'^p = z'^p` を追加した。
     - `primeGe5BranchAPrimitiveRestoreRealizationSeed_default` を削除
       （`hzEq` を持てないため薄い wrapper が成立しなくなった）。
       代わりに open kernel であることをコメントで明示した。
     - 以下の 3 定理を no-sorry で実装した：
       - `primeGe5BranchAPrimitiveRestoreStrictDescent_of_hzEq`
         - `z^p = q^p * x'^p + y^p`、`z'^p = x'^p + y'^p`
         - 差は `(q^p - 1) * x'^p > 0` → `z' < z`（冪単調性）
       - `primeGe5BranchAPrimitiveRestoreGapDivisibility_of_hzEq`
         - `gcd(p,q) = 1` → `p ∣ x'`
         - ZMod Frobenius（フェルマーの小定理）`a^p = a`
         - `hzEq` を ZMod p へ cast → `z' ≡ y' (mod p)` → `p ∣ (z' - y')`
       - `primeGe5BranchAPrimitiveRestoreCounterexamplePack_of_hzEq`
         - `hzEq` そのものが `hEq`
         - `x' ∣ x` と `Coprime x y` → `Coprime x' y'`
         - `0 < x'` と `hzEq` → `y' < z'`（冪単調性）
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     - 削除された `primeGe5BranchAPrimitiveRestoreRealizationSeed_default` への
       参照を open kernel コメントで置換した。

3. 結論:
   - `RealizationSeed` が「candidate triple + arithmetic evidence」の
     構造体として完成した。
   - 3 段の verification がすべて no-sorry で証明された。
   - genuinely undischarged kernel は以下の 1 本のみに収束した：

     ```
     PrimeGe5BranchAPrimitiveRestoreRealizationSeedTarget
       : ∃ z', (x/q)^p + y^p = z'^p
     ```

     この命題の existence 証明が FLT descent の真の核心である。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore` 成功
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant` 成功
   - sorry 数：BranchARestore.lean = 0（コード内）
   - BranchA.lean の既存 sorry は L3981 の 1 箇所のみ（変更なし）

5. 失敗事例:
   - `hR.hxMul ▸ hx_pos` → Lean の依存型問題で motive error
     → `hR.hxMul ▸` を使わず `Nat.pos_of_mul_pos_left` で回避
   - `Nat.pos_pow_of_pos` が Mathlib に存在しない → `pow_pos` を使用
   - `Nat.one_le_iff_ne_zero.mpr hpack.hp.ne_zero` → `omega` で `1 ≤ p` を使い回避
   - `congr 1; omega` でフェルマーの小定理の exponent 計算 `p - 1 + 1 = p` が成立
   - `hpack.hy0 : y ≠ 0` を `hR.y' ≠ 0` に使えない → `rw [hR.hyEq]` で変換
   - `rw [hR.hxMul]; ring` → motive error → `⟨q, hR.hxMul.trans (mul_comm q hR.x')⟩`

6. 次の課題:
   - `PrimeGe5BranchAPrimitiveRestoreRealizationSeedTarget` の証明戦略の検討：
     1. Kummer 理論経由：ℤ[ζ_p] でのイデアル分解
     2. q-adic 持ち上げ：`q^p ∣ GN` の構造を使った z' 構成
     3. Cosmic Formula 独自の降下構造

### 日時: 2026/03/30 18:30:00 JST

1. 目的:
   - `review-010` の方針「q-adic / GN 側から `RealizationSeedTarget` に切り込む」
     の実現可能性を推論・検証する。
   - 実装可能な部分は Lean で書く。

2. 実施:

   **§A. Branch B の z' 構成メカニズムの完全解析**

   - `[CosmicPetalBridgeGNDescentB.lean]` を精読し、
     Branch B の `z'` 構成が **`False.elim`** であることを発見した。
   - Branch B の矛盾メカニズム:
     1. `¬ p ∣ (z-y)` → `gap ⊥ GN`（互いに素）→ 素因数分解の一意性から
        `gap = u^p`, `GN = v^p`（ともに p 乗数）
     2. NoWieferich bridge → GN に平方で割れない素因子が存在
     3. `GN = v^p` と矛盾 → `False`
     4. `False.elim` で任意の型（`z'` を含む）を構成
   - **Branch B は z' を直接構成していない。矛盾からの空虚な存在射。**

   **§B. Branch A での同路線の適用不可性の確認**

   - Branch A の前提: `p ∣ (z-y)` → `gap` と `GN` は `p` で共通因子を持つ
   - したがって `gcd(gap, GN) ≠ 1` → 互いに素分解は不可能
   - NoWieferich bridge は `¬ p ∣ (z-y)` を要求 → Branch A には直接使えない
   - Branch A では `gap = p^{p-1} * t^p`, `GN = p * s^p` で、
     `v_p(gap) = p-1`, `v_p(GN) = 1` と p 以外の因子は p 乗構造を持つが、
     `p` 自体が clean な p 乗にならず、Branch B の矛盾が再現しない

   **§C. 数学的純粋推論の結果**

   - `(x/q)^p + y^p = z'^p` が ℕ 上で p 乗数であることは、
     **FLT の新しい（より小さい）反例の存在** と同値。
   - FLT が真であれば、`a^p + b^p` は `p ≥ 3` で p 乗数にならない。
   - したがって **直接的な z' 構成は不可能**。
   - 正しい攻略路線は Branch B と同じく **前提矛盾（`False.elim`）** である。
   - つまり `RealizationSeedTarget` は「存在を構成する」のではなく
     「前提が矛盾することを示す」ことで vacuously satisfiable にする。
   - 矛盾源の候補:
     - Branch A 固有の Wieferich 条件 `y^{p-1} ≡ 1 [MOD p^2]`
     - `q ≡ 1 [MOD p]` + `q^p ∣ GN` + `gap = p^{p-1} * t^p` の組み合わせ
     - Kummer 理論（円分体のクラス群の構造）

   **§D. 実装した補題群（no-sorry, §Q セクション）**

   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean]` に
     以下の構造体 + 定理を追加した:
     1. `BranchAQFreeQuotient s q` : `s = q * s'` の明示分解
     2. `branchAQFreeQuotient_of_dvd` : `q ∣ s` → 分解の構成
     3. `BranchAQAdicDescentData p x y z t s q` : q-adic 降下データ bundle
     4. `branchA_qadic_descent_data` : 正規形 + `RestoreWitnessProperties` から構成
     5. `branchA_xdiv_eq_p_mul_t_mul_s'` : `x' = p * (t * (s/q))`
     6. `branchA_xdiv_pow_expansion` : `x'^p = p^p * (t*s')^p`
     7. `branchA_realization_reduced_form` :
        `hzEq → p^p * (t*s')^p + y^p = z'^p`（最終還元式）

3. 結論:

   **§1. `RealizationSeedTarget` は q-adic 構造から直接 z' を構成する路線では閉じない。**

   理由: `(x/q)^p + y^p` が ℕ 上で p 乗数になることは FLT の反例存在と同値であり、
   FLT 証明中の文脈では構成不能。

   **§2. 正しい路線は矛盾（`False.elim`）であり、Branch B と同じ精神。**

   Branch B は NoWieferich bridge で`gap` と `GN` の同時 p 乗化から矛盾を導く。
   Branch A では同じ tool は使えないが、別の矛盾源が存在するはず。

   **§3. 実装した足場補題により、`RealizationSeedTarget` は以下に還元された:**

   $$\exists z',\; p^p \cdot (t \cdot s')^p + y^p = z'^p$$

   ここで `s = q * s'`, `x/q = p * t * s'`。
   この式の impossibility を示せば `False` が得られ、
   `RealizationSeedTarget` は vacuously satisfied。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore` 成功
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant` 成功
   - sorry 数: BranchARestore.lean = 0（コード内）
   - BranchARestore.lean: 862 行 → 991 行（+129 行）

5. 失敗事例:
   - `rw [hs']` で `s = q*(s/q)` を代入 → `s/q` 内の `s` も再帰的に書き換わり diverge
     → `set s' := s / q` で名前束縛して回避
   - `pow_succ` の引数パターンが `a^n * a` で `a * a^n` ではない
     → `ring` + `pow_succ` + `congr 1; omega` の組み合わせで解決
   - `Nat.dvd_of_dvd_of_eq` が存在しない → `Nat.mul_div_cancel'` 直接使用
   - `BranchAQAdicDescentData` を `theorem` にしたら Prop elimination error
     → `def` に変更

6. 次の課題:
   - **矛盾路線の設計探索**:
     Branch A の前提から `False` を導く矛盾源を特定する。
     候補:
     1. `y^{p-1} ≡ 1 [MOD p^2]` （Wieferich on y）+ `q ≡ 1 [MOD p]` の組み合わせ
     2. Kummer 理論: ℤ[ζ_p] における `x^p + y^p` のイデアル分解
     3. `RealizationSeedTarget` を bypass して直接 `False` を target にする
        アーキテクチャ変更
   - **Branch A 全体の矛盾チェーン再設計**:
     現在の descent 設計は「smaller packet を構成する」だが、
     真の攻略は「前提矛盾を示す」こと。
     これは Branch A のアーキテクチャそのものの設計転換を示唆する。

### 日時: 2026/03/30 19:20:00 JST

1. 目的:
   - 前回の分析結果「正しい路線は矛盾（`False.elim`）」を受けて、
     矛盾路線のアーキテクチャを設計・実装する。
   - `RealizationSeedTarget`（z' 存在構成）を bypass し、
     `ContradictionTarget`（前提矛盾）に open kernel を移行する。
   - 既存の 6 段チェーンを壊さず、代替路線として接続する。

2. 実施:
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean]`
     §F セクション「矛盾路線（Contradiction Route）」を追加した。
     1. `PrimeGe5BranchAPrimitiveRestoreContradictionTarget` — 新設 target
        - Branch A 全前提 + `RestoreWitnessProperties` → `False`
     2. `primeGe5BranchAPrimitiveRestoreRealizationSeed_of_contradiction`
        - `ContradictionTarget → RealizationSeedTarget`（`False.elim`）
     3. `primeGe5BranchAPrimitiveSmallerCounterexampleFromArithmetic_of_contradiction`
        - `ContradictionTarget → SmallerCounterexampleFromArithmeticTarget`
        - 6 段チェーン全体を bypass する直截な bridge
     4. `primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_contradiction`
        - `ContradictionTarget → RestoreFromArithmeticTarget`
        - packet 包装含めて最上位まで bypass する bridge
   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     provider 側 adapter を追加した。
     1. `BranchAPrimitiveRestoreContradictionAdapterTarget` — alias
     2. `branchAPrimitiveRestoreFromArithmeticAdapter_of_contradiction`
        - `ContradictionTarget → RestoreFromArithmeticTarget` adapter

3. 結論:
   - open kernel が以下のように移行した：
     - 旧: `RealizationSeedTarget`
           = `∃ z', (x/q)^p + y^p = z'^p`（z' の存在構成）
     - 新: `ContradictionTarget`
           = `[Branch A 全前提 + RestoreWitnessProperties] → False`（前提矛盾）
   - `ContradictionTarget` が証明されれば：
     - `RealizationSeedTarget` は `False.elim` で satisfied
     - 6 段チェーン（residue/root → q-adic → datum → seed → realization → verification）
       全体が bypass される
     - `RestoreFromArithmeticTarget` → `SmallerPacket` → Branch A refuter が完成する
   - sorry 増加なし。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore` 成功
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant` 成功
   - sorry 数：BranchA.lean L3981 の 1 箇所のみ（変更なし）
   - BranchARestore.lean: 991 行 → 1114 行（+123 行）

5. アーキテクチャ図:

   ```
   ContradictionTarget (NEW, open)
     │
     ├─→ RealizationSeedTarget        (bypass via False.elim)
     ├─→ SmallerCounterexampleTarget   (bypass via False.elim)
     └─→ RestoreFromArithmeticTarget   (bypass via False.elim)
           │
           └─→ SmallerPacket → descent → minimal 矛盾 → False
   ```

   既存の 6 段分割チェーンは保持されるが、
   `ContradictionTarget` 1 本で全体が short-circuit される。

6. 次の課題:
   - `ContradictionTarget` の証明（= Branch A の数学的矛盾源の特定と形式化）
   - 候補:
     1. Wieferich 条件 `y^{p-1} ≡ 1 [MOD p^2]` からの構造的矛盾
     2. GN の p^2 可除性と gap 構造の不整合
     3. Cosmic Formula のさらに深い構造（GN の mod p^p 展開）
     4. `q^p ∣ GN` + `gcd(q, gap) = 1` + `gap = p^{p-1} * t^p`
        の p-adic valuation 不整合

### 日時: 2026/03/30 20:30:00 JST

1. 目的:
   - `ContradictionTarget` の数学的矛盾源を体系的に探索する。
   - 可能ならば Lean 実装に到達する。少なくとも利用可能な全角度を網羅的に分析する。
   - 全体アーキテクチャとの接続を clean 化する。

2. 数学的分析（試行と結果）:

   以下の 5 つの角度から矛盾源を探索した:

   **角度 1: p-adic / q-adic valuation argument**
   - `v_q(z^p - y^p) = p * v_q(s)` — 全て consistent
   - 結論: **矛盾なし**

   **角度 2: s^p mod p² + Wieferich 条件**
   - `s^p ≡ y^{p-1} ≡ 1 [MOD p²]`（既存補題の組合せ）
   - → `s ≡ 1 [MOD p]`（Fermat 小定理経由）
   - `s = 1 + pa` → `s^p ≡ 1 + p²a [MOD p³]`
   - 結論: **矛盾なし** — 全条件は consistent

   **角度 3: cyclotomicPrimeCore の mod q 展開**
   - `ω = z/y mod q`, `ω^p ≡ 1 mod q`, `ω ≢ 1 mod q` （`q ∤ (z-y)` より）
   - → `Σ ω^k ≡ (ω^p - 1)/(ω - 1) ≡ 0 [MOD q]`
   - → `q ∣ core` — これは `q^p ∣ GN` と consistent
   - mod q² へ進めても q-adic valuation が consistent
   - 結論: **矛盾なし**

   **角度 4: dev-report §9 の `gcd(core/d, x) = 1` を Branch A に適用**
   - 全仮定（`Coprime(gap, y)`, `p ∣ gap`, Wieferich）が Branch A で成立
   - しかし結論 `gcd(s^p, gap) = 1` は `gcd(t,s)=1, ¬p∣s` から自明
   - 結論: **矛盾なし** — 既知事実の再確認にすぎない

   **角度 5: s = 1 の場合の ExistenceMainline 矛盾**
   - `s = 1` → `GN = p` → ExistenceMainline が要求する `q ∤ gap` は `p ∤ gap` を意味 → 矛盾
   - しかし `s = 1` は `ContradictionTarget` の前提 `q ∣ s`（prime q）で既に排除済み
   - 結論: **使えない**

   **総合結論:**
   純粋な初等的 arithmetic（valuation, congruence, coprimality）では
   Branch A の全前提が consistent であり、矛盾は導出できない。
   FLT が真であるため前提は意味論的に矛盾しているが、
   利用可能な初等的道具からの finite-step proof は見つからなかった。
   矛盾を導くには円分体理論や Kummer 理論レベルの深い数論が必要。

3. アーキテクチャ clean 化の実施:

   - `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`
     `branchAPrimitivePacketDescentAdapter_of_contradiction` を追加した。
     - `ContradictionTarget` 1 本で `ExistenceMainline`（no-sorry）と合成し
       `PacketDescentTarget` を直接閉じる parameter-free bridge。
     - 内部実装:
       1. `branchAPrimitiveRestoreFromArithmeticAdapter_of_contradiction` で
          `RestoreFromArithmeticTarget` を bypass
       2. `boundaryCoreWitnessConcreteDefault_and_restore` で
          `ExistenceMainline` の default concrete と合成
     - ビルド成功。sorry 増加なし。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant` 成功
   - sorry: GapInvariant 0（コメント内 3 箇所のみ）
   - 行数: GapInvariant 3081 → 3264 (+183)

5. 到達した clean route 全体図:

   ```
   ExistenceMainline (no-sorry, boundary-core route)
     +
   ContradictionTarget (OPEN KERNEL)
     │
     ├─→ RestoreFromArithmeticTarget (bypass via False.elim)
     │
     └─→ PacketDescentTarget (直接合成)
           │
           └─→ (+ ValuationPeel) → SmallerPacket
                 → SmallerCounterexample
                 → DistinguishedPrimeDescent
                 → (minimality) → BranchARefuterTarget
                 → (+ BranchB) → FLTPrimeGe5Target
   ```

   **FLT for p ≥ 5 の clean 証明に必要な missing pieces:**
   1. `ContradictionTarget` — Branch A 前提矛盾（数学的核心）
   2. `ValuationPeelPacketTarget` — p ∣ t の場合の peel 側
   3. `ExistingDescentRefuterTarget` — 現在 via_FLT（循環的暫定）
      ただし PacketDescent route が完成すれば、via_FLT を bypass して clean 化可能

6. 次の課題:
   - **ContradictionTarget の証明**: 深い数論（Kummer, 正則素数, 円分体）が必要
     - 初等的道具では不足していることが本セッションで確認された
     - GTail の higher-order analysis（mod p^p 展開）の可能性は残る
   - **ValuationPeelPacketTarget**: p ∣ t の場合の descent
     - これは ContradictionTarget とは独立した open kernel
   - **ExistingDescentRefuterTarget の clean 化**:
     PacketDescent chain が完成すれば自動的に clean 化される

### 日時: 2026/03/31 00:09:57 JST

1. 目的:
   - `GTail-impl-plan.md` の Phase C（GTail / GN 高次解析）を実装する。
   - `GTail.lean` に合同性補題と mod p^2 / mod p^3 展開補題を追加し、  
     Branch A の Wieferich 解析や円分核橋への接続基盤を整える。

2. 実施:

   **Phase C1: 合同性基礎補題の整備**

   `[DkMath/CosmicFormula/GTail.lean]` に以下を追加した:

   - `sum_range_modEq` (private helper):
     `Finset.range m` の和の合同性を帰納法で確立する補助補題。
     Mathlib に直接使える `Finset.sum + Nat.ModEq` 組合せ補題が
     なかったため、局所で定義した。

   - `GTail_congr_of_modEq`:
     `x ≡ x' [MOD n]`, `u ≡ u' [MOD n]` → `GTail d r x u ≡ GTail d r x' u' [MOD n]`。
     GTail が x, u の多項式であることから導く congruence 伝播補題。

   - `GTail_modEq_eval_zero_of_dvd_x`:
     `n ∣ x` → `GTail d r x u ≡ GTail d r 0 u [MOD n]`。
     `GTail_congr_of_modEq` の x ≡ 0 特殊化。

   **Phase C2: GN mod n 基本定理**

   - `GN_modEq_choose_mul_pow_of_dvd_x`:
     `n ∣ x` → `GTail d 1 x u ≡ C(d,1) * u^{d-1} [MOD n]`。
     `GTail_modEq_eval_zero_of_dvd_x` + `GTail_eval_zero` の合成。
     任意の n 倍数 x に対して成立する、宇宙式の "mod n 崩壊" 定理。

   - `GN_modEq_head_of_dvd_x`:
     同上の alias（引数名を整理した版）。

   - `GN_modEq_mul_pow_self_of_dvd_x`:
     `d ∣ x` → `GTail d 1 x u ≡ d * u^{d-1} [MOD d]`。
     `C(d,1) = d` を使った自己 modulus 版。

   **Phase C3: mod p^2 精密展開**

   - `GN_modEq_head_mod_sq_of_prime_dvd_x` (別名 `GN_mod_p2_head`):
     `p ∣ x`, prime p ≥ 5 → `GTail p 1 x u ≡ p * u^{p-1} [MOD p^2]`。
     証明: `GN_tail_rec` で展開 → `p^2 ∣ x * GTail p 2`。
     `x * C(p,2) * ...` 部は `p ∣ x` かつ `p ∣ C(p,2) = p(p-1)/2` より `p^2` 整除、
     `x^2 * ...` 部も `p ∣ x` 2 重で `p^2` 整除。

   - `GN_eq_head_add_p_sq_mul_of_prime_dvd_x`:
     `∃ M, GTail p 1 x u = p * u^{p-1} + p^2 * M`。
     mod p^2 合同式を explicit な等式へ持ち上げた版。

   **Phase C4: mod p^3 条件付き展開**

   - `GN_mod_p3_head`:
     `p^3 ∣ x * GTail p 2 x u` → `GTail p 1 x u ≡ p * u^{p-1} [MOD p^3]`。
     三次精度の mod 展開（三次尾項の整除性を仮定として受け取る形）。

   - `GN_eq_head_add_p_cube_mul_of_dvd_tail`:
     同上の explicit 等式版 `∃ M, GTail p 1 x u = p * u^{p-1} + p^3 * M`。

3. 結論:
   - `GTail.lean` に合同性 4 系 + mod p^2/p^3 展開 5 系、計 **9 + 1 (private) 補題**を sorry なしで実装した。
   - `lake build DkMath.CosmicFormula.GTail` 成功、error 0。
   - `lake build`（全体）も成功。
   - 実装計画書 `GTail-impl-plan.md` Phase C1〜C4 を完了。

4. 検証:
   - `lake build DkMath.CosmicFormula.GTail`: exit 0
   - `lake build`（全体）: exit 0
   - GTail.lean: 416 行 → 650 行（+234 行）

5. 失敗事例 (Copilot 試行過程で判明した障壁):
   - `Finset.sum_nat_modEq_sum_nat`, `Finset.sum_modEq_nonneg_congr`:
     そのような補題は Mathlib に存在しなかった。
   - `Finset.sum_nat_mod` は `@[simp]` ループを引き起こすため `simp only` 禁止。
   - `Nat.cast_id`, `Int.natCast_modEq`, `Nat.modEq_comm` も存在しない API 名だった。
   - 最終的に `sum_range_modEq` を private helper として手実装し、
     `GTail_congr_of_modEq` を帰納法ベースで確立した。

6. 次の課題:
   - Phase A: 円分核 ↔ GN ↔ 差分商の橋を theorem 化する
     - `cyclotomicPrimeCore_eq_GN_of_gap`
     - `GN_eq_diffQuot_of_pow` 等
   - Phase B: witness route / contradiction route bundle 分離
   - Phase C の延長: Wieferich 条件 `u^{p-1} ≡ 1 [MOD p^2]` と `GN_mod_p2_head` の結合
     - `branchA_spow_congr_head_mod_p2` 等
   - `ContradictionTarget` に向けた具体的な mod p^2 矛盾探索
