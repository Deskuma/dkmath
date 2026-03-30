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
