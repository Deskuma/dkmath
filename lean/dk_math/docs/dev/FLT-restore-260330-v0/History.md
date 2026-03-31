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

### 日時: 2026/03/31 01:12:56 JST

1. 目的:
   - 直前の「次の課題」(Phase A/B/C 延長) を実装側で前進させる。
   - 既存 API を壊さず、計画名で呼べる橋定理・接続補題を補強する。
   - `ContradictionTarget` 本丸の前段として、mod p^2 衝突を `False` に落とす局所補題を追加する。

2. 実施:

   **Phase A: 円分核 ↔ GN ↔ 差分商**

   `[DkMath/CFBRC/Basic.lean]` に以下を追加:

   - `cyclotomicPrimeCore_eq_GN_of_gap`  
     `y < z`（すなわち gap 正）を仮定した
     `cyclotomicPrimeCore p (z-y) y = GN p (z-y) y` の specialization。

   - `GN_eq_diffQuot_of_pow`  
     `x > 0` の下で
     `GN p x u = ((x+u)^p - u^p) / x` を与える差分商 bridge。
     （`sub_eq_mul_cyclotomicPrimeCore_nat` + `cyclotomicPrimeCore_eq_GN_nat` を合成）

   - `cyclotomicPrimeCore_eq_diffPowQuot`  
     同条件で core 側も同じ差分商に一致。

   - `GN_eq_dividedDifference_pow`  
     計画書名との互換 alias。

   **Phase B: witness route / contradiction route bundle 名寄せ**

   `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]` に以下を追加:

   - `BranchAWitnessRouteBundleTarget := PrimeGe5BranchAWieferichOnYTarget`
   - `BranchAContradictionRouteBundleTarget := PrimeGe5BranchAWieferichRefuterTarget`

   既存 target を維持したまま、route 分離を API 名で明示。

   **Phase C 延長: Wieferich 条件と GN_mod_p2_head 接続**

   同ファイルに以下を追加:

   - `branchA_spow_congr_head_mod_p2`  
     既存 `primeGe5BranchA_spow_congr_head_mod_p_sq` の計画名 alias。

   - `branchA_contradiction_of_mod_p2_conflict`  
     `¬ (s^p ≡ y^(p-1) [MOD p^2])` を仮定すれば `False` を返す局所衝突補題。

   - `branchA_Wieferich_head_conflict_mod_p2`  
     `¬ (y^(p-1) ≡ 1 [MOD p^2])` と normal form から `False` を返す concrete 版。

3. 結論:
   - 直前ログの「次の課題」4 項目のうち、Phase A と Phase C 延長は実装完了。
   - Phase B はまず bundle 名寄せを導入し、route 分離を statement レベルで固定。
   - `ContradictionTarget` 本体は未解決だが、mod p^2 矛盾探索の入口補題
     (`branchA_contradiction_of_mod_p2_conflict`, `branchA_Wieferich_head_conflict_mod_p2`)
     を追加し、次段で仮定衝突を直接差し込める形になった。

4. 検証:
   - `lake build DkMath.CFBRC.Basic` 成功 (exit 0)
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA` 成功 (exit 0)
   - 既存 warning:
     - `TriominoCosmicBranchA.lean:4008` の `sorry` warning は継続（今回差分起因ではない）

5. 失敗事例 / 修正:
   - `GN_eq_diffQuot_of_pow` で `Nat.div_eq_of_eq_mul_left` の向きが合わず、
     `... = x * GN` ではなく `... = GN * x` が要求された。
   - `Nat.mul_comm` で式向きを整えた `hmul'` を導入して解消。

6. 次の課題:
   - Phase B の実体化:
     - `BranchAWitnessRouteBundleTarget` / `BranchAContradictionRouteBundleTarget`
       を受け取る adapter 群を追加し、既存 refuter 合成点へ接続する。
   - Phase C 深化:
     - `branchA_spow_congr_head_mod_p3` 相当の API 化と、`mod p^3` 衝突補題の concrete 化。
   - `ContradictionTarget` 直接攻略に向けた入口:
     - `branchA_contradiction_of_mod_p2_conflict` へ実際に入る
       「矛盾側前提」をどの下流 statement で要求するかを設計する。

### 日時: 2026/03/31 01:46:50 JST

1. 目的:
   - Phase B の「名寄せだけ」状態を進め、
     bundle target を既存 refuter 合成点に実際に接続する。
   - witness route / contradiction route の API 分離を
     theorem レベルで運用可能にする。

2. 実施:
   `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]` に以下を追加:

   - `primeGe5BranchARefuter_of_routeBundles`
     - `BranchAWitnessRouteBundleTarget` と
       `BranchAContradictionRouteBundleTarget` を直接受ける refuter adapter。
   - `branchAContradictionRouteBundle_of_localKernel`
     - `PrimeGe5BranchAWieferichLocalKernelTarget` から contradiction bundle へ。
   - `branchAContradictionRouteBundle_of_arithmeticKernel`
     - `PrimeGe5BranchANormalFormArithmeticKernelTarget` から contradiction bundle へ。
   - `branchAWitnessRouteBundle_default`
     - witness bundle の default 入口 (`primeGe5BranchAWieferichOnY_default`)。
   - `branchAContradictionRouteBundle_default`
     - arithmetic kernel default を経由した contradiction bundle の default。
   - `primeGe5BranchARefuter_of_routeBundles_default`
     - 上記 2 つの default bundle から直接読む refuter default（bundle 経路版）。

3. 結論:
   - review-012 で指摘されていた
     「Phase B は名寄せのみで adapter 群が未整備」
     の点を解消した。
   - witness / contradiction の bundle API から
     既存 `primeGe5BranchARefuter_of_wieferich` への接続が固定された。
   - 既存の `primeGe5BranchARefuter_default`（shape pipeline 経路）は保持し、
     bundle 経路を並行で導入した。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA` 成功 (exit 0)
   - 既存 warning:
     - `TriominoCosmicBranchA.lean:4008` の `sorry` warning は継続（今回差分起因ではない）

5. 失敗事例:
   - なし（今回追加分で新規エラーは発生せず）。

6. 次の課題:
   - bundle 経路版をどこまで公開 default として昇格するかを決める
     （`primeGe5BranchARefuter_default` の経路統一方針）。
   - `branchA_spow_congr_head_mod_p3` 相当 API と
     mod `p^3` concrete conflict の追加。
   - `ContradictionTarget` に入る「矛盾側前提」の供給元 statement 設計。

### 日時: 2026/03/31 01:54:09 JST

1. 目的:
   - `primeGe5BranchARefuter_default` の経路統一方針を確定する。

2. 実施:
   - 方針決定:
     - **並行維持**を採用。
     - 既存 default (`shape pipeline` 経路) は現状維持。
     - 新規 `route bundles` 経路 (`primeGe5BranchARefuter_of_routeBundles_default`) は並行で維持。

3. 結論:
   - `TriominoCosmicBranchA` の refuter 入口は当面 2 経路併存とする。
   - 将来、`ContradictionTarget` 側の concrete kernel が固まった段階で統一可否を再判定する。

4. 検証:
   - 方針決定のみ（コード変更なし）。

5. 失敗事例:
   - なし。

6. 次の課題:
   - `branchA_spow_congr_head_mod_p3` 相当 API と mod `p^3` concrete conflict の追加。
   - `ContradictionTarget` に入る「矛盾側前提」の供給元 statement 設計。

### 日時: 2026/03/31 02:00:28 JST

1. 目的:
   - 直前ログの次課題 2 点を実装する:
     1) `branchA_spow_congr_head_mod_p3` 相当 API と mod `p^3` concrete conflict
     2) `ContradictionTarget` に入る「矛盾側前提」の供給元 statement 設計

2. 実施:
   `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]` に以下を追加:

   - 新 target（供給元 statement）:
     - `BranchAContradictionModP3SourceTarget`
       - Branch A normal form 入力から
         `¬ (s^p ≡ y^(p-1) [MOD p^3])`
         を供給する契約を定義。

   - mod `p^3` head API:
     - `primeGe5BranchA_spow_eq_head_add_p_cube_mul`
       - `∃ M, s^p = y^(p-1) + p^3 * M`
     - `primeGe5BranchA_spow_congr_head_mod_p_cube`
       - `s^p ≡ y^(p-1) [MOD p^3]`
     - `branchA_spow_congr_head_mod_p3`
       - 計画名互換 alias

   - mod `p^3` concrete conflict:
     - `branchA_contradiction_of_mod_p3_conflict`
       - `¬ (s^p ≡ y^(p-1) [MOD p^3])` を仮定すれば `False`

   - 供給元 statement から refuter への接続:
     - `primeGe5BranchARefuter_of_modP3Source`
       - `BranchAContradictionModP3SourceTarget` を受け取り、
         normal form 抽出 + `branchA_contradiction_of_mod_p3_conflict`
         で Branch A refuter を閉じる adapter。

3. 結論:
   - review-014 で指摘された「次段の焦点」を、そのまま API と target に落とし込んだ。
   - `mod p^3` 側は、単なる命名追加ではなく
     `eq` 版 (`...add_p_cube_mul`) → `ModEq` 版 (`...mod_p_cube`) → conflict 版
     の 3 層で運用可能になった。
   - `ContradictionTarget` の入口設計として、
     「何を外部から供給すれば refuter が閉じるか」を
     `BranchAContradictionModP3SourceTarget` で明示できた。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA` 成功 (exit 0)
   - 既存 warning:
     - `TriominoCosmicBranchA.lean:4092` の `sorry` warning は継続（今回差分起因ではない）

5. 失敗事例:
   - なし（追加分で新規ビルドエラーは発生せず）。

6. 次の課題:
   - `BranchAContradictionModP3SourceTarget` を満たす concrete 数学（negation 供給）をどの層で構成するか決める。
   - `mod p^3` conflict を `PrimeGe5BranchAPrimitiveRestoreContradictionTarget` 系へどう注入するか（restore/gap-invariant 側 adapter 設計）。

### 日時: 2026/03/31 08:30:00 JST

1. 目的:
   - 前回の「次の課題」2 項を解決する:
     - `BranchAContradictionModP3SourceTarget` の実現可能性を判定する。
     - `mod p^3` conflict の `RestoreContradictionTarget` への注入設計。
   - adapter 設計を確定し、3 ファイルに実装する。

2. 実施:

   **§A. `BranchAContradictionModP3SourceTarget` の偽命題判定**

   数学的分析により、`BranchAContradictionModP3SourceTarget` は **偽命題** であることが確定した。

   - `branchA_spow_congr_head_mod_p3` により
     `s^p ≡ y^{p-1} [MOD p^3]` が Branch A normal form から
     **自動で従う** ことが前回コミットで証明済み。
   - したがって `¬ (s^p ≡ y^{p-1} [MOD p^3])` を供給することは不可能。
   - さらに一般に、mod p^k (k ≤ p-1) の head congruence も
     gap shape `z - y = p^{p-1} * t^p` から自動で従う。
   - Wieferich 条件 `y^{p-1} ≡ 1 [MOD p^2]` と合わせると
     `s^p ≡ 1 [MOD p^2]` が得られるが、`s ≡ 1 [MOD p]` と
     `¬ p ∣ s` は両立するため矛盾しない。
   - **結論**: mod p^k 合同式のみからの矛盾導出は不可能。
     矛盾には witness q の情報が必須。

   **§B. `ModP3SourceTarget` の docstring に DEPRECATED/FALSE 注釈を追加**

   `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`:
   - `BranchAContradictionModP3SourceTarget` の docstring に
     `**DEPRECATED / FALSE**` 注釈を追加。
   - `primeGe5BranchARefuter_of_modP3Source` の docstring にも
     前提が満たされない旨の NOTE を追加。
   - 歴史的記録として残す（削除はしない）。

   **§C. `BranchAContradictionWithWitnessSourceTarget` の新設**

   `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean]`:
   - `BranchAContradictionWithWitnessSourceTarget` を新設:
     - Branch A normal form + witness `q` の全構造的性質を個別引数で受け取る形
     - `RestoreWitnessProperties` structure への前方参照を避けるため、
       `q ∣ x`, `¬ q ∣ y`, `¬ q ∣ z`, `¬ q ∣ (z-y)`, `p ∣ (q-1)`,
       `q^p ∣ GN` を個別引数として展開する設計にした
   - `PrimeGe5BranchAPrimitiveRestoreContradictionTarget` との関係:
     同一 signature（witness 性質の渡し方が structure vs 個別引数の差のみ）

   **§D. thin adapter の配置**

   `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean]`:
   - `primeGe5BranchAPrimitiveRestoreContradiction_of_witnessSource`:
     `WithWitnessSourceTarget` → `RestoreContradictionTarget` への bridge。
     個別引数を `RestoreWitnessProperties` の field に再包装する。

   `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]`:
   - `BranchAContradictionWithWitnessSourceAdapterTarget`:
     provider 側 alias。
   - `branchAPrimitiveRestoreContradictionAdapter_of_witnessSource`:
     witness source → contradiction adapter bridge。
   - `branchAPrimitiveRestoreFromArithmeticAdapter_of_witnessSource`:
     restore 6 段チェーン全体を bypass する short-circuit adapter。
   - `branchAPrimitivePacketDescentAdapter_of_witnessSource`:
     ExistenceMainline + witness source → PacketDescent の最上位 adapter。

3. 結論:

   **到達した contradiction route の全体図:**

   ```
   BranchAContradictionWithWitnessSourceTarget  [OPEN KERNEL - 新設]
     │
     ├─(BranchARestore)─→ RestoreContradictionTarget
     │                       │
     │                       └──→ RestoreFromArithmeticTarget (bypass)
     │
     ├─(GapInvariant)──→ ContradictionAdapter
     │                       │
     │                       ├──→ RestoreFromArithmeticAdapter (bypass)
     │                       │
     │                       └──→ PacketDescentAdapter (最上位 short-circuit)
     │
     └─ [DEPRECATED] BranchAContradictionModP3SourceTarget (偽命題)
   ```

   **open kernel の現状:**
   - `BranchAContradictionWithWitnessSourceTarget` 1 本
   - これは witness q の全性質（`q ∣ x`, `q ∤ y`, `p ∣ (q-1)`, `q^p ∣ GN` 等）
     を前提として受け取り、`False` を導く命題。
   - mod p^k 路線ではなく、witness q の構造的衝突から矛盾を導く新路線が必要。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA` 成功 (exit 0)
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore` 成功 (exit 0)
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant` 成功 (exit 0)
   - `lake build`（全体）成功 (exit 0)
   - sorry: L4099（comparison route 末端マーカー）の 1 箇所のみ、増加なし
   - BranchA.lean: 5569 → 5620 (+51 行)
   - BranchARestore.lean: 1114 → 1140 (+26 行)
   - GapInvariant.lean: 3264 → 3309 (+45 行)
   - 合計: 9947 → 10069 (+122 行)

5. 失敗事例:
   - `BranchAContradictionWithWitnessSourceTarget` の abbrev を L4334
     （`primeGe5BranchARefuter_of_modP3Source` の直後）に初配置した際、
     `RestoreWitnessProperties` への前方参照エラーが発生。
     → signature を structure 参照ではなく個別引数展開に変更して解決。
   - thin adapter `primeGe5BranchAPrimitiveRestoreContradiction_of_witnessSource` を
     BranchA.lean 内に配置しようとしたが、
     `PrimeGe5BranchAPrimitiveRestoreContradictionTarget` が
     BranchARestore.lean で定義されており逆方向 import エラー。
     → adapter を BranchARestore.lean に配置して解決。
   - GapInvariant 側の witness source adapter が
     `branchAPrimitiveRestoreFromArithmeticAdapter_of_contradiction` /
     `branchAPrimitivePacketDescentAdapter_of_contradiction` を前方参照。
     → adapter 定義を `of_contradiction` の直後に再配置して解決。

6. 次の課題:
   - **`BranchAContradictionWithWitnessSourceTarget` の証明**:
     witness q の構造的性質から `False` を導く具体的数学の発見。
     候補:
     - Wieferich 条件の高次化: `y^{p-1} ≡ 1 + cp^2 [MOD p^3]` の係数 c と witness q の関係
     - GN の q-adic 構造: `q^p ∣ GN` と `q ∤ gap` の組み合わせから GTail 内部の因子関係
     - 円分体理論: `q ≡ 1 [MOD p]` と ℤ[ζ_p] でのイデアル分解
   - mod p^k 路線は行き止まりと確定したため、今後は witness q 側の解析に集中する。

### 日時: 2026/03/31 09:30:00 JST

1. 目的:
   - `design-017.md` / `consider-017.md` の「干渉縞」像に基づき、
     Branch A の二系統の構造的縞を統一的に束ねる
     **干渉縞集合 (Interference Fringe Bundle)** を Lean で形式化する。
   - p-adic head 縞と witness q 縞を個別の structure に分離しつつ、
     両者を合成する bundle structure を定義する。
   - 既存の default 補題と `RestoreWitnessProperties` から
     sorry なしで一括構成できることを検証する。
   - `BranchAContradictionWithWitnessSourceTarget` との双方向変換を実装する。

2. 実施:

   **§A. 干渉縞集合の structure 設計と実装**

   `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean]` に以下を追加:

   - `BranchAPadicFringe (p x y z t s : ℕ) : Prop` — **第一縞**
     - Normal form base: pack, hp_dvd_gap, hgap, hsGN, hsx
     - Coprimality: hcop_ts, hcop_ty, hcop_sy
     - p-divisibility: hp_not_dvd_s, hp_not_dvd_t
     - Wieferich: hWieferich
     - Head congruences: hhead_mod_p2, hhead_mod_p3
     - Derived: hs_cong_one, hspow_cong_one

   - `BranchAWitnessFringe (p x y z t s q : ℕ) : Prop` — **第二縞**
     - Witness basic: hqprime, hqs, hqt, hcop_qy, hq_ne_p
     - Structural: hq_dvd_x, hq_not_dvd_y, hq_not_dvd_z,
       hq_not_dvd_gap, hq_cong, hqp_dvd_GN

   - `BranchAInterferenceFringeBundle (p x y z t s q : ℕ) : Prop`
     — **干渉縞集合**: `padic` + `witness` の合成

   **§B. Constructor theorems**

   - `branchAPadicFringe_default`: 第一縞の一括構成（`¬ p ∣ t` のみ外部引数）
   - `branchAWitnessFringe_of_restoreProperties`: 第二縞の構成
   - `branchAInterferenceFringeBundle_default`: 両縞の一括構成

   **§C. 双方向変換 theorems**

   - `BranchAFringeContradictionTarget`: bundle 版の矛盾 target
   - `branchAContradictionWithWitnessSource_of_fringeContradiction`:
     bundle → 個別引数 (unbundle)
   - `branchAFringeContradiction_of_witnessSource`:
     個別引数 → bundle (bundle)

   **§D. GapInvariant 側 adapter**

   `[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]` に以下を追加:

   - `BranchAFringeContradictionAdapterTarget`: provider 側 alias
   - `branchAContradictionWithWitnessSourceAdapter_of_fringeContradiction`:
     fringe → witness source
   - `branchAPrimitiveRestoreContradictionAdapter_of_fringeContradiction`:
     fringe → restore contradiction (short-circuit)

3. 結論:

   **到達したアーキテクチャ:**

   ```
   BranchAFringeContradictionTarget  [OPEN KERNEL - bundle 版]
     ↕ (双方向変換)
   BranchAContradictionWithWitnessSourceTarget  [OPEN KERNEL - 個別引数版]
     │
     ├─(BranchARestore)─→ RestoreContradictionTarget
     │
     └─(GapInvariant)───→ ContradictionAdapter
                             ├──→ RestoreFromArithmeticAdapter
                             └──→ PacketDescentAdapter
   ```

   - **3 structure** を新設:
     `BranchAPadicFringe`, `BranchAWitnessFringe`,
     `BranchAInterferenceFringeBundle`
   - **7 theorem** を新設（全て sorry なし）:
     default 構成 3 本、双方向変換 2 本、GapInvariant adapter 3 本
   - **1 target** を新設: `BranchAFringeContradictionTarget`
   - bundle 版と個別引数版は **等価** であることが双方向 theorem で保証された。

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore` 成功
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant` 成功
   - `lake build`（全体）成功 (exit 0)
   - sorry 増加なし
   - BranchARestore.lean: 1140 → 1352 (+212 行)
   - GapInvariant.lean: 3309 → 3338 (+29 行)

5. 失敗事例:
   - なし（設計段階で前方参照問題を回避するために
     BranchARestore.lean に配置する判断を済ませていた）。

6. 次の課題:
   - `BranchAFringeContradictionTarget` の証明:
     干渉縞集合の共存不可能性（= `False`）を導く concrete 数学。
   - 干渉縞集合の field を活用した新しい矛盾候補の探索:
     - `hqp_dvd_GN` (`q^p ∣ GN`) と `hhead_mod_p3` (`s^p ≡ y^{p-1} [MOD p^3]`) の結合
     - `hq_cong` (`p ∣ (q-1)`) と Wieferich の相互作用
     - `hq_not_dvd_gap` (`q ∤ (z-y)`) と gap shape の衝突可能性

### 日時: 2026/03/31 10:30:00 JST

1. 目的:
   - 前回の「次の課題」3 ルートを数学的に精査する:
     - ルート 1: `q^p ∣ GN` + `s^p ≡ y^{p-1} [MOD p^3]` の結合
     - ルート 2: `p ∣ (q-1)` + Wieferich の相互作用
     - ルート 3: `q ∤ (z-y)` + gap shape の衝突可能性
   - 各ルートから導出可能な新規補題を実装する。

2. 実施:

   **§A. 3 ルートの数学的分析**

   **ルート 1** (`q^p ∣ GN` + head congruence):
   - `∃ M, s^p = y^{p-1} + p^3*M` と `q ∣ s` を結合。
   - `q ∣ s^p` から `q ∣ (y^{p-1} + p^3*M)`。
   - 仮に `q ∣ M` なら `q ∣ (p^3*M)` → `q ∣ y^{p-1}` → `q ∣ y`。
     しかし `q ∤ y` (witness fringe)。矛盾。
   - **結論**: `q ∤ M` が証明可能。
   - さらに `q^p ∣ s^p` から `q^p ∣ (y^{p-1} + p^3*M)`。
     v_q(y^{p-1}) = 0 かつ v_q(M) = 0 なのに和の v_q ≥ p。
     **massive cancellation** を意味する構造的制約。
   - 直接的矛盾には至らないが、tail 係数 M の q-adic 構造が固定される。

   **ルート 2** (`p ∣ (q-1)` + Wieferich):
   - Wieferich `y^{p-1} ≡ 1 [MOD p^2]` は p-adic 世界。
   - `p ∣ (q-1)` は (Z/qZ)* に p-torsion を保証。
   - CRT: Z/p^2Z と Z/q^jZ の制約は独立。
   - **直接的矛盾なし**。
   - ただし `q ≡ 1 [MOD p]` と `s ≡ 1 [MOD p]` の組み合わせから
     **`s' ≡ 1 [MOD p]`** が導ける（descent 不変量）。

   **ルート 3** (`q ∤ (z-y)` + gap shape):
   - `z-y = p^{p-1}*t^p` で `q ∤ (z-y)` → `q ∤ t^p` → `q ∤ t`。
   - これは coprimality から既知。**新規なし**。

   **§B. 新規補題の実装（7 本, 全て sorry なし）**

   `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean]`:

   - `branchA_fringe_q_congr_one_mod_p`:
     `p ∣ (q-1)` → `q ≡ 1 [MOD p]` (ModEq 形式変換)

   - `branchA_fringe_q_dvd_head_sum`:
     `q ∣ s` → `q ∣ (y^{p-1} + p^3*M)` (基本 cross-modular 制約)

   - `branchA_fringe_qpow_dvd_head_sum`:
     `q ∣ s` → `q^p ∣ (y^{p-1} + p^3*M)` (深層 cross-modular 制約)
     massive cancellation の形式的表現。

   - **`branchA_fringe_q_not_dvd_tail_coeff`**:
     `q ∣ s` ∧ `q ∤ y` → **`q ∤ M`** (核心的 cross-modular 制約)
     p-adic head 縞と q-adic witness 縞の干渉の直接的帰結。

   - **`branchA_fringe_sprime_congr_one_mod_p`**:
     `s ≡ 1 [MOD p]` ∧ `q ≡ 1 [MOD p]` ∧ `s = q*s'` → **`s' ≡ 1 [MOD p]`**
     descent 不変量: 降下の各段で mod p 合同が保存される。

   - `branchA_fringe_tail_coeff_coprime_to_witness`:
     fringe bundle → `∃ M, s^p = y^{p-1} + p^3*M ∧ ¬ q ∣ M` (統合版)

   - `branchA_fringe_descent_preserves_mod_p`:
     fringe bundle + `s = q*s'` → `s' ≡ 1 [MOD p]` (統合版)

3. 結論:

   **数学的到達点:**

   ルート 1 から **2 つの新知見** を得た:
   - `q ∤ M` (tail 係数は witness q に coprime)
   - `q^p ∣ (y^{p-1} + p^3*M)` (v_q = 0 + v_q = 0 の和が v_q ≥ p の massive cancellation)

   ルート 2 から **1 つの新知見** を得た:
   - `s' ≡ 1 [MOD p]` (descent 不変量)

   ルート 3 は既知の帰結のみ。

   **未到達の矛盾:**

   3 ルート単独では矛盾に至らない。矛盾には以下のいずれかが必要:
   - GN の q-adic 内部構造のさらなる精密化
     （cyclotomic core としての解析 — Kummer / Mihailescu 型の議論）
   - `q^p ∣ (y^{p-1} + p^3*M)` の cancellation が実は不可能であることの証明
     （これは本質的に cyclotomic valuation の理論）
   - 円分体 Q(ζ_p) での ideal factorization の Lean 形式化

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore` 成功
   - `lake build`（全体）成功 (exit 0)
   - sorry 増加なし
   - BranchARestore.lean: 1352 → 1510 (+158 行)

5. 失敗事例:
   - `branchA_fringe_q_not_dvd_tail_coeff` の証明で `dvd_add_right` を使おうとしたが、
     これは Ring.Divisibility の補題で ℕ には直接適用不可。
     → `Nat.dvd_sub` + `Nat.add_sub_cancel` で解決。
   - `branchA_fringe_q_congr_one_mod_p` で `Nat.modEq_iff_dvd'` の引数順序が
     `Nat.ModEq p 1 q` を返し、期待の `Nat.ModEq p q 1` と逆。
     → `.symm` で対称性を適用して解決。

6. 次の課題:
   - **cyclotomic valuation theory**: `q^p ∣ (y^{p-1} + p^3*M)` の
     massive cancellation が実際に成立しうるかどうかの判定。
     これは円分核 Φ_p(z, y) の q-adic 展開の理論（Kummer 型）に直結する。
   - **Hensel lifting**: ZMod q での primitive p-th root ω の
     ZMod q^p への lift の形式化。
     既存の `PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed` の拡張として。
   - **descent chain 分析**: `s' ≡ 1 [MOD p]` の不変量と、
     各 descent step での `s → s' = s/q` の値の厳密減少から、
     有限ステップでの停止条件（s' = 1 のケース分析）を調べる。

### 日時: 2026/03/31 11:45:00 JST

1. 目的:
   - 前回の「次の課題」3 ルートを全て実装する:
     - cyclotomic valuation theory
     - Hensel lifting（ω の接続定理）
     - descent chain 分析（strict decrease + 停止条件）

2. 実施:

   **§A. Descent chain 分析（降下連鎖の形式化）**

   `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean]` に以下を追加:

   - `branchA_s_pos`: `x = p*(t*s)` ∧ `x ≠ 0` → `0 < s`
   - `branchA_t_pos`: 同上 → `0 < t`
   - `branchA_descent_s_prime_pos`: `0 < s` ∧ `s = q*s'` → `0 < s'`
   - `branchA_descent_s_strict_decrease`: `q` prime ∧ `s = q*s'` → `s' < s`
     （well-founded の基盤。`q ≥ 2` から `s' < 2*s' ≤ q*s' = s`）
   - `branchA_descent_x_strict_decrease`: `s' < s` → `p*(t*s') < x`
   - `BranchADescentStep (p x y z t s q : ℕ) : Prop` — 降下 1 step の全性質
     (`s = q*s'`, `0 < s'`, `s' < s`, `s' ≡ 1 [MOD p]`, `p*(t*s') < x`)
   - `branchA_descent_step_of_fringe`: fringe bundle → `BranchADescentStep` の一括構成

   **§B. Cyclotomic valuation の構造定理**

   - `branchA_lift_seed_z_eq_omega_mul_y`:
     `ω = z * y⁻¹ ∈ ZMod q` として `(z : ZMod q) = ω * (y : ZMod q)`
     — QAdicLiftSeed の `ω` と witness properties の接続。
     `y ≠ 0 [MOD q]` は `hq_not_dvd_y` から直接得られる。
   - `branchA_cyclotomic_q_valuation_ge_p`:
     `q^p ∣ GN p (z-y) y` — v_q(GN) ≥ p の形式的表現。
     fringe bundle の alias。
   - `branchA_descent_spow_factorization`:
     `s = q*s'` → `s^p = q^p * s'^p`
     — 降下 1 step で GN の q-adic 因子が `q^p` ずつ剥がれることの算術的基盤。

   **§C. Docstring 重複修正**

   `BranchADescentStep` の定義直前に重複していた 2 つの docstring を
   1 つに統合（コンテキスト適合側を残した）。

3. 結論:

   **到達した降下構造:**

   ```
   BranchAInterferenceFringeBundle
     │
     ├──→ BranchADescentStep (1 step の全性質)
     │     ├── s' < s        (strict decrease, well-founded)
     │     ├── 0 < s'        (正値保存)
     │     ├── s' ≡ 1 [MOD p] (合同保存)
     │     └── p*(t*s') < x  (x の strict decrease)
     │
     ├──→ ω = z*y⁻¹ [ZMod q]  (Hensel lifting 基盤)
     │     └── (z : ZMod q) = ω * (y : ZMod q)
     │
     └──→ s^p = q^p * s'^p    (q-valuation 因子分解)
           └── q^p ∣ GN       (v_q(GN) ≥ p)
   ```

   - **9 定義/定理** を新設（全て sorry なし）:
     `branchA_s_pos`, `branchA_t_pos`, `branchA_descent_s_prime_pos`,
     `branchA_descent_s_strict_decrease`, `branchA_descent_x_strict_decrease`,
     `BranchADescentStep`, `branchA_descent_step_of_fringe`,
     `branchA_lift_seed_z_eq_omega_mul_y`, `branchA_cyclotomic_q_valuation_ge_p`,
     `branchA_descent_spow_factorization`
   - 降下連鎖の well-foundedness（`s' < s`）と不変量保存（`s' ≡ 1 [MOD p]`）が
     同時に形式化された。
   - ω の ZMod q 上での接続が explicit theorem として固定された。

4. 検証:
   - `lake build`（全体）成功 (exit 0)
   - sorry 増加なし（BranchA.lean L4099 の既存 1 箇所のみ）
   - BranchARestore.lean: 1510 → 1717 (+207 行)

5. 失敗事例:
   - `Nat.mul_lt_mul_left` は Lean 4 / Mathlib v4.26 では `Iff` を返す。
     → `Nat.mul_lt_mul_of_pos_left` に変更して解決。
   - `BranchADescentStep` を最初 `structure : Prop` で定義しようとしたが、
     `s' : ℕ` のデータ field は Prop structure に入れられない。
     → `def ... : Prop := let s' := s / q; ...` の形に変更。
   - docstring の重複（2 つの /-- ... --/ が連続）が発生していた。
     → コンテキスト適合側を残して統合。

6. 次の課題:
   - **descent chain の停止条件分析**:
     well-founded な `s' < s` の降下連鎖は有限ステップで
     `s' = 1` に到達する。このとき `x' = p*t` となり、
     `x'^p + y^p = z'^p` の解は `Coprime x' y'` を保ちながら
     p-free な `x'` を持つ — これは Branch A の前提 `p ∣ x` に矛盾する可能性がある。
   - **ω^p = 1 の明示的証明**:
     `branchA_lift_seed_z_eq_omega_mul_y` を拡張し、
     `ω^p = 1` かつ `ω ≠ 1` を `ZMod q` 上で示す。
     （`restore_witness_cong_one_mod_p` の orderOf 理論を接続）
   - **Hensel lifting の高次化**:
     `ZMod q` → `ZMod (q^p)` への ω の lift。
     既存の `PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed` との接続。

### 日時: 2026/03/31 12:30:00 JST

1. 目的:
   - `review-020.md` の方針に従い、`ω := z * y⁻¹ ∈ ZMod q` の
     位数構造を干渉縞集合 interface で明示的に確定する:
     - `ω^p = 1` (p-th root of unity)
     - `ω ≠ 1` (非自明性)
     - `orderOf ω = p` (primitive)
   - 既存の `PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed` との直接接続。

2. 実施:

   `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean]` に以下を追加:

   **§A. ω の位数構造 (Root of Unity Analysis)**

   - **`branchA_omega_pow_eq_one`**: `ω^p = 1`
     FLT 等式 `x^p + y^p = z^p` と `q ∣ x` から ZMod q 上で
     `z^p = y^p` を導き、`(z*y⁻¹)^p = z^p*(y⁻¹)^p = y^p*(y⁻¹)^p = 1` を構成。

   - **`branchA_omega_ne_one`**: `ω ≠ 1`
     `q ∤ (z-y)` → `z ≢ y [MOD q]` → `z*y⁻¹ ≠ 1`。
     `ω = 1` と仮定すると `z = z*y⁻¹*y = 1*y = y` (in ZMod q) → `q ∣ (z-y)` → 矛盾。

   - **`branchA_omega_order_eq_p`**: `orderOf ω = p`
     `ω^p = 1` かつ `ω ≠ 1` で `p` が素数なので
     `orderOf_eq_prime` により直接得られる。
     これは `ω` が **primitive p-th root of unity** であることの確定。

   **§B. QAdicLiftSeed への直接接続**

   - **`branchA_qadic_lift_seed_of_fringe`**: `def` (データ構成)
     干渉縞集合 → `PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed` の全 field 供給。
     `ω`, `hω_pow`, `hω_ne_one` を fringe bundle の定理から直接構成。

3. 結論:

   **到達した円分構造の全体像:**

   ```
   BranchAInterferenceFringeBundle
     │
     ├──→ branchA_omega_pow_eq_one   : ω^p = 1
     ├──→ branchA_omega_ne_one       : ω ≠ 1
     ├──→ branchA_omega_order_eq_p   : orderOf ω = p
     │
     └──→ branchA_qadic_lift_seed_of_fringe
           └── PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed
                ├── ω : ZMod q
                ├── hω_pow : ω^p = 1
                └── hω_ne_one : ω ≠ 1
   ```

   これにより:
   - `ω` が **primitive p-th root of unity mod q** であることが形式的に確定した。
   - 既存の `QAdicLiftSeed` が fringe bundle から sorry なしで構成可能になった。
   - `p ∣ (q-1)` は `orderOf ω = p` と `orderOf ω ∣ (q-1)` の合成として
     改めて理解される — 同じ計算が `restore_witness_cong_one_mod_p` にあるが、
     ω そのものが fringe interface で公開されたのが今回の進歩。

   **数学的意味:**

   `ω` が primitive ⟹ `q` は $\mathbb{Q}(\zeta_p)$ で完全分解する。
   Hensel lifting の高次化（`ZMod q` → `ZMod (q^p)`）は
   この 3 定理の上に構築される。

   - **4 定理/定義** を新設（全て sorry なし）:
     `branchA_omega_pow_eq_one`, `branchA_omega_ne_one`,
     `branchA_omega_order_eq_p`, `branchA_qadic_lift_seed_of_fringe`

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore` 成功
   - `lake build`（全体）成功 (exit 0)
   - sorry 増加なし（BranchA.lean L4099 の既存 1 箇所のみ）
   - BranchARestore.lean: 1717 → 1839 (+122 行)

5. 失敗事例:
   - `branchA_omega_ne_one` で `field_simp` を使ったところ、
     `z/y = 1` の形に正規化され `z = y` ではなく `↑z / ↑y = 1` が出力された。
     → `mul_assoc + inv_mul_cancel₀ + one_mul` による explicit 計算で解決。
   - `branchA_qadic_lift_seed_of_fringe` を `theorem` で定義したが、
     `QAdicLiftSeed` はデータ structure (non-Prop) なので型エラー。
     → `def` に変更。

6. 次の課題:
   - **Hensel lifting の高次化**:
     `ω^p = 1` ∧ `ω ≠ 1` in `ZMod q` を `ZMod (q^p)` へ lift する。
     Hensel の補題の Lean 形式化が必要。
   - **cyclotomic valuation の精密化**:
     `orderOf ω = p` から `v_q(Φ_p(z,y))` の正確な値を決定する。
     Kummer の定理: `v_q(Φ_p(z,y)) = v_q(z - ωy)` (他の因子は q-coprime)。
   - **descent chain の terminal case**:
     `s' = 1` のとき `x' = p*t` → `ω' = z'*(y')⁻¹` の位数と
     新しい fringe bundle の構造分析。

### 日時: 2026/03/31 13:00:00 JST

1. 目的:
   - `review-021.md` の方針に従い、cyclotomic valuation を精密化する。
   - 具体的には、円分核 Φ_p(z,y) の因子分解において
     **distinguished factor `z - ω*y` だけが q で消え、他は消えない**
     ことを ZMod q 上で形式化する。

2. 実施:

   `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean]` に以下を追加:

   **§A. Cyclotomic Valuation の精密化**

   - **`branchA_omega_i_ne_omega`**: `i ≢ 1 [MOD p]` → `ω^i ≠ ω`
     primitive root の基本性質。
     証明: `ω^i = ω` → (i=0 の場合) `ω = 1` 矛盾、(i>0 の場合)
     `ω^(i-1) = 1` → `orderOf ω ∣ (i-1)` → `p ∣ (i-1)` → `i ≡ 1 [MOD p]` 矛盾。
     `orderOf_dvd_of_pow_eq_one` と `Nat.modEq_iff_dvd'` を使用。

   - **`branchA_distinguished_factor_vanishes`**: `(z : ZMod q) - ω * y = 0`
     ω の定義 `ω = z*y⁻¹` から直接。`z = ω*y` なので `z - ω*y = 0`。
     `inv_mul_cancel₀` で explicit に計算。

   - **`branchA_non_distinguished_factor_nonzero`**: `i ≢ 1 [MOD p]` → `z - ω^i * y ≠ 0`
     `z = ω*y` と `z = ω^i*y` を仮定すると `ω^i = ω` → 上の補題に矛盾。
     `mul_right_cancel₀ hy_ne_zero` で `ω^i*y = ω*y` → `ω^i = ω` を導出。

3. 結論:

   **円分核の因子構造 (ZMod q 上):**

   ```
   Φ_p(z, y) = ∏_{i=1}^{p-1} (z - ω^i * y)

   i = 1:         z - ω * y = 0    [MOD q]  — distinguished
   i ≢ 1 [MOD p]: z - ω^i * y ≠ 0  [MOD q]  — q-coprime
   ```

   これにより:
   - **q は 1 つの因子 `z - ω*y` のみを割る** ことが確定した。
   - Kummer 型の valuation 定理 `v_q(Φ_p(z,y)) = v_q(z - ω*y)` への
     道が開かれた（ZMod q 上では q-coprime 因子は q-adic valuation 0）。
   - massive cancellation の正体が「1 因子集中」として見えた。

   **3 定理** を新設（全て sorry なし）:
   `branchA_omega_i_ne_omega`, `branchA_distinguished_factor_vanishes`,
   `branchA_non_distinguished_factor_nonzero`

4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore` 成功
   - `lake build`（全体）成功 (exit 0)
   - sorry 増加なし（BranchA.lean L4099 の既存 1 箇所のみ）
   - BranchARestore.lean: 1839 → 1951 (+112 行)

5. 失敗事例:
   - `pow_eq_pow_iff_modEq` は `LeftCancelMonoid` を要求するが、
     `ZMod q` は field であっても零元があるため `LeftCancelMonoid` ではない。
     → case split (`i=0` vs `i>0`) + `orderOf_dvd_of_pow_eq_one` で回避。
   - `Nat.modEq_iff_dvd'` は `1 ≡ i [MOD p]` を返す（方向注意）。
     → `.symm` で `i ≡ 1 [MOD p]` に変換。
   - `mul_right_cancel₀` の引数順: `ω^i*y = ω*y` を要求されたが
     `ω*y = ω^i*y` を渡していた。→ `.symm.trans` の順序を修正。
   - `show` tactic は Lean linter で `change` 推奨。→ `change` に修正。

6. 次の課題:
   - **Kummer valuation 定理の形式化**:
     `v_q(Φ_p(z,y)) = v_q(z - ω*y)` を ℕ の `padicValNat` で表現する。
     ZMod q 上の因子分離（今回）から、q-adic valuation の完全集中を導く。
   - **Hensel lifting**:
     `ω^p = 1, ω ≠ 1` in `ZMod q` → `ω' ^p = 1` in `ZMod (q^k)` の lift。
   - **descent terminal case**:
     降下鎖の停止条件 `s' = 1` の構造分析。

### 日時: 2026/03/31 13:45:00 JST

1. 目的:
   - `review-022.md` の方針に従い、Kummer valuation を実装する。
   - ZMod q 上の因子分離結果を ℕ の `padicValNat` に翻訳し、
     massive cancellation の定量的表現を得る。

2. 実施:

   `[DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean]` に以下を追加:

   **§A. Kummer Valuation — padicValNat への翻訳**

   3 段の橋を組み立てた:

   - **`branchA_padicValNat_sub_pow_eq_GN`** [第 1 段]:
     `v_q(z^p - y^p) = v_q(GN p (z-y) y)`
     既存の `padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap` を
     fringe bundle interface で wrap。`q ∤ (z-y)` は bundle の witness 側に含まれる。

   - **`branchA_padicValNat_GN_decomp`** [第 2 段]:
     `v_q(GN) = v_q(p) + p * v_q(s)`
     `GN = p * s^p` (正規形) + `padicValNat.mul` + `padicValNat.pow` で分解。

   - **`branchA_padicValNat_p_eq_zero`** [第 2.5 段]:
     `v_q(p) = 0`
     `q ≠ p` (異なる素数) → `q ∤ p` → `padicValNat.eq_zero_of_not_dvd`。

   - **`branchA_kummer_valuation`** [統合]:
     `v_q(z^p - y^p) = p * v_q(s)`
     3 段の橋の合成。Central statement。

   - **`branchA_padicValNat_s_ge_one`**:
     `v_q(s) ≥ 1`
     `q ∣ s` → `one_le_padicValNat_of_dvd`。

   - **`branchA_kummer_valuation_ge_p`** [下界]:
     `p ≤ v_q(z^p - y^p)`
     `v_q(z^p - y^p) = p * v_q(s) ≥ p * 1 = p`。

   **§B. 降下と Kummer valuation の接続**

   - **`branchA_descent_padicValNat_s`**:
     `v_q(s) = 1 + v_q(s/q)`
     `s = q * s'` → `padicValNat.mul` + `padicValNat_self`。
     各降下 step で `v_q(s)` が 1 ずつ、`v_q(z^p - y^p)` が p ずつ減る。

3. 結論:

   **Kummer valuation の全体像:**

   ```
   v_q(z^p - y^p)
     = v_q(GN p (z-y) y)           [第 1 段: q ∤ gap]
     = v_q(p) + p * v_q(s)         [第 2 段: GN = p * s^p]
     = 0 + p * v_q(s)              [第 2.5 段: q ≠ p]
     = p * v_q(s)                  [統合]
     ≥ p                           [下界: q ∣ s → v_q(s) ≥ 1]
   ```

   **降下との接続:**

   ```
   s = q * s'  →  v_q(s) = 1 + v_q(s')
                →  v_q(z^p - y^p) が p ずつ減少
   ```

   - **7 定理** を新設（全て sorry なし）
   - massive cancellation の定量的表現が `padicValNat` で確定した。
   - 降下 1 step ごとの valuation 変化が定理化された。

4. 検証:
   - `lake build`（全体）成功 (exit 0)
   - sorry 増加なし（BranchA.lean L4099 の既存 1 箇所のみ）
   - BranchARestore.lean: 1951 → 2077 (+126 行)

5. 失敗事例:
   - `DkMath.NumberTheory.GcdNext.padicValNat_sub_pow_...` — namespace が
     `GcdNext` ではなく `Gcd` だった。→ 修正。
   - `hBundle.padic.pack.hyz` は `y ≤ z` だが、外部定理は `y < z` を要求。
     `hyz_lt` field を使うよう修正。`.hy0` は `y ≠ 0` で `.hy0.bot_lt` で `0 < y` が取れた。
   - `padicValNat.mul` / `.pow` は `Fact (Nat.Prime q)` instance を要求するが、
     haveI で bundle から供給が必要だった。
   - `prime_pow_self` は存在しない。`padicValNat_self` が正しい名前。

6. 次の課題:
   - **Hensel lifting**:
     `ω^p = 1, ω ≠ 1` in `ZMod q` を `ZMod (q^k)` へ lift する。
     これにより `v_q(z - ω*y)` の正確な値が決定できる。
   - **descent terminal case**:
     `v_q(s) = 0` (= `s' = 1` に対応) のとき、
     `v_q(z^p - y^p) = 0` → `q ∤ (z^p - y^p)` → 矛盾の可能性。
   - **Kummer valuation と distinguished factor の接続**:
     今回の `v_q(z^p - y^p) = p * v_q(s)` と
     前回の `z - ω*y ≡ 0 [MOD q]` を結合し、
     `v_q(z - ω*y) = p * v_q(s)` を得る（他の因子は v_q = 0 なので）。
