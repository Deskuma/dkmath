# History

prev cid: 69ca1b34-0bcc-83a2-bcfd-529624b85356
cid: 69d13ce6-7814-83a8-8075-aa4b1b4b48af

- 時刻の打刻は `date` コマンドを使用して時間(時分秒)まで正確に行うこと。
- 新規履歴は **ファイル末尾** に追加すること。

## History Log

Archive

- None

### 日時: 2026/04/05 01:15 JST — Regular branch sorry 完全解消

1. 目的:
   - `qAdicGapReductionRegularBranch_of_global` の sorry を解消する。
   - ZMod unit 理論を使った witness R の自動構成を formal 化。
2. 実施:
   - `GapDivisibleBranch.lean` に以下の補助定理を新設:
     - `sub_one_eq_sub_mul_inv`: `z * ↑u⁻¹ - 1 = (z - ↑u) * ↑u⁻¹`
     - `pow_mul_unit_inv_eq_one`: `z^p = ↑u^p → (z * ↑u⁻¹)^p = 1`
     - `zpow_eq_ypow_zmod`: `x^p+y^p=z^p, q|x → z^p = y^p in ZMod(q^p)`
     - `isUnit_sub_of_not_dvd_gap`: `¬q|(z-y) → IsUnit(z-y) in ZMod(q^p)`
   - 主定理 `qAdicGapReductionRegularBranch_of_global` を 6 step で証明:
     - Step 1: `Coprime x y + q|x → ¬q|y → y` は `ZMod(q^p)` の unit
     - Step 2: R := z · y⁻¹ in `ZMod(q^p)` 構成
     - Step 3: z^p = y^p → R^p = 1
     - Step 4: ¬q|(z-y) → IsUnit(R-1)
     - Step 5: `geom_sum_eq_zero...` で Φ_p(R) = 0
     - Step 6: hGlobal に (R, Φ_p=0, z=R·y) を供給 → conclusion
3. 結論:
   - `GapDivisibleBranch.lean` は **sorry-free** になった ✅
   - Kummer ディレクトリ全体の sorry は 1 箇所のみ（CyclotomicPrincipalization.lean:120）
   - no-sorry theorem: 8 本（前回 6 本から +2）
   - sorry theorem: 2 本（前回 3 本から -1、1 つの distinct open kernel に帰着）
4. 検証:
   - `lake build` 全体 green
   - `#print axioms qAdicGapReductionRegularBranch_of_global` → `[propext, Classical.choice, Quot.sound]`（sorryAx なし）
5. 失敗事例:
   - `inv_pow` は ZMod n (非 DivisionMonoid) では使えない → Units.val_pow_eq_pow_val + Units.val_mul 経由で回避
   - `Dvd.dvd.pow` は `q ∣ x → q ∣ x^p` のみ（指数のみ変化）→ `pow_dvd_pow_of_dvd` が正しい（base も変化）
   - `Nat.cast_add` の rw 順序で goal が汚染される → `conv_lhs => rw [hsplit, Nat.cast_add, hmod, add_zero]` で一括処理
   - `ZMod.IsUnit.IsUnit_IsUnit` は存在しない → `ZMod.coe_unitOfCoprime` が正しい名前
6. 次の課題:
   - 唯一の open kernel: `cyclotomicPrincipalization_of_classGroupPTorsionFree`
   - これは Kummer 理論/ideal class group の formal 化 = genuine global stage

## Note

タイムスタンプの打刻は `date` コマンドを使用して、実際の日時を正確に記録してください。例: `date "+%Y/%m/%d %H:%M JST"` など。

※コミット時間がより正確であり、異なる場合は、コミット時間を優先とする。

## Template

### 日時: `タイムスタンプ date コマンドを使用して年月日時分まで` JST (template)

1. 目的:
   - （内容）
2. 実施:
   - （内容）
3. 結論:
   - （内容）
4. 検証:
   - （内容）
5. 失敗事例:
   - （内容）
6. 次の課題:
   - （内容）
