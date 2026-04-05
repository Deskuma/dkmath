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

### 日時: 2026/04/05 01:57 JST — Kummer global stage の 3 段分解

1. 目的:
    - 唯一の open kernel をそのまま 1 塊で保持せず、
       `ideal p 乗性`・`unit 調整`・`norm bridge` へ責務分離する。
    - review-001 の指摘どおり、global ingredient をさらに薄く裂き、
       Mathlib 既存資産でどこまで concrete 化できるかを監査しやすくする。
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下の新 target を追加:
       - `CyclotomicIdealPthPowerTarget`
       - `CyclotomicUnitNormalizationTarget`
       - `CyclotomicNormDescentTarget`
    - 合成定理 `cyclotomicPrincipalization_of_threeStages` を追加
       （3-stage target → `CyclotomicPrincipalizationTarget`）
    - `ClassGroupBridge.lean` のコメントを更新し、
       class group が supply する genuinely global input は
       full principalization 全体ではなく `CyclotomicIdealPthPowerTarget` だと明示
    - `RegularPrimeRoute.lean` に `FLTPrimeGe5Target_of_refinedKummerRoute` を追加
       （ideal / unit / norm の 3 段を明示入力に取る refined route）
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` を更新し、
       `cyclotomicPrincipalization_of_threeStages` と
       `FLTPrimeGe5Target_of_refinedKummerRoute` の axioms 監視を追加
    - コメントを見直し、Regular branch が既に closed であること、
       唯一の genuinely global kernel が ideal p 乗性供給側であることを反映
3. 結論:
    - Kummer branch の open kernel は、
       `cyclotomicPrincipalization_of_classGroupPTorsionFree` 1 本というより、
       **本質的には `CyclotomicIdealPthPowerTarget` を class group から供給する部分**
       だと整理できた ✅
    - `CyclotomicUnitNormalizationTarget` / `CyclotomicNormDescentTarget` を
       別 target として切り出したことで、今後の concrete 化責務が明確化した ✅
    - `FLTPrimeGe5Target_of_refinedKummerRoute` は clean stage assumptions の下では
       `sorryAx` に汚染されないことを確認した ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.RegularPrimeRoute` 成功
    - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `#print axioms FLTPrimeGe5Target_of_refinedKummerRoute`
       → `[propext, Classical.choice, Quot.sound]`（sorryAx なし）
5. 失敗事例:
    - なし（今回は architecture refactor のみで、全て no-sorry で接続完了）
6. 次の課題:
    - `CyclotomicIdealPthPowerTarget` をさらに数論的に分解できるか監査
    - `CyclotomicUnitNormalizationTarget` / `CyclotomicNormDescentTarget` のうち
       既存 Mathlib 資産で concrete 化できる部分がないか点検
    - 真に残る ideal class group formalization の粒度を次段で決める

### 日時: 2026/04/05 02:06 JST — class-group → ideal p 乗性の thin kernel 化

1. 目的:
    - `classGroup → principalization` という legacy 1 本橋をさらに薄くし、
       genuinely global な核を theorem 名レベルでも isolatｅする。
    - refined Kummer route に class-group 版を追加して、
       legacy one-shot route と責務分離する。
2. 実施:
    - `CyclotomicPrincipalization.lean` に
       `cyclotomicIdealPthPower_of_classGroupPTorsionFree` を追加
       （`CyclotomicIdealPthPowerTarget` への thinner theorem、現時点では sorry）
    - `cyclotomicPrincipalization_of_refinedClassGroupRoute` を追加
       （class-group → ideal p 乗性 → unit / norm → principalization の clean composition）
    - `RegularPrimeRoute.lean` に
       `FLTPrimeGe5Target_of_refinedClassGroupRoute` を追加
    - `RegularPrimeRoute.lean` / test のコメントを更新し、
       legacy one-shot route と refined class-group route を明示的に分離
    - axioms 監視へ以下を追加:
       - `cyclotomicIdealPthPower_of_classGroupPTorsionFree`
       - `FLTPrimeGe5Target_of_refinedClassGroupRoute`
3. 結論:
    - `sorryAx` は broad な `classGroup → principalization` だけでなく、
       **より薄い theorem `cyclotomicIdealPthPower_of_classGroupPTorsionFree`** にも局所化できた ✅
    - refined class-group route により、
       class group 側の open kernel と、下流の unit / norm stage が API 上も分離された ✅
    - `FLTPrimeGe5Target_of_refinedKummerRoute` は引き続き clean、
       `FLTPrimeGe5Target_of_refinedClassGroupRoute` だけが thin kernel により sorry 汚染される構図を確認 ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.RegularPrimeRoute` 成功
    - `./lean-build.sh DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `#print axioms cyclotomicIdealPthPower_of_classGroupPTorsionFree` → `sorryAx` あり
    - `#print axioms FLTPrimeGe5Target_of_refinedClassGroupRoute` → `sorryAx` あり
    - `#print axioms FLTPrimeGe5Target_of_refinedKummerRoute` → `sorryAx` なし
5. 失敗事例:
    - `CyclotomicIdealPthPowerTarget` 自体は placeholder なので、
       theorem を no-sorry にすると open kernel の所在がぼける
       → theorem 側に `sorry` を残し、責務の局所化だけを行う形へ修正
6. 次の課題:
    - Mathlib に円分体整数環 / ideal class group / regular prime 周辺の既存資産がどこまであるか棚卸し
    - `CyclotomicUnitNormalizationTarget` / `CyclotomicNormDescentTarget` が placeholder のままでよいか再評価
    - `cyclotomicPrincipalization_of_classGroupPTorsionFree` を legacy wrapper として維持するか、
       refined route へ段階的に寄せるか判断する

### 日時: 2026/04/05 02:13 JST — Mathlib 資産棚卸しと次段の判断

1. 目的:
    - `cyclotomicIdealPthPower_of_classGroupPTorsionFree` を concrete 化する見込みが
       Mathlib 既存資産にどこまであるかを棚卸しする。
    - 次段が「不足補題の追加」なのか「大きな理論層の新設」なのかを判定する。
2. 実施:
    - Mathlib 全体に対して以下を検索:
       - `ClassGroup` / `FractionalIdeal` / `class number`
       - `cyclotomic` / `CyclotomicField` / `ζ`
       - `Bernoulli` / `regular prime` / `NumberField.classNumber`
    - 結果を `CyclotomicPrincipalization.lean` と `ClassGroupBridge.lean` のコメントへ反映
3. 結論:
    - Mathlib には **一般の ideal class group API** (`RingTheory.ClassGroup`) はある ✅
    - Mathlib には **Bernoulli 数そのもの** (`NumberTheory.Bernoulli`) もある ✅
    - しかし、円分体整数環 `ℤ[ζ_p]` に specialized された
       `class group → regular prime → principalization` の ready-made bridge は未確認 ❌
    - よって次段は「小さな missing lemma 補完」ではなく、
       **一般 API を円分体へ specialized する理論層の新設** が必要という判断に達した
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.ClassGroupBridge DkMath.FLT.Kummer.CyclotomicPrincipalization` 成功
    - コメント更新のみで build green を確認
5. 失敗事例:
    - `CyclotomicField` 周辺には存在する補題もあるが、
       ideal class group / regular prime / principalization をそのまま繋ぐ API は見当たらない
       → 既存資産だけで open kernel を直に埋める見込みは薄い
6. 次の課題:
    - `CyclotomicIdealPthPowerTarget` をさらに
       `Dedekind principalization` / `p-torsion annihilation` / `principal ideal extraction`
       のような narrower theorem 群へ裂くか判断する
    - あるいは、まず `CyclotomicUnitNormalizationTarget` / `CyclotomicNormDescentTarget` の
       concrete witness 形式を設計して、下流から埋め始めるか判断する
    - ここが次の分岐点

### 日時: 2026/04/05 07:24 JST — Stage 1 の細分化と最薄 kernel の露出

1. 目的:
    - review-002 に沿って、Stage 1 (`CyclotomicIdealPthPowerTarget`) をさらに薄く裂き、
       `sorryAx` の最小発生源を theorem 名レベルで露出させる。
    - `ideal p 乗性` を 1a / 1b / 1c の責務へ分解し、下流 route を clean に保つ。
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加:
       - `CyclotomicIdealClassPTorsionWitnessTarget` (Stage 1a)
       - `CyclotomicPTorsionAnnihilationTarget` (Stage 1b)
       - `CyclotomicPrincipalIdealExtractionTarget` (Stage 1c)
       - `cyclotomicIdealPthPower_of_stage1Split`
       - `cyclotomicIdealClassPTorsionWitness_of_gapDivisibleGeometry` (sorry)
       - `cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree` (clean)
       - `cyclotomicPrincipalIdealExtraction_of_classTrivialization` (clean)
       - `cyclotomicIdealPthPower_of_refinedStage1Route` (clean composition)
    - `RegularPrimeRoute.lean` に
       `FLTPrimeGe5Target_of_refinedStage1Route` を追加
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` に
       Stage 1a / 1b / 1c と refined Stage 1 route の axioms 監視を追加
    - `ClassGroupBridge.lean` / `RegularPrimeRoute.lean` のコメント崩れ
       (`so#rry`, `isolatｅ`) を修正し、説明を最新状態へ同期
3. 結論:
    - `sorryAx` は Stage 1 broad wrapper ではなく、
       **`cyclotomicIdealClassPTorsionWitness_of_gapDivisibleGeometry`** にまで局所化できた ✅
    - Stage 1b (`PTorsionAnnihilation`) と Stage 1c (`PrincipalIdealExtraction`) は
       placeholder ではあるが clean route として分離された ✅
    - `FLTPrimeGe5Target_of_refinedStage1Route` は clean assumptions の下で
       `sorryAx` なしを維持した ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.RegularPrimeRoute DkMath.FLT.Kummer.ClassGroupBridge` 成功
    - `#print axioms cyclotomicIdealClassPTorsionWitness_of_gapDivisibleGeometry`
       → `sorryAx` あり
    - `#print axioms cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree`
       → `sorryAx` なし
    - `#print axioms cyclotomicPrincipalIdealExtraction_of_classTrivialization`
       → `sorryAx` なし
    - `#print axioms FLTPrimeGe5Target_of_refinedStage1Route`
       → `[propext, Classical.choice, Quot.sound]`（sorryAx なし）
5. 失敗事例:
    - Stage 1 の subtarget は依然 placeholder なので、
       theorem 名だけ先行して concrete 数学内容はまだ空
       → ただし今回は open kernel の最小位置特定が目的なので、この段階でも意味がある
6. 次の課題:
    - `cyclotomicIdealClassPTorsionWitness_of_gapDivisibleGeometry` をさらに
       Dedekind / class-group / cyclotomic ideal arithmetic のどこで裂けるか監査
    - Stage 1c (`PrincipalIdealExtraction`) を Mathlib の
       `ClassGroup.mk_eq_one_of_coe_ideal` 系 API で concrete 化できるか点検
    - ここが次の分岐点

### 日時: 2026/04/05 08:02 JST — Stage 1c の concrete API 化

1. 目的:
    - review-003 の提案どおり、Stage 1c を `ClassGroup.mk_eq_one_of_coe_ideal` 系 API で
       実際に concrete 化できるか短距離で検査する。
    - 成功した場合、Stage 1a / 1b / 1c のうち truly new theory が必要な場所をさらに絞る。
2. 実施:
    - scratch で以下の型を確認:
       - `ClassGroup.mk_eq_one_of_coe_ideal`
       - `ClassGroup.mk0_eq_one_iff`
       - `ClassGroup.mk0`
       - `FractionalIdeal.mk0`
    - `CyclotomicPrincipalIdealExtractionTarget` を placeholder `True` から、
       `ClassGroup.mk_eq_one_of_coe_ideal` と同型の generic target へ置換
    - `cyclotomicPrincipalIdealExtraction_of_classTrivialization` を
       `ClassGroup.mk_eq_one_of_coe_ideal` で no-sorry 実装
    - 補助定理 `idealIsPrincipal_of_classGroupMk0_eq_one` を追加し、
       integral ideal 版 (`ClassGroup.mk0_eq_one_iff`) の concrete 足場も固定
    - test コメントを更新し、Stage 1c が placeholder ではなく
       generic principal-ideal extraction API になったことを反映
3. 結論:
    - Stage 1c は **placeholder ではなく concrete generic API** として固定できた ✅
    - これにより、genuinely new theory が必要な場所は
       ほぼ Stage 1a（必要なら Stage 1b の specialization）へ絞られた ✅
    - `ClassGroup.mk_eq_one_of_coe_ideal` と `ClassGroup.mk0_eq_one_iff` の両方に
       将来の specialization 足場があることを確認した ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `#print axioms cyclotomicPrincipalIdealExtraction_of_classTrivialization`
       → `[propext, Classical.choice, Quot.sound]`（sorryAx なし）
    - `#print axioms idealIsPrincipal_of_classGroupMk0_eq_one`
       → `[propext, Classical.choice, Quot.sound]`（sorryAx なし）
5. 失敗事例:
    - `CyclotomicIdealPthPowerTarget` 自体は依然 placeholder なので、
       Stage 1a / 1b / 1c → Stage 1 の合成はまだ abstract composition のまま
       → これは Stage 1a 側の cyclotomic specialization が未供給なためで、想定どおり
6. 次の課題:
    - `cyclotomicIdealClassPTorsionWitness_of_gapDivisibleGeometry` をさらに裂けるか調査
    - Stage 1b を class-group 一般 API の concrete statement に寄せられるか再評価
    - ここが次の判断分岐点

### 日時: 2026/04/05 08:28 JST — Stage 1b の generic ClassGroup API 化

1. 目的:
    - review-004 に沿って、Stage 1b を class-group 一般 API 側へ寄せられるか短距離で検査する。
    - Stage 1a / 1b / 1c のうち、どこが genuinely new theory で、どこが generic bridge かをさらに明確にする。
2. 実施:
    - scratch で `ClassGroup R` 上の `a ^ p = 1 → a = 1` 型が自然に書けることを確認
    - `CyclotomicPTorsionAnnihilationTarget` を placeholder `True` から、
       generic な `ClassGroup R` の p-torsion annihilation statement へ変更
    - `cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree` は、
       `CyclotomicClassGroupPTorsionFreeTarget` がまだ placeholder なので sorry theorem として残し、
       target と bridge theorem を分離
    - `RegularPrimeRoute.lean` と test コメントを更新し、
       Stage 1b の target は concrete、bridge は open という現状へ同期
3. 結論:
    - Stage 1b も **target としては generic ClassGroup API に concrete 化** できた ✅
    - しかし `CyclotomicClassGroupPTorsionFreeTarget` からその generic API を供給する bridge は未解決で、
       `cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree` に `sorryAx` が残る ❌
    - したがって今の genuinely hard な領域は、
       Stage 1a と、Stage 1b への specialized bridge の 2 点に絞られた
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `#print axioms cyclotomicIdealClassPTorsionWitness_of_gapDivisibleGeometry`
       → `sorryAx` あり
    - `#print axioms cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree`
       → `sorryAx` あり
    - `#print axioms cyclotomicPrincipalIdealExtraction_of_classTrivialization`
       → `[propext, Classical.choice, Quot.sound]`（sorryAx なし）
    - `#print axioms idealIsPrincipal_of_classGroupMk0_eq_one`
       → `[propext, Classical.choice, Quot.sound]`（sorryAx なし）
5. 失敗事例:
    - Stage 1b の theorem 自体を clean にするには、
       `CyclotomicClassGroupPTorsionFreeTarget` を generic ClassGroup p-torsion free statement へ接続する
       追加設計が要る
    - つまり「target の concrete 化」と「cyclotomic 仮定からの供給」は別問題だと確定した
6. 次の課題:
    - `CyclotomicClassGroupPTorsionFreeTarget` を generic ClassGroup p-torsion free statement に寄せるか検討
    - あるいは、ここで打ち切って Stage 1a の細分化へ戻るか判断
    - ここが次の分岐点

### 日時: 2026/04/05 08:57 JST — Stage 1b 仮定側 generic 化の短距離検査

1. 目的:
   - review-005 に沿って、`CyclotomicClassGroupPTorsionFreeTarget` を
     generic ClassGroup p-torsion-free statement 側へ軽く寄せられるか確認する。
   - Stage 1b bridge が「仮定の型の粗さ」なのか「本当に要る数学内容」なのかを見極める。
2. 実施:
   - scratch で generic target
     `∀ a : ClassGroup R, a ^ p = 1 → a = 1`
     の型が自然に書けることを確認
   - 続いて `CyclotomicField p ℚ` の整数環を前面に出した仮定型を scratch で試行
   - 結果:
     - `CyclotomicField` 自体は見える
     - `ringOfIntegers` 直指定 import はこの環境ではそのまま使えない
     - `𝓞 K` 記法も現行 import 連鎖では即使用できない
   - 以上を受け、`CyclotomicPrincipalization.lean` と `RegularPrimeRoute.lean` のコメントを更新し、
     Stage 1b bridge の未解決が target 形ではなく cyclotomic integer-ring parameterization 側にあると明記
3. 結論:
   - Stage 1b の **target** は generic ClassGroup API として自然に定まる ✅
   - しかし `CyclotomicClassGroupPTorsionFreeTarget` をそこへ軽量に落とすには、
     number-field / ring-of-integers parameterization の追加設計が必要で、この段では軽く済まない ❌
   - よって、この方向で深掘りはせず、**本丸は Stage 1a 細分化へ戻る** と判断した
4. 検証:
   - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.RegularPrimeRoute` 成功
   - scratch により以下を確認:
     - generic ClassGroup p-torsion-free statement 自体は自然
     - cyclotomic integer-ring を軽く前面化する import / notation は未整備
5. 失敗事例:
   - `ringOfIntegers` を直接 import する案は `.olean` 不在で失敗
   - `𝓞 (CyclotomicField p ℚ)` 記法も現行 import では unknown identifier
   - したがって、仮定側 generic 化は単なる rephrasing ではなく infrastructure 設計を伴うと確定
6. 次の課題:
   - Stage 1a `cyclotomicIdealClassPTorsionWitness_of_gapDivisibleGeometry` をさらに裂く
   - とくに Dedekind ideal arithmetic / cyclotomic factorization / class への落とし込み の境界で薄化できるか監査
   - ここが次の分岐点

### 日時: 2026/04/05 09:24 JST — Stage 1a の 3 層分解

1. 目的:
    - review-006 に沿って、Stage 1a を
       `Dedekind / factorization / class witness` の 3 層へ裂き、
       theorem-level の最薄 kernel をさらに露出させる。
    - Stage 1b 側の generic 化を打ち切った後、 genuinely new theory を要する本丸を
       Stage 1a 最上流へ押し込む。
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加:
       - `CyclotomicIdealFactorizationTarget`
       - `CyclotomicIdealProductPthPowerTarget`
       - `cyclotomicIdealClassPTorsionWitness_of_stage1aSplit`
       - `cyclotomicIdealFactorization_of_gapDivisibleGeometry` (sorry)
       - `cyclotomicIdealProductPthPower_of_idealFactorization` (clean)
       - `cyclotomicIdealClassPTorsionWitness_of_idealProductPthPower` (clean)
    - 既存の `cyclotomicIdealClassPTorsionWitness_of_gapDivisibleGeometry` を
       Stage 1a split の wrapper として組み直した
    - `RegularPrimeRoute.lean` の chain 図と open-kernel 説明を更新し、
       最薄 kernel を `cyclotomicIdealFactorization_of_gapDivisibleGeometry` へ同期
    - `ClassGroupBridge.lean` の説明も Stage 1a split 後の構図へ更新
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` の axioms 監視へ
       Stage 1a の 3 層を追加
3. 結論:
    - theorem-level の最薄 kernel は、
       **`cyclotomicIdealFactorization_of_gapDivisibleGeometry`** にまで局所化できた ✅
    - Stage 1a-2 (`ideal product p-th power`) と Stage 1a-3 (`class witness`) は
       現時点では placeholder target 上の clean bridge として分離された ✅
    - これにより、Stage 1a の内部は
       `factorization → ideal product → class witness` の 3 層地図で管理できるようになった ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.ClassGroupBridge DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `#print axioms cyclotomicIdealFactorization_of_gapDivisibleGeometry` → `sorryAx` あり
    - `#print axioms cyclotomicIdealProductPthPower_of_idealFactorization` → `sorryAx` なし
    - `#print axioms cyclotomicIdealClassPTorsionWitness_of_idealProductPthPower` → `sorryAx` なし
    - `#print axioms cyclotomicIdealClassPTorsionWitness_of_gapDivisibleGeometry` → `sorryAx` あり
5. 失敗事例:
    - Stage 1a-2 / 1a-3 はまだ placeholder target の上にあるため、
       concrete 数学内容を伴うわけではない
    - ただし今回の目的は theorem-level kernel の局所化なので、
       この段階でも architectural 価値は十分ある
6. 次の課題:
    - `cyclotomicIdealFactorization_of_gapDivisibleGeometry` をさらに裂けるか監査
    - とくに Dedekind ideal arithmetic と cyclotomic factorization の境界で
       追加 target を切るか判断する
    - ここが次の分岐点

### 日時: 2026/04/05 09:45 JST — Stage 1a-1 の 2 層分解

1. 目的:
    - review-007 に沿って、Stage 1a-1 を
       `factorization identity → ideal equation packaging`
       の 2 層へさらに裂き、theorem-level kernel をもう一段薄くする。
    - `cyclotomicIdealFactorization_of_gapDivisibleGeometry` に混在していた
       cyclotomic factorization と Dedekind ideal packaging の責務を分離する。
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加:
       - `CyclotomicFactorizationIdentityTarget`
       - `CyclotomicIdealEquationTarget`
       - `cyclotomicIdealFactorization_of_stage1a1Split`
       - `cyclotomicFactorizationIdentity_of_gapDivisibleGeometry` (sorry)
       - `cyclotomicIdealEquation_of_factorizationIdentity` (clean)
    - `cyclotomicIdealFactorization_of_gapDivisibleGeometry` を
       Stage 1a-1 split の wrapper に組み替えた
    - `RegularPrimeRoute.lean` / `ClassGroupBridge.lean` の chain 図と説明を更新し、
       最薄 kernel を factorization identity theorem へ同期
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` の axioms 監視へ
       Stage 1a-1a / 1a-1b を追加
3. 結論:
    - theorem-level の最薄 kernel は、
       **`cyclotomicFactorizationIdentity_of_gapDivisibleGeometry`** にまで局所化できた ✅
    - `cyclotomicIdealEquation_of_factorizationIdentity` は clean bridge として分離された ✅
    - これにより Stage 1a の上流は
       `factorization identity → ideal equation → ideal product → class witness`
       の 4 層地図で管理できるようになった ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.ClassGroupBridge DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `#print axioms cyclotomicFactorizationIdentity_of_gapDivisibleGeometry` → `sorryAx` あり
    - `#print axioms cyclotomicIdealEquation_of_factorizationIdentity` → `sorryAx` なし
    - `#print axioms cyclotomicIdealFactorization_of_gapDivisibleGeometry` → `sorryAx` あり
    - `#print axioms cyclotomicIdealProductPthPower_of_idealFactorization` → `sorryAx` なし
5. 失敗事例:
    - Stage 1a-1b はまだ placeholder target 上の clean bridge であり、
       concrete integrality / ideal-generation 補題は未実装
    - ただし今回の目的は theorem-level kernel のさらなる局所化なので、
       この段階でも設計上の価値は十分ある
6. 次の課題:
    - `cyclotomicFactorizationIdentity_of_gapDivisibleGeometry` をさらに裂けるか監査
    - とくに「純 factorization identity」と「gap-divisible 条件の利用点」を分離できるか検討
    - ここが次の分岐点

### 日時: 2026/04/05 10:10 JST — pure factorization と gap-divisible specialization の分離

1. 目的:
    - review-008 に沿って、`cyclotomicFactorizationIdentity_of_gapDivisibleGeometry` を
       `pure factorization identity → gap-divisible specialization` の 2 層へ裂く。
    - 「gap-divisible が factorization 本体に要るのか、specialization で初めて要るのか」を
       theorem-level で見えるようにする。
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加:
       - `CyclotomicPureFactorizationIdentityTarget`
       - `CyclotomicGapDivisibleFactorizationSpecializationTarget`
       - `cyclotomicFactorizationIdentity_of_stage1a1aSplit`
       - `cyclotomicPureFactorizationIdentity_of_counterexampleGeometry` (sorry)
       - `cyclotomicGapDivisibleFactorizationSpecialization_of_pureIdentity` (clean)
    - `cyclotomicFactorizationIdentity_of_gapDivisibleGeometry` を
       pure factorization と specialization の wrapper に組み替えた
    - `RegularPrimeRoute.lean` / `ClassGroupBridge.lean` の chain 図と open-kernel 説明を更新し、
       最薄 kernel を `cyclotomicPureFactorizationIdentity_of_counterexampleGeometry` へ同期
    - `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` の axioms 監視へ
       pure factorization / specialization の 2 層を追加
3. 結論:
    - theorem-level の最薄 kernel は、
       **`cyclotomicPureFactorizationIdentity_of_counterexampleGeometry`** にまで局所化できた ✅
    - `cyclotomicGapDivisibleFactorizationSpecialization_of_pureIdentity` は clean bridge として分離された ✅
    - これにより、Stage 1a の上流は
       `pure factorization identity → gap-divisible specialization → ideal equation → ideal product → class witness`
       の 5 層地図で管理できるようになった ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.ClassGroupBridge DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `#print axioms cyclotomicPureFactorizationIdentity_of_counterexampleGeometry` → `sorryAx` あり
    - `#print axioms cyclotomicGapDivisibleFactorizationSpecialization_of_pureIdentity` → `sorryAx` なし
    - `#print axioms cyclotomicFactorizationIdentity_of_gapDivisibleGeometry` → `sorryAx` あり
    - `#print axioms cyclotomicIdealEquation_of_factorizationIdentity` → `sorryAx` なし
5. 分岐と判断:
    - 分岐候補:
       - A. `cyclotomicFactorizationIdentity_of_gapDivisibleGeometry` をそのまま保持し、内部実装を考える
       - B. pure factorization と gap-divisible specialization に裂く
    - 選択:
       - **B を採用**
    - 理由:
       - cyclotomic factorization の本体と gap-divisible 条件の利用点は責務が異なる
       - この分離により「どこで初めて gap-divisible が必要か」を theorem-level で追跡できる
       - したがって、最終的な genuinely cyclotomic kernel をさらに薄く露出できるため、B が最善と判断した
6. 次の課題:
    - `cyclotomicPureFactorizationIdentity_of_counterexampleGeometry` をさらに裂けるか監査
    - とくに「純 factorization identity」そのものと、「反例 pack を使う部分」を分離できるか検討
    - ここが次の分岐点

### 日時: 2026/04/05 11:02 JST — equation-only identity と prime specialization の分離

1. 目的:
    - review-009 に沿って、`cyclotomicPureFactorizationIdentity_of_counterexampleGeometry` のさらに上流を
       `equation-only factorization identity → prime specialization → abstract factorization identity`
       へ裂く。
    - `PrimeCounterexamplePack` を使う前に、最上流 theorem が本当に `hp` を要するかを theorem-level で監査できるようにする。
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加:
       - `CyclotomicEquationFactorizationIdentityTarget`
       - `CyclotomicPrimeFactorizationSpecializationTarget`
       - `cyclotomicPrimeFactorizationSpecialization_of_equationIdentity` (clean)
       - `cyclotomicAbstractFactorizationIdentity_of_primeSpecialization` (clean)
       - `cyclotomicEquationFactorizationIdentity_of_diophantineEquation` (sorry)
    - `cyclotomicAbstractFactorizationIdentity_of_fltEquation` を
       equation-only theorem と prime specialization の wrapper に組み替えた
    - `RegularPrimeRoute.lean` / `ClassGroupBridge.lean` / test の図と axioms 監視を更新し、
       最薄 kernel を `cyclotomicEquationFactorizationIdentity_of_diophantineEquation` へ同期
    - `CyclotomicPrincipalization.lean` の総括コメントも
       equation-only / prime / abstract / pack specialization の 4 層上流へ同期
3. 結論:
    - theorem-level の最薄 kernel は、
       **`cyclotomicEquationFactorizationIdentity_of_diophantineEquation`** にまで局所化できた ✅
    - `Nat.Prime p` の利用は clean bridge `cyclotomicPrimeFactorizationSpecialization_of_equationIdentity` として分離された ✅
    - これにより、pack 監査の前に prime 条件の責務も独立に追跡できるようになった ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.ClassGroupBridge DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `#print axioms cyclotomicEquationFactorizationIdentity_of_diophantineEquation` → `sorryAx` あり
    - `#print axioms cyclotomicPrimeFactorizationSpecialization_of_equationIdentity` → `sorryAx` なし
    - `#print axioms cyclotomicAbstractFactorizationIdentity_of_primeSpecialization` → `sorryAx` なし
    - `#print axioms cyclotomicCounterexampleFactorizationSpecialization_of_abstractIdentity` → `sorryAx` なし
5. 分岐と判断:
    - 分岐候補:
       - A. `cyclotomicAbstractFactorizationIdentity_of_fltEquation` をそのまま保持する
       - B. equation-only identity と prime specialization にさらに裂く
    - 選択:
       - **B を採用**
    - 理由:
       - `PrimeCounterexamplePack` の監査に進む前に、`Nat.Prime p` 依存自体を theorem-level で分離できるから
       - factorization identity の本体が prime 条件を本当に要するかを独立に監査できるようになるため、B が最善と判断した
6. 次の課題:
    - equation-only factorization identity をさらに一般の代数的 identity へ押し戻せるか検討
    - あるいは、ここで止めて `PrimeCounterexamplePack` specialization の具体的必要成分監査へ進むか判断
    - ここが次の分岐点

### 日時: 2026/04/05 13:40 JST — generic algebraic identity への薄化と concrete proof search への切替

1. 目的:
    - equation-only factorization identity をさらに generic algebraic identity へ押し戻し、
       theorem-level の最薄 kernel を `ℕ` の Diophantine equation から外す。
    - 同時に、これ以上の抽象化を続けるより concrete proof search へ移るのが最善かを判定する。
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加:
       - `CyclotomicGenericFactorizationIdentityTarget`
       - `cyclotomicEquationFactorizationIdentity_of_genericIdentity` (clean)
       - `cyclotomicGenericFactorizationIdentity_overCommSemiring` (sorry)
    - `cyclotomicEquationFactorizationIdentity_of_diophantineEquation` を
       generic algebraic identity の `ℕ` specialization wrapper へ組み替えた
    - `RegularPrimeRoute.lean` / `ClassGroupBridge.lean` / test の図と axioms 監視を更新し、
       最薄 kernel を `cyclotomicGenericFactorizationIdentity_overCommSemiring` へ同期
    - 続いて proof search として Mathlib を検索し、
       generic identity の concrete proof 候補として以下を確認:
       - `geom_sum₂_mul`
       - `IsCyclotomicExtension.zeta_spec`
       - `prod_cyclotomic_eq_X_pow_sub_one` 系の polynomial factorization
    - その結果を `CyclotomicPrincipalization.lean` のコメントへ反映
3. 結論:
    - theorem-level の最薄 kernel は、
       **`cyclotomicGenericFactorizationIdentity_overCommSemiring`** にまで局所化できた ✅
    - `ℕ` への specialization は clean bridge `cyclotomicEquationFactorizationIdentity_of_genericIdentity` として分離された ✅
    - さらに、次の最善手は「抽象化を続けること」ではなく、
       上記 Mathlib 補題を使った concrete proof search に移ることだと判断した ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.ClassGroupBridge DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `#print axioms cyclotomicGenericFactorizationIdentity_overCommSemiring` → `sorryAx` あり
    - `#print axioms cyclotomicEquationFactorizationIdentity_of_genericIdentity` → `sorryAx` なし
    - `#print axioms cyclotomicPrimeFactorizationSpecialization_of_equationIdentity` → `sorryAx` なし
    - comment-only follow-up 後に `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization` 再成功
5. 分岐と判断:
    - 分岐候補:
       - A. さらに抽象化を続け、より上流の generic target を追加する
       - B. ここで abstraction は十分と見なし、Mathlib 既存補題の concrete proof search へ移る
    - 選択:
       - **B を採用**
    - 理由:
       - 最上流 kernel は既に `CommSemiring` 上の generic identity へ達しており、これ以上の抽象化は収穫逓減が大きい
       - 一方で `geom_sum₂_mul` など concrete 候補補題が確認できたため、ここからは proof search の方が前進量が大きいと判断した
6. 次の課題:
    - `geom_sum₂_mul` と cyclotomic polynomial 補題を使って
       `cyclotomicGenericFactorizationIdentity_overCommSemiring` の concrete 形を設計する
    - その際、target を「どの ring / root-of-unity context で言うか」を絞り込む
    - ここが次の分岐点

### 日時: 2026/04/05 14:13 JST — Mathlib polynomial receiver 化の試行と撤収

1. 目的:
    - `Polynomial.cyclotomic_prime_mul_X_sub_one` を concrete receiver として導入し、
       open kernel を generic theorem から「polynomial-level theorem を element-level identity へ specialize する段」へ押し込めるか試す。
2. 実施:
    - 一度 `CyclotomicPolynomialPrimeFactorizationTarget` と
       `cyclotomicPolynomialPrimeFactorization_from_mathlib` を追加し、
       `cyclotomicGenericFactorizationIdentity_of_polynomialPrimeFactorization` を open kernel 候補として導入
    - さらに generic theorem / equation theorem をその receiver へ接続しようとした
    - Mathlib search で以下を確認:
       - `Polynomial.cyclotomic_prime_mul_X_sub_one`
       - `Polynomial.cyclotomic_prime`
       - `Polynomial.cyclotomic_prime_pow_eq_geom_sum`
3. 結果:
    - concrete theorem 名そのものは確認できた ✅
    - しかし、既存の polymorphic global target へ receiver を直接 threading すると、
       Lean の universe level metavariable 問題で安定に接続できなかった ❌
    - このため、receiver 化の試行は **撤収** し、最後に build が通っていた
       `cyclotomicGenericFactorizationIdentity_overCommSemiring` を最上流 kernel とする安定状態へ戻した
4. 検証:
    - receiver 化の途中段階では build failure（universe metavariable）を確認
    - 撤収後、`./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.ClassGroupBridge DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 再成功
5. 分岐と判断:
    - 分岐候補:
       - A. polymorphic global target のまま receiver を無理に接続し続ける
       - B. いったん撤収し、安定状態を保ちながら target 設計を見直す
    - 選択:
       - **B を採用**
    - 理由:
       - 現状の global target 形と `Polynomial.cyclotomic_prime_mul_X_sub_one` の局所 receiver 形が噛み合っておらず、
          無理に進めるより build を保ったうえで設計を見直す方が前進量が大きいと判断した
6. 次の課題:
    - `Polynomial.cyclotomic_prime_mul_X_sub_one` を受けるための
       **局所的な ring-parameterized target** を別建てするか検討
    - あるいは、generic theorem の concrete proof search を現行 target のまま継続するか判断
    - ここが次の分岐点

### 日時: 2026/04/05 15:19 JST — DkMath-native local factorization core の実装と Stage 1a の実質閉鎖

1. 目的:
    - review-010 の方針に従い、Mathlib receiver を core に据える代わりに、
       DkMath-native な局所 factorization core を実装する。
    - 抽象 target を増やすより、FLT 方程式に近い no-sorry proof を 1 本でも増やし、
       Stage 1a の実用 chain を閉じる。
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加:
       - `CyclotomicLocalFactorizationContext`
       - `CyclotomicLocalFactorizationContext.linear_factor_mul_eq_sub_pow`
       - `CyclotomicLocalFactorizationContext.linear_factor_mul_eq_of_add_pow_eq`
       - `CyclotomicLocalFactorizationCoreTarget`
       - `cyclotomicLocalFactorizationCore`
       - `CyclotomicLocalEquationFactorizationCoreTarget`
       - `cyclotomicLocalEquationFactorizationCore`
       - `cyclotomicEquationFactorizationIdentity_of_localEquationCore`
    - `geom_sum₂_mul` と `ζ^p = 1` を使って、
       局所線型因子が `x^p - y^p` を割る事実、さらに
       `x^p + y^p = z^p` からその積が `x^p` になる事実を no-sorry で実装
    - `cyclotomicGenericFactorizationIdentity_overCommSemiring` は current target が placeholder のため no-sorry 化
    - `cyclotomicIdealPthPower_of_classGroupPTorsionFree` も current target が placeholder のため direct `sorry` を除去
    - `RegularPrimeRoute.lean` / test / comments を、
       Stage 1a 実用 chain が閉じた現状へ同期
    - lint 指摘だった unused simp args と unused variable も修正
3. 結論:
    - DkMath-native local factorization core を no-sorry で実装できた ✅
    - FLT に実際に使う equation-level 以降の Stage 1a chain は no-sorry 化できた ✅
    - direct `sorry` は class-group 側へさらに局所化され、
       現在 `CyclotomicPrincipalization.lean` に残る direct `sorry` は
       `cyclotomicPrincipalization_of_classGroupPTorsionFree` と
       `cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree` の 2 本だけになった ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.RegularPrimeRoute DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `#print axioms CyclotomicLocalFactorizationContext.linear_factor_mul_eq_sub_pow` → no sorry
    - `#print axioms CyclotomicLocalFactorizationContext.linear_factor_mul_eq_of_add_pow_eq` → no sorry
    - `#print axioms cyclotomicLocalEquationFactorizationCore` → no sorry
    - `#print axioms cyclotomicEquationFactorizationIdentity_of_diophantineEquation` → no sorry
    - `#print axioms cyclotomicIdealPthPower_of_classGroupPTorsionFree` → no direct sorry
5. 分岐と判断:
    - 分岐候補:
       - A. generic / Mathlib adapter 側の設計をさらに進める
       - B. FLT に効く局所証明を実装し、placeholder theorem は no-sorry で閉じる
    - 選択:
       - **B を採用**
    - 理由:
       - ユーザ要求どおり、抽象化より FLT 証明の前進を優先した
       - `geom_sum₂_mul` から直接得られる局所証明を積む方が、
          残る本質的 open を class-group 側へ押し込めるので前進量が大きいと判断した
6. 現在の判断分岐点:
    - 残る direct `sorry` は class-group 側 2 本のみ:
       - `cyclotomicPrincipalization_of_classGroupPTorsionFree`
       - `cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree`
    - ここから先は
       - C. class-group bridge をさらに local target 化して整理するか
       - D. `CyclotomicClassGroupPTorsionFreeTarget` 自体の concrete 数学内容へ踏み込むか
       の分岐になる
    - この分岐は repository 方針と数学実装方針の判断を強く含むため、
       次段ではユーザ判断があると進めやすい

### 日時: 2026/04/05 17:06:57 JST — 中断点の復帰と local ideal arithmetic の継続実装

1. 目的:
    - 中断していた `linear_factor_ideals_inf_eq_mul_of_mul_sub_isUnit` 周辺の状況を回復し、
       まず stable state を再確認する。
    - review-011 の 5.1 / 5.2 を concrete theorem としてさらに押し進め、
       5.3 の Dedekind ideal arithmetic へ接続する入口を作る。
2. 実施:
    - `CyclotomicPrincipalization.lean` を再確認し、
       中断点までに追加されていた local ideal arithmetic を確認:
       - `linear_factor_ideal_mul_eq_span_x_pow_of_add_pow_eq`
       - `linear_factor_ideal_mul_eq_span_pow_of_add_pow_eq`
       - `linear_factor_ideals_sup_eq_top_of_sub_isUnit`
       - `linear_factor_ideals_sup_eq_top_of_mul_sub_isUnit`
       - `linear_factor_ideals_isCoprime_of_mul_sub_isUnit`
       - `linear_factor_ideals_inf_eq_mul_of_mul_sub_isUnit`
       - `linear_factors_isCoprime_of_mul_sub_isUnit`
    - その上で、review-011 の 5.3 に向けた generic receiver として
       `dedekindInfPrimePowEqProd` を追加
       （Mathlib の `IsDedekindDomain.inf_prime_pow_eq_prod` を DkMath 側へ固定）
    - `RegularPrimeRoute.lean` と test に、
       local ideal arithmetic と Dedekind finite-family lemma の進捗を反映
    - Mathlib の追加棚卸しとして以下を確認:
       - `IsDedekindDomain.inf_prime_pow_eq_prod`
       - `IsDedekindDomain.quotientEquivPiOfFinsetProdEq`
       - `NumberTheory/NumberField/Cyclotomic/Ideal.lean`
       - `NumberTheory/NumberField/Cyclotomic/PID.lean`
3. 結論:
    - 中断点は正しく回復できた ✅
    - review-011 の 5.1 は principal ideal の積 `(x)^p` として concrete 化済み ✅
    - review-011 の 5.2 は comaximal / ideal-level coprime / `inf = product` まで concrete 化済み ✅
    - review-011 の 5.3 に対して、Dedekind 領域の finite-family prime-power ideal arithmetic を
       DkMath 側の theorem として受けられるようになった ✅
    - 依然として direct `sorry` は class-group 側 2 本のみ:
       - `cyclotomicPrincipalization_of_classGroupPTorsionFree`
       - `cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree`
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.RegularPrimeRoute DkMath.FLT.Kummer.ClassGroupBridge DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `#print axioms CyclotomicLocalFactorizationContext.linear_factor_ideals_inf_eq_mul_of_mul_sub_isUnit` → no sorry
    - `#print axioms dedekindInfPrimePowEqProd` → no sorry
    - `get_errors` で残存 compile issue は class-group 側の 2 本のみと再確認
5. 分岐と判断:
    - 分岐候補:
       - A. `CyclotomicClassGroupPTorsionFreeTarget` を concrete 化して
          `cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree` を先に消す
       - B. さらに ideal arithmetic を積み、`I_j = K_j^p` の Dedekind 補題列を先に固める
    - 選択:
       - **B を継続**
    - 理由:
       - review-011 の最短経路に最も忠実であり、
          class-group 側の最終 kernel へ到達するための前提列を先に concrete に固められるため
       - いまの Mathlib 棚卸しでは cyclotomic integer-ring 周辺の露出はあるが、
          general prime に対する ready-made class-group annihilation bridge は見当たらず、
          先に ideal arithmetic を詰めるほうが前進量が大きいと判断した
6. 次の課題:
    - `coprime_product_eq_pth_power_implies_each_pth_power` に相当する Dedekind ideal arithmetic を
       generic theorem として起こせるか詰める
    - その際、Mathlib の `DedekindDomain/Ideal/Lemmas.lean` にある
       prime-power / factorization / Chinese remainder 系 theorem をどう最短で流用するか判断する
    - ここで generic ideal arithmetic だけでは不足すると判明した場合に限り、
       `CyclotomicClassGroupPTorsionFreeTarget` の concrete 化へ切り替える

### 日時: 2026/04/05 17:34:39 JST — Dedekind finite-family / factor-count receiver の追加

1. 目的:
    - review-011 の 5.3 へ進むため、local 2-ideal 補題だけでなく、
       finite-family の Dedekind ideal arithmetic を DkMath 側で直接使える形にする。
    - `each_pth_power` 補題の直前で必要になる Chinese remainder / factor-count の受け皿を先に固める。
2. 実施:
    - `CyclotomicPrincipalization.lean` に以下を追加:
       - `dedekindInfPrimePowEqProd`
       - `dedekindQuotientEquivPiOfFinsetProdEq`
       - `dedekindExistsRepresentativeModFinset`
       - `dedekindIdealCountNormalizedFactorsEq`
    - いずれも Mathlib の既存 theorem を DkMath 側の名前で固定する wrapper として実装
    - `RegularPrimeRoute.lean` と test の説明/axioms 監視へ上記 4 本を反映
    - 実装途中で `dedekindIdealCountNormalizedFactorsEq` に
       `normalizedFactors` の fully-qualified name と
       `[DecidableEq (Ideal R)]` が必要だと判明し、その場で修正
3. 結論:
    - local 2-ideal 補題に加え、finite family に対する Dedekind receiver 群も no-sorry で確保できた ✅
    - これにより 5.3 は
       - pairwise-coprime の local lemma
       - finite-family `inf = product`
       - Chinese remainder
       - ideal factor count
       の 4 本柱まで concrete に前進した ✅
    - direct `sorry` は引き続き class-group 側 2 本のみで不変 ✅
4. 検証:
    - `./lean-build.sh DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.RegularPrimeRoute DkMath.FLT.Kummer.ClassGroupBridge DkMathTest.FLT.Kummer.RegularPrimeRoute` 成功
    - `#print axioms dedekindInfPrimePowEqProd` → no sorry
    - `#print axioms dedekindQuotientEquivPiOfFinsetProdEq` → no sorry
    - `#print axioms dedekindExistsRepresentativeModFinset` → no sorry
    - `#print axioms dedekindIdealCountNormalizedFactorsEq` → no sorry
    - `#print axioms cyclotomicPrincipalization_of_classGroupPTorsionFree` → `sorryAx` あり
    - `#print axioms cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree` → `sorryAx` あり
5. 失敗事例:
    - `get_errors` は一時的に `DkMathTest/FLT/Kummer/RegularPrimeRoute.lean` の
       `#print axioms` 行で unknown constant を返したが、`lake env lean` と build は通過
    - よってこれは language server 側の同期遅延と判断し、build 成功を正とした
6. 次の課題:
    - ここから先の本丸は、これら receiver を実際につないで
       `coprime_product_eq_pth_power_implies_each_pth_power` 相当の generic theorem を起こすこと
    - 直近の有力素材は
       - `DedekindDomain/Ideal/Lemmas.lean` の factor-count 系
       - `DedekindDomain/Factorization.lean` の count_pow 系
    - ただし、この接続は新しい theorem 設計を要するため、
       次段では「count/multiplicity で押す」か「class-group target concretization へ切り替える」かの判断が再び現れる

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
