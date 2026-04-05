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
