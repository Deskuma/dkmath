# ABC–GN Next Campaign Reconnaissance

Date: 2026-07-26  
Status: **design only / start on a separate campaign branch**

## 1. 戦況

M1 により、奇素数指数 `p` の exceptional valuation excess は exact に消えた。

```text
τe = 0
De = 0
```

したがって `GNFinalBudgetBridge` に残る本質的な入力は次の二つである。

```text
M2  lifted-radical support growth
M3  non-exceptional valuation excess
```

本ノートは M2/M3 の theorem を追加しない。現在の M1 branch を閉じたまま、
次 campaign の最初の checkpoint を定めるための reconnaissance である。

## 2. 既存 API が与える境界

### M2: support

既存の budget interface は:

```lean
GNLiftRadicalGrowthBudgetAffine
```

であり、そこから:

```lean
Triple.nonExceptionalSupportBudgetAffine_of_liftGrowth
Triple.GNSupportBudgetAffine_of_liftGrowth
```

へ決定論的に輸送できる。

一方、primitive divisor / Zsigmondy 型の既存結果が直接与えるのは、典型的には
fresh prime の**存在または下界方向**である。必要な uniform support budget は
総 support の**上界方向**なので、この存在定理だけでは M2 は閉じない。

### M3: multiplicity

既存 API は high-lift locus を有限 support として正確に切り出している。

```lean
GNHighLiftPrime
GNNonExceptionalHighLiftPrime
highLiftSupport
valuationExcess_eq_sum_highLift
GNValuationExcess_eq_sum_highLift
GNValuationExcess_eq_zero_of_no_highLift
Triple.nonExceptionalHighLift_not_dvd_boundary
two_le_padicValNat_GN_of_highLift
padicValNat_GN_le_one_of_noHighLift
Triple.padic_powerDiff_le_one_of_nonExceptional_noHighLift
```

しかしこの API は high-lift prime の global rarity や uniform depth bound を
主張しない。M3 を単独で一様化する正面攻撃は、Wieferich/Hensel 型の
multiplicity 現象を直接扱うことになる。

## 3. 推奨する次戦線

最終 contract が必要とするのは M2 と M3 の個別最強定理ではなく、最終指数の
margin に収まる**合成予算**である。従って次 campaign は:

```text
support mass + multiplicity excess
```

を同じ有限 prime support 上で扱う joint support–multiplicity campaign とする。

出発点には既存の exact identity:

```lean
log_eq_log_rad_add_valuationExcess
```

および `GNValuationExcess_eq_sum_highLift` を使う。目標は、radical support と
high-lift depth を別々に過大評価せず、`log (GN ...)` の中で再結合した量を
最終 budget へ輸送できる最小 API を同定することである。

これは joint bound が既に証明可能だという主張ではない。M2/M3 の独立 uniform
bound より弱く、かつ `GNFinalBudgetBridge` に十分な命題が存在するかを最初に
監査する方針である。

## 4. 次 campaign の checkpoint 案

### JSM-001: Exact accounting audit

- `log_eq_log_rad_add_valuationExcess` の型と positivity 条件を固定する。
- `GNValuationExcess_eq_sum_highLift` と同一 support 上で書ける正確な恒等式を
  inventory する。
- M1 の exceptional zero を代入し、odd-prime non-exceptional normal form を得る。
- 新しい一様評価、解析的仮定、axiom は導入しない。

### JSM-002: Minimal combined budget contract

- `GNFinalBudgetBridge` が実際に必要とする合成係数・定数を逆算する。
- M2/M3 の個別 contract より弱い joint contract を定義できるか判定する。
- 既存 contract から joint contract への transport と、joint contract から
  final bridge への transport を分離する。

### JSM-003: Arithmetic obstruction audit

- primitive-divisor 情報が joint quantity のどの項に効くか確認する。
- high-lift depth が support growth と相殺または再配分可能か確認する。
- uniform theorem が得られなければ、未解決算術 input を exact obligation として
  文書化し、Lean 上の reduction theorem だけを閉じる。

## 5. Victory condition

次 campaign の勝利条件は、次のいずれかである。

```text
A. final bridge に十分な joint affine budget を無条件に証明する
B. 既存算術結果から joint budget への canonical reduction theorem を証明する
C. 不可能な強化を避け、残る外部算術 obligation を exact な Lean proposition
   として最小化する
```

`C` は ABC そのものの証明ではないが、形式化としては honest な前線固定である。

## 6. Branch hygiene

- M1 branch では設計記録だけを残し、M2/M3 実装を開始しない。
- 次 campaign は専用 branch と専用 checkpoint 文書から開始する。
- `abc_main_axiom`、FLT5/FLT7 WIP、`sorry`、新規 axiom、`native_decide`、
  有限列挙による一般証明に依存しない。
- M1 の一般 odd-prime endpoint を閉じた Core として import する。
