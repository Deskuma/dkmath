# CFZP-0018 — CFZP-006N contact threshold decomposition audit 実装指示書

## 0. 作業対象

Repository:

```text
Deskuma/dkmath
```

Working branch:

```text
wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0
```

この指示書作成直前の Green checkpoint:

```text
f0cbf1daeddd99865383e167e32db38ea4ca5fcf
Add: CFZP-0017: CFZP-006M integrated polarized balance threshold audit
```

CFZP-006M 実装 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaIntegratedPolarizedBalanceThresholdAudit
```

006M では、forward integrated polarized masses

```text
Pplus  >= 0
Pminus >= 0
```

と rectangle background `B` に対して、二種類の balance が exact に分離された。

```text
Pminus = Pplus
  ↔ TopMismatch = 0
```

一方、radial-contact balance は

```text
Pminus - Pplus = 4 * π * B
  ↔ CompletionRemainder = 0
  ↔ RadialContactDeficit = 0
```

である。

さらに CompletionRemainder / RadialContactDeficit の正負条件は、同じ threshold inequality に exact に翻訳された。

今回 CFZP-006N では、この右辺

```text
4 * π * RectangleBackground
```

を first-class な **contact threshold level** として取り出し、その内部を既存 completion / independent complete-source / polarization / interaction ledger へ分解する。

重要: この threshold level は現時点で非負とは証明されていない。したがって `ThresholdMass` ではなく `ThresholdLevel` と呼ぶ。

---

# 1. 推奨 module

```text
DkMath.RH.CFBRC.CosmicFormulaZetaContactThresholdDecompositionAudit
```

推奨 path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaContactThresholdDecompositionAudit.lean
```

最低限 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaIntegratedPolarizedBalanceThresholdAudit
import Mathlib.Tactic
```

CS24 / CS25 の既存 theorem surface を直接使う場合は、その定義元 module を追加 import してよい。

`DkMath/RH.lean` に public import を追加する。

---

# 2. 今回の数学的核心

略記する。

```text
Δ := Pminus - Pplus
B := RectangleBackground
G := RadialContactDeficit
R := CompletionRemainder
```

006L / 006M と既存 completion geometry から

```text
G = π * B - Δ / 4
G = π * R
```

が既に exact に得られている。

したがって

```text
4 * π * B = Δ + 4 * G
```

および

```text
4 * π * B = Δ + 4 * π * R
```

が exact に成り立つ。

今回の第一目的は、この右辺全体を contact threshold level として明示し、

```text
ThresholdLevel
  = IntegratedPolarizedImbalance
    + ContactSlack
```

という構造を Lean theorem として固定することにある。

ここで `ContactSlack` は別の新しい物理量を発明するのではなく、まず `4 * G` または `4 * π * R` という既存量の exact alias / expression として扱う。

---

# 3. Gate A — integrated imbalance と threshold level の命名

必要なら integrated imbalance を短い alias にしてよい。

推奨:

```lean
noncomputable def cfzpIntegratedPolarizedImbalance
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  cfzpProjectedMirrorForwardIntegratedMinusMass ε X W -
    cfzpProjectedMirrorForwardIntegratedPlusMass ε X W
```

次に threshold level:

```lean
noncomputable def cfzpIntegratedPolarizedContactThresholdLevel
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  4 * Real.pi *
    pascalCenteredXiPrimeSideFiniteRectangleBackground ε W X
```

引数順は既存 CFZP naming に合わせて調整してよい。

必須の単純 fold:

```text
cfzpIntegratedPolarizedImbalance
  = Pminus - Pplus

cfzpIntegratedPolarizedContactThresholdLevel
  = 4 * π * RectangleBackground
```

これらは notation convenience であり、新しい数学的仮定を導入しない。

重要:

- `ThresholdLevel >= 0` は置かない。
- `ThresholdLevel` を `mass` と呼ばない。
- `RectangleBackground` の sign を仮定しない。

---

# 4. Gate B — radial-deficit slack decomposition

006L / 006M の exact radial-contact ledger を使い、同じ hypotheses の下で

```text
ThresholdLevel
  = IntegratedPolarizedImbalance
    + 4 * RadialContactDeficit
```

を証明する。

同値な差分形も first-class theorem として記録することを推奨する。

```text
ThresholdLevel - IntegratedPolarizedImbalance
  = 4 * RadialContactDeficit
```

これにより contact 条件は

```text
IntegratedPolarizedImbalance = ThresholdLevel
  ↔ RadialContactDeficit = 0
```

と読み直せる。

006M に同値 theorem が既にある場合、今回は新 alias に fold するだけでよい。重複証明ではなく public API の正規化が目的である。

係数 `4` と符号を必ず Lean に確認させる。

---

# 5. Gate C — completion-remainder slack decomposition

既存

```text
RadialContactDeficit = π * CompletionRemainder
```

または 006K の rectangle ledger を使い、exact に

```text
ThresholdLevel
  = IntegratedPolarizedImbalance
    + 4 * π * CompletionRemainder
```

を証明する。

差分形:

```text
ThresholdLevel - IntegratedPolarizedImbalance
  = 4 * π * CompletionRemainder
```

も記録する。

この theorem は今回の load-bearing statement である。

解釈は

```text
contact threshold level
  = actual projected integrated imbalance
    + completion slack
```

である。

ただし `completion slack >= 0` は証明していないため、ここでも「余剰質量」「正の Gap」とは呼ばない。

---

# 6. Gate D — independent complete-source decomposition

既存 CFZP-006 source completion theorem:

```text
CompletionRemainder
  = FixedRadialSecondMoment
    - IndependentCompleteSourceReal
```

を使い、exact に

```text
ThresholdLevel
  = IntegratedPolarizedImbalance
    + 4 * π *
        (FixedRadialSecondMoment
          - IndependentCompleteSourceReal)
```

を証明する。

同値な threshold residual:

```text
ThresholdLevel - IntegratedPolarizedImbalance
  = 4 * π *
      (FixedRadialSecondMoment
        - IndependentCompleteSourceReal)
```

も安価なら記録する。

ここで初めて threshold の右側が

```text
projected integrated imbalance
+
fixed radial reference - independent complete source
```

という既存二系統の exact ledger に分解される。

注意:

- `FixedRadialSecondMoment >= IndependentCompleteSourceReal` は仮定・証明しない。
- independent complete source の sign を追加しない。

---

# 7. Gate E — threshold classification の first-class API

006M の theorem を named threshold level に rewrite し、以下を exact に揃える。

## 7.1 zero/contact

```text
IntegratedPolarizedImbalance = ThresholdLevel
  ↔ CompletionRemainder = 0
```

```text
IntegratedPolarizedImbalance = ThresholdLevel
  ↔ RadialContactDeficit = 0
```

## 7.2 nonnegative side

```text
IntegratedPolarizedImbalance <= ThresholdLevel
  ↔ 0 <= CompletionRemainder
```

```text
IntegratedPolarizedImbalance <= ThresholdLevel
  ↔ 0 <= RadialContactDeficit
```

## 7.3 nonpositive side

```text
ThresholdLevel <= IntegratedPolarizedImbalance
  ↔ CompletionRemainder <= 0
```

```text
ThresholdLevel <= IntegratedPolarizedImbalance
  ↔ RadialContactDeficit <= 0
```

これは新 sign theorem ではない。006M の sign frontier を named threshold level に exact 翻訳するだけである。

`IntegratedPolarizedImbalance <= ThresholdLevel` 自体を無条件に証明してはならない。

---

# 8. Gate F — polarized balance `Pminus = Pplus` との比較

006M の結果を threshold notation で再確認する。

`Pminus = Pplus` の下では integrated imbalance は zero なので、既存 exact results から

```text
CompletionRemainder = RectangleBackground
RadialContactDeficit = π * RectangleBackground
ThresholdLevel = 4 * RadialContactDeficit
```

を得られる。

最後の theorem は安価なら追加する。

重要な意味:

```text
Pminus = Pplus
```

は `TopMismatch = 0` を意味するが、contact condition ではない。

contact にはさらに

```text
ThresholdLevel = 0
```

すなわち同じ balance 下では `RectangleBackground = 0` が必要になる。

安価なら exact に

```text
(Pminus = Pplus ∧ RadialContactDeficit = 0)
  ↔ (Pminus = Pplus ∧ RectangleBackground = 0)
```

のような paired statement を置いてもよい。

ただし source zero / zeta zero へは進まない。

---

# 9. Gate G — CS24 canonical polarization ledger への接続（既存 API が確認できれば推奨）

既存 CS24 には概念的に

```text
CanonicalPolarizationMass := Eplus / 2
CanonicalPolarizationRemainder := π * (...) + Eminus / 2

RadialContactDeficit
  = CanonicalPolarizationRemainder
    - CanonicalPolarizationMass
```

という exact ledger が存在する。

実装時に repository の現行 theorem / definition 名を必ず確認し、**名前を推測して作らない**こと。

該当 API がそのまま利用できるなら、今回の threshold decomposition と組み合わせて

```text
ThresholdLevel
  = IntegratedPolarizedImbalance
    + 4 *
        (CanonicalPolarizationRemainder
          - CanonicalPolarizationMass)
```

を exact に証明する。

さらに安価なら

```text
IntegratedPolarizedImbalance = ThresholdLevel
  ↔ CanonicalPolarizationRemainder = CanonicalPolarizationMass
```

を記録する。

ここで既存 `CanonicalPolarizationMass` の nonnegativity があっても、`CanonicalPolarizationRemainder` の nonnegativity を新たに主張しない。

この Gate は exact API の発見が難しい場合は optional とする。無理に CS24 を import して再構成しない。

---

# 10. Gate H — CS25 zero-cutoff / interaction ledger への接続（既存 API が確認できれば推奨）

既存 CS25 には概念的に

```text
RadialContactDeficit
  = ZeroCutoffDeficit - AggregateRayInteractionEnergy
```

という exact interaction classification がある。

過去 audit で確認された theorem candidate は

```text
pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_zeroCutoff_deficit_sub_interaction
```

だが、実装前に現行 source で正式名・引数を確認すること。

利用できるなら

```text
ThresholdLevel
  = IntegratedPolarizedImbalance
    + 4 *
        (ZeroCutoffDeficit - AggregateRayInteractionEnergy)
```

を exact に閉じる。

また

```text
IntegratedPolarizedImbalance = ThresholdLevel
  ↔ ZeroCutoffDeficit = AggregateRayInteractionEnergy
```

まで安価なら記録する。

これは sign provider ではない。

既存 marker

```text
noIndependentCofinalInteractionReachProvider
```

の意味を上書きしない。

この Gate も exact API が不自然に遠い場合は optional とする。

---

# 11. Gate I — raw RectangleBackground expansion（optional）

CS30 の `pascalCenteredXiPrimeSideFiniteRectangleBackground` は既に

```text
FixedRadialSecondMoment
+ ComplementBoundaryScalar
- NormalizedArchimedeanContribution
- NormalizedElementaryContribution
- 2 * TopArchimedeanCompanionScalar
- 2 * TopElementaryCompanionScalar
```

という finite background definition を持つ。

必要なら threshold level を `4π` 倍したこの raw background expansion へ展開する theorem を置いてよい。

ただし今回の本質は source completion / canonical slack decomposition であり、単なる巨大 unfold は必須ではない。

---

# 12. Frontier markers

最低限、threshold level 自身の sign provider が無いことを明示する。

推奨:

```lean
inductive CfzpContactThresholdLevelNonnegativityGap : Prop
  | noIndependentThresholdLevelNonnegativityProvider
```

CS24/25 まで接続した場合は必要に応じて

```lean
inductive CfzpContactThresholdCanonicalBalanceReachGap : Prop
  | noIndependentCanonicalSlackSignOrReachProvider
```

を追加してよい。

これは impossibility theorem ではない。

---

# 13. Firewall

今回も以下を禁止する。

- `ThresholdLevel >= 0` の無条件 theorem
- `RectangleBackground >= 0` の無条件 theorem
- `CompletionRemainder >= 0` の新規 provider
- `RadialContactDeficit >= 0` の新規 provider
- threshold level を `Mass`, `Big`, `Body`, `Gap` と命名すること
- CompletionRemainder を CFZP prime-mirror Gap / cosmic coordinate Gap と同一視すること
- `Pminus = Pplus` を radial contact と同一視すること
- contact balance を pointwise polarization balance と同一視すること
- contact balance を complex source zero / zeta zero と同一視すること
- channel cross terms の消去
- total projected quadratic mass と Euler-only FullPairSum の同一視
- infinite Euler product
- `X -> infinity`
- RH conclusion
- `Complex.arg`
- 新しい global `Complex.log` branch
- `sorry` / `admit` / `axiom` / `native_decide`

---

# 14. 成功条件

最低限、次が Green なら CFZP-006N 完了とする。

```text
1. IntegratedPolarizedImbalance を named alias 化
2. ContactThresholdLevel := 4π * RectangleBackground を named alias 化
3. ThresholdLevel = Imbalance + 4 * RadialContactDeficit
4. ThresholdLevel = Imbalance + 4π * CompletionRemainder
5. ThresholdLevel - Imbalance = 4 * RadialContactDeficit
6. ThresholdLevel - Imbalance = 4π * CompletionRemainder
7. independent complete-source ledger へ exact fold
8. contact zero iff Imbalance = ThresholdLevel
9. remainder / radial-deficit sign iff threshold ordering の named theorem
10. ThresholdLevel の nonnegativity を主張しない
11. Pminus=Pplus と radial contact を同一視しない
12. source/zeta zero へ進まない
13. DkMath.RH public import
14. target module build Green
15. lake build DkMath.RH Green
16. nested ./lean-build.sh Green
17. nested ./lean-test.sh Green
18. git diff --check Green
19. 新規 module に sorry / admit / axiom / native_decide / Complex.arg / Complex.log なし
```

CS24 / CS25 への exact fold は推奨だが optional。現行 API が自然に届く場合だけ追加する。

---

# 15. 次 Gate への判断材料

006N が Green になると、contact threshold は概念的に

```text
ThresholdLevel
  = Pminus - Pplus
    + 4 * RadialContactDeficit
```

かつ

```text
ThresholdLevel
  = Pminus - Pplus
    + 4π * CompletionRemainder
```

さらに

```text
ThresholdLevel
  = Pminus - Pplus
    + 4π * (FixedRadialSecondMoment - IndependentCompleteSourceReal)
```

まで分解される。

これにより「右側 `4πB` の正体」は単独の未知量ではなく、

```text
actual projected integrated imbalance
+
independent completion slack
```

として exact に読める。

次 CFZP-006O の第一候補は、CS24/25 の既存 canonical polarization / interaction ledger を 006N の threshold API と完全に接続し、

```text
contact
  ↔ canonical remainder = canonical mass
  ↔ zero-cutoff deficit = interaction
```

という **dual balance classification** を一枚の audit module に統合すること。

その時点でも独立 sign / reach provider が無ければ、そこを次の本当の数学的 frontier として固定する。