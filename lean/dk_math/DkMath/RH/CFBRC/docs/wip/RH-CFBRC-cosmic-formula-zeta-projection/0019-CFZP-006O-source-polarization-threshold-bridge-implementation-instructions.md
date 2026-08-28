# CFZP-0019 — CFZP-006O source polarization threshold bridge 実装指示書

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
6e350aa5eee72a4753cb06bf322485bd0de334b3
CFZP-006N implementation
```

直前 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaContactThresholdDecompositionAudit
```

006N で first-class 化された量を略記する。

```text
Δ := cfzpIntegratedPolarizedImbalance
T := cfzpIntegratedPolarizedContactThresholdLevel
G := pascalCenteredXiPrimeSideFiniteRadialContactDeficit
```

006N は exact に

```text
T - Δ = 4 * G
```

を与えた。

今回 CFZP-006O では、この signed difference を `ContactSlack` として一度だけ命名し、既存 CS24 / CS25 の exact finite ledger へ完全に接続する。

今回の中心は新しい positivity provider を作ることではない。

```text
ContactSlack
  = 4 * (CanonicalPolarizationRemainder - CanonicalPolarizationMass)
  = 4 * (ZeroCutoffDeficit - AggregateRayInteractionEnergy)
```

を Lean 上の canonical bridge として固定し、contact 条件を二つの既存 balance 条件へ exact に分類することが目的である。

---

# 1. 現行 source で確認済みの既存 API

この指示書では名前を推測しない。以下は現行 branch で確認済み。

## CS24

Module:

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCanonicalPolarizationSignedMassAudit
```

Definitions:

```lean
pascalCenteredXiPrimeSideCanonicalPolarizationMass
pascalCenteredXiPrimeSideCanonicalPolarizationRemainder
```

Exact theorem:

```lean
pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_canonicalRemainder_sub_mass
```

内容:

```text
G
  = CanonicalPolarizationRemainder
    - CanonicalPolarizationMass
```

既存 positivity:

```lean
pascalCenteredXiPrimeSideCanonicalPolarizationMass_nonneg
```

ただし CanonicalPolarizationRemainder の非負性は与えられていない。

既存 frontier:

```lean
PascalCenteredXiPrimeSideCanonicalPolarizationRemainderGap
  | noIndependentCofinalCanonicalRemainderProvider
```

## CS25

Module:

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit
```

Definition:

```lean
pascalCenteredXiPrimeSideAggregateRayInteractionEnergy
```

Exact theorem:

```lean
pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_zeroCutoff_deficit_sub_interaction
```

内容:

```text
G(ε,W,X)
  = G(ε,W,0)
    - AggregateRayInteractionEnergy(ε,W,X)
```

また exact に

```lean
pascalCenteredXiPrimeSideCanonicalPolarization_common_carrier_cancels
```

があり、

```text
CanonicalPolarizationRemainder - CanonicalPolarizationMass
  = G(ε,W,0) - AggregateRayInteractionEnergy
```

を与える。

既存 frontier:

```lean
PascalCenteredXiPrimeSideAggregateInteractionReachGap
  | noIndependentCofinalInteractionReachProvider
```

この frontier を今回消してはならない。

---

# 2. 推奨 module

```text
DkMath.RH.CFBRC.CosmicFormulaZetaContactThresholdPolarizationBridgeAudit
```

推奨 path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaContactThresholdPolarizationBridgeAudit.lean
```

最低限 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaContactThresholdDecompositionAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit
import Mathlib.Tactic
```

CS25 が CS24 を import 済みなので、通常は CS24 の direct import を重ねなくてよい。

`DkMath/RH.lean` に public import を追加する。

---

# 3. Gate A — contact slack の命名

新しい量は一つだけにする。

推奨:

```lean
noncomputable def cfzpIntegratedPolarizedContactSlack
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  cfzpIntegratedPolarizedContactThresholdLevel ε X W -
    cfzpIntegratedPolarizedImbalance ε X W
```

これは signed difference であり、非負とは未証明。

したがって以下は禁止。

```text
ContactSlackMass
ContactSlackGap
PositiveSlack
```

など positivity を暗示する命名。

単純 fold theorem は置いてよい。

```text
ContactSlack = ThresholdLevel - IntegratedPolarizedImbalance
```

---

# 4. Hypotheses

threshold から radial deficit へ降りる bridge は 006N の theorem

```lean
cfzpIntegratedPolarizedContactThresholdLevel_sub_imbalance_eq_four_mul_radialContactDeficit
```

を再利用する。

したがって、基本 section は 006N の `FiniteLedger` section と同じ hypotheses をそのまま使ってよい。

少なくとも以下の exact 条件を変えない。

```text
hε : 0 < ε
hSafe
hZeta
hPHZ
hWeighted
hρ
hρm
hPairLeft
hPairRight
hArch
hElem
```

CS24 / CS25 側の theorem 自体は `hε` だけで成立するが、`T - Δ = 4G` に接続する箇所では 006N と同じ ledger hypotheses が必要である。

不必要に新しい仮定を追加しない。

---

# 5. Gate B — radial contact slack

まず 006N を fold して exact に

```text
ContactSlack
  = 4 * RadialContactDeficit
```

を証明する。

推奨 theorem 名:

```lean
cfzpIntegratedPolarizedContactSlack_eq_four_mul_radialContactDeficit
```

これは今回の基底 bridge。

係数は `4`。`4π` ではない。

006N で CompletionRemainder を使う場合だけ

```text
ContactSlack = 4π * CompletionRemainder
```

も安価に再掲してよいが、今回の中心ではない。

---

# 6. Gate C — CS24 canonical polarization bridge

既存 exact theorem

```lean
pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_canonicalRemainder_sub_mass
```

を用いて

```text
ContactSlack
  = 4 *
      (CanonicalPolarizationRemainder
        - CanonicalPolarizationMass)
```

を証明する。

推奨 theorem 名:

```lean
cfzpIntegratedPolarizedContactSlack_eq_four_mul_canonicalPolarizationRemainder_sub_mass
```

さらに threshold の加法形も first-class theorem として置く。

```text
ThresholdLevel
  = IntegratedPolarizedImbalance
    + 4 *
        (CanonicalPolarizationRemainder
          - CanonicalPolarizationMass)
```

推奨 theorem 名:

```lean
cfzpIntegratedPolarizedContactThresholdLevel_eq_imbalance_add_four_mul_canonicalPolarizationSlack
```

ここで `CanonicalPolarizationRemainder - CanonicalPolarizationMass` は signed quantity。

`CanonicalPolarizationMass >= 0` は既知でも、`CanonicalPolarizationRemainder >= 0` を追加してはならない。

---

# 7. Gate D — CS24 contact balance classification

Gate C から exact に以下を揃える。

## zero

```text
ContactSlack = 0
  ↔ CanonicalPolarizationRemainder = CanonicalPolarizationMass
```

## threshold contact

```text
IntegratedPolarizedImbalance = ThresholdLevel
  ↔ CanonicalPolarizationRemainder = CanonicalPolarizationMass
```

## nonnegative side

```text
0 <= ContactSlack
  ↔ CanonicalPolarizationMass <= CanonicalPolarizationRemainder
```

同値に

```text
IntegratedPolarizedImbalance <= ThresholdLevel
  ↔ CanonicalPolarizationMass <= CanonicalPolarizationRemainder
```

## nonpositive side

```text
ContactSlack <= 0
  ↔ CanonicalPolarizationRemainder <= CanonicalPolarizationMass
```

同値に

```text
ThresholdLevel <= IntegratedPolarizedImbalance
  ↔ CanonicalPolarizationRemainder <= CanonicalPolarizationMass
```

これらは sign provider ではない。

特に

```text
CanonicalPolarizationMass <= CanonicalPolarizationRemainder
```

そのものを無条件に証明しない。

---

# 8. Gate E — CS25 zero-cutoff / interaction bridge

既存 theorem

```lean
pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_zeroCutoff_deficit_sub_interaction
```

を使って exact に

```text
ContactSlack
  = 4 *
      (RadialContactDeficit(ε,W,0)
        - AggregateRayInteractionEnergy(ε,W,X))
```

を証明する。

推奨 theorem 名:

```lean
cfzpIntegratedPolarizedContactSlack_eq_four_mul_zeroCutoffDeficit_sub_interaction
```

threshold 加法形:

```text
ThresholdLevel
  = IntegratedPolarizedImbalance
    + 4 *
        (RadialContactDeficit(ε,W,0)
          - AggregateRayInteractionEnergy(ε,W,X))
```

も記録する。

ここで interaction は signed。非負とは仮定しない。

---

# 9. Gate F — CS25 interaction reach classification

Gate E から exact に以下を揃える。

## zero/contact

```text
ContactSlack = 0
  ↔ RadialContactDeficit(ε,W,0)
      = AggregateRayInteractionEnergy(ε,W,X)
```

```text
IntegratedPolarizedImbalance = ThresholdLevel
  ↔ RadialContactDeficit(ε,W,0)
      = AggregateRayInteractionEnergy(ε,W,X)
```

## nonnegative side

```text
0 <= ContactSlack
  ↔ AggregateRayInteractionEnergy(ε,W,X)
      <= RadialContactDeficit(ε,W,0)
```

同値に

```text
IntegratedPolarizedImbalance <= ThresholdLevel
  ↔ AggregateRayInteractionEnergy(ε,W,X)
      <= RadialContactDeficit(ε,W,0)
```

## nonpositive side

```text
ContactSlack <= 0
  ↔ RadialContactDeficit(ε,W,0)
      <= AggregateRayInteractionEnergy(ε,W,X)
```

同値に

```text
ThresholdLevel <= IntegratedPolarizedImbalance
  ↔ RadialContactDeficit(ε,W,0)
      <= AggregateRayInteractionEnergy(ε,W,X)
```

これは interaction reach の分類であり、reach theorem ではない。

既存 marker

```text
noIndependentCofinalInteractionReachProvider
```

を保持する。

---

# 10. Gate G — dual balance theorem

今回もっとも読みやすい統合 theorem を一つ置く。

同じ finite hypotheses の下で exact に

```text
IntegratedPolarizedImbalance = ThresholdLevel
  ↔ CanonicalPolarizationRemainder = CanonicalPolarizationMass
  ↔ RadialContactDeficit(ε,W,0) = AggregateRayInteractionEnergy(ε,W,X)
```

Lean の chained `↔` は結合の読みが悪くなる場合があるので、実装では pair で明示してよい。

推奨安全形:

```lean
(... IntegratedPolarizedImbalance = ThresholdLevel) ↔
  (CanonicalPolarizationRemainder = CanonicalPolarizationMass ∧
    RadialContactDeficit ε W 0 = AggregateRayInteractionEnergy ε W X)
```

ただしこの conjunction 形は、両方が同じ contact condition と同値であることから証明する。

または二 theorem に分けてもよい。

重要なのは API 上で

```text
contact
  ↔ canonical polarization balance
  ↔ interaction reaches zero-cutoff baseline
```

が明示されること。

---

# 11. Gate H — common-carrier cancellation の exact identification

CS25 には既に

```lean
pascalCenteredXiPrimeSideCanonicalPolarization_common_carrier_cancels
```

がある。

これを CFZP slack に fold して、安価なら

```text
ContactSlack / 4
  = CanonicalPolarizationRemainder - CanonicalPolarizationMass
  = RadialContactDeficit(ε,W,0) - AggregateRayInteractionEnergy(ε,W,X)
```

に相当する theorem を置く。

division by `4` を導入するより、Lean では factor `4` を保った次の形を推奨する。

```text
4 * (CanonicalPolarizationRemainder - CanonicalPolarizationMass)
  = 4 * (RadialContactDeficit(ε,W,0) - AggregateRayInteractionEnergy)
```

ただし CS25 theorem そのものが既に unscaled exact equality を与えるので、単なる重複になるなら追加しなくてよい。

今回の新規価値は `ContactSlack` / `ThresholdLevel` 側への bridge である。

---

# 12. Frontier markers

新しい marker を置く場合は「不足している provider」を正確に限定する。

推奨:

```lean
inductive CfzpContactThresholdCanonicalPolarizationDominanceGap : Prop
  | noIndependentCanonicalPolarizationDominanceProvider
```

```lean
inductive CfzpContactThresholdInteractionReachGap : Prop
  | noIndependentZeroCutoffInteractionReachProvider
```

```lean
inductive CfzpContactSlackToPrimeMirrorGapIdentificationGap : Prop
  | noExactPrimeMirrorGapIdentificationProvided
```

既存 CS24 / CS25 marker の再 export だけで十分なら、新 marker を増やしすぎなくてよい。

いずれも impossibility theorem ではない。

---

# 13. 数学的解釈の境界

006O が Green になると、signed contact slack は exact に

```text
ContactSlack
  = 4 * RadialContactDeficit
```

かつ

```text
ContactSlack
  = 4 * (CanonicalPolarizationRemainder - CanonicalPolarizationMass)
```

かつ

```text
ContactSlack
  = 4 * (ZeroCutoffDeficit - AggregateRayInteractionEnergy)
```

となる。

ここで重要なのは、残った frontier が

```text
「新しい正の Gap を探す」
```

ではなく

```text
AggregateRayInteractionEnergy が
ZeroCutoffDeficit に到達するか
```

という **interaction reach problem** に移ること。

CS25 はすでに common carrier が差し引きで消えることを証明している。
したがって contact の本質は common positive carrier ではなく signed interaction と baseline の一致である。

ただし、到達性そのものは今回証明しない。

---

# 14. Firewall

今回も以下を禁止する。

- `ContactSlack >= 0` の無条件 theorem
- `ThresholdLevel >= 0` の無条件 theorem
- `CanonicalPolarizationRemainder >= 0` の新規 theorem
- `AggregateRayInteractionEnergy >= 0` の無条件 theorem
- `AggregateRayInteractionEnergy <= ZeroCutoffDeficit` の無条件 theorem
- `CanonicalPolarizationMass <= CanonicalPolarizationRemainder` の無条件 theorem
- `ContactSlack` を `Mass`, `Big`, `Body`, `Gap` と呼ぶこと
- CS24 canonical polarization remainder を CFZP prime-mirror Gap と同一視すること
- CompletionRemainder を prime-mirror amplitude Gap または cosmic coordinate gap `δ²` と同一視すること
- finite contact を pointwise polarization balance と同一視すること
- finite contact を complex source zero と同一視すること
- finite contact を zeta zero と同一視すること
- interaction reach gap が解決したと主張すること
- cofinal / infinite limit を新規に導入すること
- `X -> infinity`
- infinite Euler product
- RH conclusion
- `Complex.arg`
- 新しい global `Complex.log` branch
- `sorry` / `admit` / `axiom` / `native_decide`

---

# 15. 成功条件

最低限、次が Green なら CFZP-006O 完了とする。

```text
1. ContactSlack := ThresholdLevel - IntegratedImbalance を定義
2. ContactSlack = 4 * RadialContactDeficit
3. ContactSlack = 4 * (CanonicalPolarizationRemainder - CanonicalPolarizationMass)
4. ThresholdLevel = Imbalance + 4 * (CanonicalRemainder - CanonicalMass)
5. contact ↔ CanonicalRemainder = CanonicalMass
6. canonical side の sign/order iff を exact に分類
7. ContactSlack = 4 * (ZeroCutoffDeficit - AggregateRayInteractionEnergy)
8. ThresholdLevel = Imbalance + 4 * (ZeroCutoffDeficit - AggregateRayInteractionEnergy)
9. contact ↔ ZeroCutoffDeficit = AggregateRayInteractionEnergy
10. interaction side の sign/order iff を exact に分類
11. dual balance classification を public theorem として記録
12. common-carrier cancellation / interaction reach frontier を保持
13. ContactSlack / ThresholdLevel の positivity を主張しない
14. prime-mirror/cosmic Gap と同一視しない
15. source/zeta zero / RH へ進まない
16. DkMath.RH public import
17. target module build Green
18. lake build DkMath.RH Green
19. ./lean-build.sh Green
20. ./lean-test.sh Green
21. git diff --check Green
22. 新規 module に sorry / admit / axiom / native_decide / Complex.arg / Complex.log なし
```

---

# 16. 次 Gate への判断材料

006O が Green なら exact chain は

```text
contact slack / 4
  = RadialContactDeficit
  = CanonicalPolarizationRemainder - CanonicalPolarizationMass
  = ZeroCutoffDeficit - AggregateRayInteractionEnergy
```

まで閉じる。

すると次 CFZP-006P の第一候補は、`ZeroCutoffDeficit` 自体の finite baseline 構造を public API として整理し、

```text
ZeroCutoffDeficit
  versus
AggregateRayInteractionEnergy
```

の reach problem に何が不足しているかを audit すること。

特に CS25 内部には zero-cutoff deficit を fixed radial second moment と independent correction source で表す private theorem があるため、006P では private theorem を再利用しようとせず、既存 public API だけで同じ baseline representation を安全に public 化できるかを先に調べる。

その時点でも independent reach provider が無ければ、それを次の本当の数学的 frontier として固定する。