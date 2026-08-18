# CFZP-0020 — CFZP-006P zero-cutoff contact baseline public decomposition audit 実装指示書

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
83d158caa709111f92c33280d15477129140a8aa
Add: CFZP-0019: CFZP-006O source polarization threshold bridge
```

直前 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaContactThresholdPolarizationBridgeAudit
```

006O では signed contact slack が exact に

```text
ContactSlack
  = 4 * RadialContactDeficit(ε,W,X)
  = 4 * (CanonicalPolarizationRemainder - CanonicalPolarizationMass)
  = 4 * (RadialContactDeficit(ε,W,0) - AggregateRayInteractionEnergy(ε,W,X))
```

へ接続された。

したがって contact 条件は

```text
AggregateRayInteractionEnergy(ε,W,X)
  = RadialContactDeficit(ε,W,0)
```

という finite interaction reach condition と exact に同値になった。

今回 CFZP-006P では、右辺の `RadialContactDeficit(ε,W,0)` を first-class な **zero-cutoff radial-contact baseline** として public 化し、その source decomposition を既存 public theorem だけから exact に整理する。

private theorem を import 越しに再利用したり、同名コピーを作ったりしない。

---

# 1. 現行 source で確認済みの public API

## CS23

Module:

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideIndependentRadialContactProviderAudit
```

Definition:

```lean
pascalCenteredXiPrimeSideIndependentCompleteSourceReal
```

Exact theorem:

```lean
pascalCenteredXiPrimeSideIndependentCompleteSource_radialDeficit_eq
```

内容:

```text
RadialContactDeficit(ε,W,X)
  = π *
      (FixedRadialSecondMoment(W.R)
        - IndependentCompleteSourceReal(ε,W,X))
```

したがって `X = 0` へ特殊化すれば zero-cutoff baseline の complete-source 表現が public theorem だけで得られる。

## CS24

Module:

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCanonicalPolarizationSignedMassAudit
```

Definition:

```lean
pascalCenteredXiPrimeSideIndependentCorrectionSourceReal
```

Exact theorem:

```lean
pascalCenteredXiPrimeSideIndependentCompleteSourceReal_eq_prime_add_correction
```

内容:

```text
IndependentCompleteSourceReal(ε,W,X)
  = NormalizedPrimeContribution(ε,W,X)
    + IndependentCorrectionSourceReal(ε,W)
```

また public theorem:

```lean
pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_two_div_pi_modeSum
```

があり、`X = 0` では有限 mode sum が消えるため prime contribution は zero になるはずである。

ここは実装時に Lean の `simp` で確認すること。既存 theorem 名を新たに推測しない。

## CS25

Module:

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit
```

Public theorem:

```lean
pascalCenteredXiPrimeSideAggregateRayInteractionEnergy_eq_two_modeSum
```

があるため、必要なら `X = 0` で aggregate interaction energy が zero であることも public に証明できる。

また 006O からすでに

```text
ContactSlack
  = 4 * (RadialContactDeficit(ε,W,0) - AggregateRayInteractionEnergy(ε,W,X))
```

が利用可能。

---

# 2. 推奨 module

```text
DkMath.RH.CFBRC.CosmicFormulaZetaZeroCutoffContactBaselineAudit
```

推奨 path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaZeroCutoffContactBaselineAudit.lean
```

最低限 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaContactThresholdPolarizationBridgeAudit
import Mathlib.Tactic
```

006O の import chain で CS23 / CS24 / CS25 の public API へ届くため、不要な direct import は増やさなくてよい。

`DkMath/RH.lean` に public import を追加する。

---

# 3. Gate A — zero-cutoff baseline の命名

新しい first-class alias を一つ定義する。

推奨:

```lean
noncomputable def cfzpZeroCutoffRadialContactBaseline
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0
```

単純 fold theorem を置いてよい。

```text
cfzpZeroCutoffRadialContactBaseline
  = RadialContactDeficit(ε,W,0)
```

重要:

- `Baseline` は signed quantity。
- `BaselineMass` と呼ばない。
- `Baseline >= 0` は未証明。
- prime-mirror Gap / cosmic Gap と同一視しない。

---

# 4. Gate B — complete-source baseline representation

CS23 の public theorem

```lean
pascalCenteredXiPrimeSideIndependentCompleteSource_radialDeficit_eq
```

を `X = 0` に特殊化し、`hε : 0 < ε` の下で exact に

```text
ZeroCutoffBaseline
  = π *
      (FixedRadialSecondMoment(W.R)
        - IndependentCompleteSourceReal(ε,W,0))
```

を証明する。

推奨 theorem 名:

```lean
cfzpZeroCutoffRadialContactBaseline_eq_pi_mul_fixedMoment_sub_completeSourceZero
```

これは private theorem の再実装ではなく、既存 public theorem の zero-cutoff specialization とする。

---

# 5. Gate C — zero-cutoff prime contribution の消失

CS24 の public theorem

```lean
pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_two_div_pi_modeSum
```

を `X = 0` に特殊化し、exact に

```text
pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W 0
  = 0
```

を証明する。

推奨 CFZP theorem 名:

```lean
cfzpMellinQuadraticNormalizedPrimeContribution_zeroCutoff
```

第一候補 proof は既存 theorem を rewrite して `simp`。

概念的には

```text
range (0 + 1) = {0}
```

であり、`vonMangoldt 0` が zero なので有限和が消える。

もし `simp` だけで閉じなければ、現行 source の既存 simp theorem / definition を確認して最小限展開する。

禁止:

- 未確認 theorem 名を想像して呼ぶこと。
- prime contribution zero を解析接続や infinite Euler product から証明すること。

これは純粋な finite cutoff-zero identity である。

---

# 6. Gate D — complete source zero = correction source

Gate C と CS24 の public split

```lean
pascalCenteredXiPrimeSideIndependentCompleteSourceReal_eq_prime_add_correction
```

から exact に

```text
IndependentCompleteSourceReal(ε,W,0)
  = IndependentCorrectionSourceReal(ε,W)
```

を証明する。

推奨 theorem 名:

```lean
cfzpIndependentCompleteSourceReal_zeroCutoff_eq_correctionSourceReal
```

この theorem により zero-cutoff baseline の「prime-free baseline」構造が first-class になる。

ただし `correction source` の符号を追加しない。

---

# 7. Gate E — correction-source baseline representation

Gate B と Gate D から exact に

```text
ZeroCutoffBaseline
  = π *
      (FixedRadialSecondMoment(W.R)
        - IndependentCorrectionSourceReal(ε,W))
```

を証明する。

推奨 theorem 名:

```lean
cfzpZeroCutoffRadialContactBaseline_eq_pi_mul_fixedMoment_sub_correctionSource
```

これは今回の load-bearing theorem。

意味は

```text
interaction が到達すべき baseline
  = fixed radial reference
    minus non-prime correction source
```

である。

ここで「non-prime」は `X = 0` で prime contribution が finite に消えたという意味だけで使う。

解析接続や prime-free zeta object を新たに定義しない。

---

# 8. Gate F — correction source の raw finite expansion

既存 definition

```lean
pascalCenteredXiPrimeSideIndependentCorrectionSourceReal
```

は exact に

```text
NormalizedArchimedeanContribution
+ NormalizedElementaryContribution
+ NormalizedTopContribution
```

である。

安価なら public theorem として

```text
IndependentCorrectionSourceReal(ε,W)
  = NormalizedArchimedeanContribution(ε,W)
    + NormalizedElementaryContribution(ε,W)
    + NormalizedTopContribution(ε,W)
```

を記録する。

さらに baseline を

```text
ZeroCutoffBaseline
  = π *
      (FixedRadialSecondMoment
        - (NormalizedArchimedean
           + NormalizedElementary
           + NormalizedTop))
```

まで exact に展開してよい。

ただし単なる巨大 unfold になるなら theorem は一つだけでよい。

今回の目的は sign を証明することではなく、baseline の source components を公開 API として可視化すること。

---

# 9. Gate G — baseline sign/order classification

Gate E と `Real.pi_pos` から exact に以下を揃える。

## zero

```text
ZeroCutoffBaseline = 0
  ↔ IndependentCorrectionSourceReal
      = FixedRadialSecondMoment
```

左右の equality の向きは Lean proof が簡単な方でよい。

## nonnegative side

```text
0 <= ZeroCutoffBaseline
  ↔ IndependentCorrectionSourceReal
      <= FixedRadialSecondMoment
```

## nonpositive side

```text
ZeroCutoffBaseline <= 0
  ↔ FixedRadialSecondMoment
      <= IndependentCorrectionSourceReal
```

これは **classification** であって sign theorem ではない。

次を無条件に証明してはならない。

```text
IndependentCorrectionSourceReal <= FixedRadialSecondMoment
```

あるいは

```text
0 <= ZeroCutoffBaseline
```

---

# 10. Gate H — zero-cutoff interaction energy の消失（推奨）

CS25 の public theorem

```lean
pascalCenteredXiPrimeSideAggregateRayInteractionEnergy_eq_two_modeSum
```

を `X = 0` に特殊化して、安価なら exact に

```text
pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W 0
  = 0
```

を証明する。

推奨 theorem 名:

```lean
cfzpAggregateRayInteractionEnergy_zeroCutoff
```

これにより

```text
X = 0
```

では interaction がまだ baseline を削っていない、という finite ledger の初期状態が明示される。

これは monotonicity や future reach を意味しない。

特に

```text
InteractionEnergy(X) >= 0
InteractionEnergy(X+1) >= InteractionEnergy(X)
```

などは主張しない。

---

# 11. Gate I — 006O interaction reach を named baseline で正規化

006O の theorem を named baseline に rewrite し、同じ finite ledger hypotheses の下で exact に

```text
ContactSlack
  = 4 *
      (ZeroCutoffBaseline
        - AggregateRayInteractionEnergy(ε,W,X))
```

を証明する。

推奨 theorem 名:

```lean
cfzpIntegratedPolarizedContactSlack_eq_four_mul_zeroCutoffBaseline_sub_interaction
```

さらに contact classification:

```text
IntegratedPolarizedImbalance = ContactThresholdLevel
  ↔ ZeroCutoffBaseline
      = AggregateRayInteractionEnergy(ε,W,X)
```

を named baseline 版として記録する。

推奨 theorem 名:

```lean
cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_interaction_reaches_zeroCutoffBaseline
```

006O theorem の `simpa [cfzpZeroCutoffRadialContactBaseline]` で閉じるならそれを優先する。

---

# 12. Gate J — named baseline order/reach classification

006O の order iff を named baseline に rewrite して exact に揃える。

```text
0 <= ContactSlack
  ↔ AggregateRayInteractionEnergy <= ZeroCutoffBaseline
```

```text
ContactSlack <= 0
  ↔ ZeroCutoffBaseline <= AggregateRayInteractionEnergy
```

同様に threshold ordering:

```text
IntegratedPolarizedImbalance <= ContactThresholdLevel
  ↔ AggregateRayInteractionEnergy <= ZeroCutoffBaseline
```

```text
ContactThresholdLevel <= IntegratedPolarizedImbalance
  ↔ ZeroCutoffBaseline <= AggregateRayInteractionEnergy
```

これらも reach provider ではない。

---

# 13. Gate K — canonical zero-cutoff interpretation（optional）

既存 CS24 theorem:

```lean
pascalCenteredXiPrimeSideCanonicalPolarizationMass_zero
```

および

```lean
pascalCenteredXiPrimeSideCanonicalPolarizationRemainder_eq_zeroCutoff_deficit_add_minusMass
```

と zero-cutoff minus-energy identityを用いて、安価なら

```text
CanonicalPolarizationMass(ε,W,0) = 0
```

は既存 theorem をそのまま参照し、さらに

```text
CanonicalPolarizationRemainder(ε,W,0)
  = ZeroCutoffBaseline
```

を public CFZP theorem として記録してよい。

ただしこれは baseline の positivity を意味しない。

CS24 の canonical remainder は signed source frontier のまま。

---

# 14. Frontier marker

今回の baseline sign に必要な不足を明示する。

推奨:

```lean
inductive CfzpZeroCutoffBaselineNonnegativityGap : Prop
  | noIndependentCorrectionSourceBelowFixedMomentProvider
```

interaction reach については 006O / CS25 の既存 marker を保持する。

必要なら CFZP 側 alias marker を一つだけ追加してよいが、重複 marker を増やしすぎない。

この marker は impossibility theorem ではない。

---

# 15. 数学的解釈

006P が Green になると、contact の二項差

```text
ZeroCutoffBaseline - AggregateRayInteractionEnergy
```

の左項が exact に

```text
π *
  (FixedRadialSecondMoment
    - IndependentCorrectionSourceReal)
```

へ分解される。

したがって現在の finite contact problem は

```text
AggregateRayInteractionEnergy
```

が

```text
π *
  (FixedRadialSecondMoment
    - Archimedean/Elementary/Top correction source)
```

へ到達するか、という形にまで具体化される。

ここでもまだ二つの独立問題を混同しない。

```text
A. ZeroCutoffBaseline の sign / size
B. AggregateRayInteractionEnergy の reach
```

A が非負と分かっても B は自動ではない。
B の exact equality が得られても pointwise zeta-zero theorem にはならない。

---

# 16. Firewall

今回も以下を禁止する。

- `ZeroCutoffBaseline >= 0` の無条件 theorem
- `IndependentCorrectionSourceReal <= FixedRadialSecondMoment` の無条件 theorem
- Archimedean contribution の符号を未検証で主張すること
- Elementary contribution の符号を未検証で主張すること
- Top contribution の符号を未検証で主張すること
- `AggregateRayInteractionEnergy >= 0` の無条件 theorem
- interaction energy の cutoff monotonicity を仮定・主張すること
- interaction が baseline へ実際に到達すると主張すること
- zero-cutoff baseline を `Mass`, `Big`, `Body`, `Gap` と命名すること
- zero-cutoff baseline を prime-mirror amplitude Gap と同一視すること
- zero-cutoff baseline を cosmic coordinate gap `δ²` と同一視すること
- CompletionRemainder と zero-cutoff baseline の無条件同一視
- finite contact を pointwise polarization balance と同一視すること
- finite contact を complex source zero と同一視すること
- finite contact を zeta zero と同一視すること
- cofinal provider の導入
- `X -> infinity`
- infinite Euler product
- RH conclusion
- `Complex.arg`
- 新しい global `Complex.log` branch
- `sorry` / `admit` / `axiom` / `native_decide`

---

# 17. 成功条件

最低限、次が Green なら CFZP-006P 完了とする。

```text
1. ZeroCutoffRadialContactBaseline := RadialContactDeficit ε W 0 を定義
2. Baseline = π * (FixedMoment - IndependentCompleteSourceReal ε W 0)
3. finite normalized prime contribution at X=0 = 0
4. IndependentCompleteSourceReal ε W 0 = IndependentCorrectionSourceReal ε W
5. Baseline = π * (FixedMoment - IndependentCorrectionSourceReal)
6. correction source の Archimedean + Elementary + Top finite expansionを public 化
7. Baseline zero iff correction = fixed moment
8. Baseline nonnegative iff correction <= fixed moment
9. Baseline nonpositive iff fixed moment <= correction
10. 可能なら AggregateRayInteractionEnergy ε W 0 = 0
11. ContactSlack = 4 * (Baseline - InteractionEnergy X)
12. contact iff InteractionEnergy X = Baseline
13. named baseline による order/reach iff を記録
14. Baseline / correction / interaction の positivity を新規主張しない
15. prime-mirror/cosmic Gap と同一視しない
16. source/zeta zero / RH へ進まない
17. DkMath.RH public import
18. target module build Green
19. lake build DkMath.RH Green
20. ./lean-build.sh Green
21. ./lean-test.sh Green
22. git diff --check Green
23. 新規 module に sorry / admit / axiom / native_decide / Complex.arg / Complex.log なし
```

Gate K は optional。その他は public theorem surface が自然に届く限り実装する。

---

# 18. 次 Gate への判断材料

006P が Green なら interaction の到達先は

```text
ZeroCutoffBaseline
  = π *
      (FixedRadialSecondMoment
        - IndependentCorrectionSourceReal)
```

まで public に解剖される。

次 CFZP-006Q の第一候補は、baseline の三つの correction component

```text
NormalizedArchimedeanContribution
NormalizedElementaryContribution
NormalizedTopContribution
```

および `FixedRadialSecondMomentFunctional` の既存 sign / square / integral representation を repository 上で監査し、どこまで exact sign information が既に存在するかを整理すること。

006Q では先に既存 theorem surface を調査し、符号 theorem が無ければ新しい解析結果を仮定せず、component-wise sign frontier として固定する。

これにより次に本当に必要な新数学が

```text
baseline sign problem
```

なのか

```text
interaction reach problem
```

なのか、あるいは両方なのかを明確に切り分ける。