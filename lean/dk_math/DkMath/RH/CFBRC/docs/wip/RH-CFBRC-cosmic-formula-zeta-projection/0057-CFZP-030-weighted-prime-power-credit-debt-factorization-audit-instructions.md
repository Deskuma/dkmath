# CFZP-0057 / CFZP-030

## weighted prime-power credit/debt factorization audit — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-024: finite certified Good-credit / Bad-debt dominance
- CFZP-025: quantitative phase-core margin -> Good derivative margin / Good credit
- CFZP-027: subcritical large-cell readiness -> ready Good hit -> finite certificate
- CFZP-028: irrational fixed-prime AddCircle rotation -> cofinal ready Good hits (conditional)
- CFZP-029: universal automatic Bad derivative/event/pulse/debt envelope; certificate constructor without per-Bad `K / henvelope`

CFZP-029 により、有限 block の両側がついに explicit になった。

Good 側は

```text
2 * log p * CriticalScale(p^j) * κ_good
```

Bad 側は

```text
2 * log p * CriticalScale(p^j) * K_bad
```

という同じ arithmetic carrier を持つ。

本段の目的は、この共通 carrier を first-class に切り出し、Good credit と Bad debt envelope を同じ正規形に置き、CFZP-024 dominance を **一個の finite net balance** に書き換えることである。

新しい抽象 provider wrapper を増やしてはいけない。
CFZP-030 は「存在」を仮定する段ではなく、現在すでに存在する finite quantities の exact factorization / comparison layer を作る段である。

---

## 1. 新規 module

作成候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaWeightedPrimePowerCreditDebtFactorizationAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaWeightedPrimePowerCreditDebtFactorizationAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaUniversalPrimePowerBadDebtEnvelopeAudit
import Mathlib.Tactic
```

---

## 2. Gate A — common critical carrier

Good/Bad 双方に共通する factor を定義する。

推奨 shape:

```lean
noncomputable def cfzp030PrimePowerCriticalCarrier
    (p j : ℕ) : ℝ :=
  2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j)
```

prime-power assumptions

```text
Nat.Prime p
0 < j
```

の下で

```text
0 < cfzp030PrimePowerCriticalCarrier p j
```

を証明する。

必要なら nonnegative 版も公開してよい。

この carrier は CFZP-023/024/025/029 に散在している

```text
2 * Real.log (p : ℝ) * cfzpModeCriticalScale (p ^ j)
```

の canonical name とする。

---

## 3. Gate B — critical scale の prime-power exponent 正規形

既存定義は

```text
cfzpModeCriticalScale n = exp (-(1/2) * log n)
```

である。

prime `p` と exponent `j` について、Mathlib の `log_pow` 系 API を使い、exact に

```text
cfzpModeCriticalScale (p ^ j)
  = Real.exp (-(j : ℝ) / 2 * Real.log (p : ℝ))
```

または Lean で最も扱いやすい algebraically equivalent formを証明する。

さらに carrier を

```text
cfzp030PrimePowerCriticalCarrier p j
  = 2 * Real.log (p : ℝ) *
      Real.exp (-(j : ℝ) / 2 * Real.log (p : ℝ))
```

へ rewrite する theorem を公開する。

重要:

- asymptotic notation は導入しない。
- convergence / divergence は言わない。
- `p^(-j/2)` への Real.rpow rewrite は、既存 API で綺麗に閉じる場合のみ追加してよい。主 theorem は exp/log 形で十分。

---

## 4. Gate C — Good local credit の carrier factorization

CFZP-025/027 の ready-hit spine が作る Good side quantityを、

```text
carrier * normalizedGoodShape
```

の形にする。

まず最小限の generic version として、

```lean
noncomputable def cfzp030GoodLocalCredit
    (p j : ℕ) (κ : ℝ) : ℝ :=
  cfzp030PrimePowerCriticalCarrier p j * κ
```

を定義し、CFZP-024 の Good summand と exact equality を持たせる。

その上で、CFZP-025 の synthesized margin

```text
κ = centeredDerivativePrefactorFloor * phaseCoreMargin
```

へ接続できる named theorem を追加する。

さらに CFZP-027 ready hit から得る explicit phase-core marginが theorem surface に既にあるなら、それを使って

```text
ready Good credit
  = carrier
      * (centeredDerivativePrefactorFloor * readyPhaseCoreMargin)
```

という exact factorization を公開する。

実装上、027 の exact margin expression を取り出すために theorem 名が長くなりすぎる場合は、first-class normalized Good shape を追加してよい。

推奨概念形:

```lean
noncomputable def cfzp030ReadyGoodShape ... : ℝ :=
  cfzp025CenteredDerivativePrefactorFloor ... *
    <explicit CFZP-026/027 phase-core margin>
```

ただし **新しい仮定を追加して shape を作ってはいけない**。027 が既に持つ ready-hit data から定義・証明する。

---

## 5. Gate D — Bad local envelope の carrier factorization

CFZP-029 の automatic Bad bound を同じ正規形にする。

推奨 normalized Bad shape:

```lean
noncomputable def cfzp030BadLocalShape
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  cfzp029CenteredProfileDerivativeAbsBound ε W p j
```

そして exact に

```text
cfzp029PrimePowerBadDebtEnvelope ε W p j
  = cfzp030PrimePowerCriticalCarrier p j *
      cfzp030BadLocalShape ε W p j
```

を証明する。

ここは unfold/rfl で閉じる可能性が高い。

safe prime-power assumptions の下で shape / local envelope の nonnegativity も公開する。

---

## 6. Gate E — prefactor floor / ceiling sanity comparison

同一 centered interval について CFZP-025 の Good prefactor floor と CFZP-029 の Bad prefactor ceiling を比較する。

safe prime-power assumptions の下で、可能なら

```text
cfzp025CenteredDerivativePrefactorFloor ε W p j
  ≤ cfzp029CenteredDerivativePrefactorCeiling ε W p j
```

を証明する。

推奨 route:

- CFZP-025 floor theoremを interval 内の適切な point に適用するか、
- left < right と `a>0` から endpoint formulaを直接比較する。

これが閉じれば、局所 Good/Bad の差は「carrier の差」ではなく、主に phase-core margin と universal core envelope の差であることを theorem-level で明示できる。

この Gate が API ergonomics 上非常に重い場合は補助 theorem に留めてもよいが、可能な限り CLOSED を狙う。

---

## 7. Gate F — finite automatic net balance

029 により Bad envelope は external `K` なしで explicit finite sumになった。
これを Good certified credit と引き合わせる first-class finite net balance を定義する。

推奨:

```lean
noncomputable def cfzp030CertifiedNetBalance
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ}
    (cert : Cfzp024FiniteBlockCertificate ε W A B) : ℝ :=
  cfzp024CertifiedGoodCredit cert.Good cert.κ -
    cfzp029AutomaticBadDebtEnvelope ε W
      (cfzp024BadPrimePowerPairBlockSupport A B cert.Good)
```

ただし generic `cert` の `cert.K` は automatic 029 bound と一致するとは限らない。
したがって **net balance 自体は automatic Bad sum を使う**一方、CFZP-024 dominance への exact bridge は次 Gate で 029 constructor が生成した certificate、または automatic-envelope equality を持つ certificate に限定する。

必要なら ready-hit input dataを bundle する lightweight structureを作ってもよいが、新しい provider Prop は作らない。

---

## 8. Gate G — finite Good/Bad sum factorization

本段の主要 endpoint の一つ。

029 constructor へ渡す ready-hit Good dataに対して、finite net balance を explicit sums として露出する。

概念形:

```text
NetBalance
  = Σ pk ∈ Good,
      [CriticalCarrier(pk) * GoodShape(pk)]
    - Σ pk ∈ Bad,
      [CriticalCarrier(pk) * BadShape(pk)]
```

ここで

```text
Bad = blockSupport A B \ Good
```

である。

Good 側は 025/027 の actual synthesized κ を使う。
Bad 側は 029 automatic shape を使う。

重要:

- 旧 `cert.K` の abstract sumを endpoint に残さない。
- Good/Bad 双方が同じ `cfzp030PrimePowerCriticalCarrier` を通る表示にする。
- theorem statement が多少長くなっても、この exact identity を first-class にする価値が高い。

---

## 9. Gate H — dominance を net balance へ書き換える

CFZP-024 の核心 inequality

```text
G_A + BadEnvelope ≤ GoodCredit + η
```

を

```text
G_A ≤ NetBalance + η
```

へ exact に書き換える。

まず pure algebra theorem:

```lean
G_A + Bad ≤ Good + η ↔
  G_A ≤ (Good - Bad) + η
```

を実 quantities に specializeしてよい。

その上で 029 automatic certificate / ready-hit dataについて

```text
pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W A
  ≤ cfzp030CertifiedNetBalance ... + η
```

から

```text
pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W B ≤ η
```

を導く theoremを作る。

証明は CFZP-024 の

```text
cfzp024CertifiedBlockDominance_radialContactDeficit_le
```

を再利用すること。
pulse telescope を再証明しない。

可能なら equivalence と implication の両方を API 化する。

---

## 10. Gate I — axis diagnostics without asymptotic claims

ここで exact formula から「どの方向を次に攻めるべきか」を判断できる primitive facts を用意する。

固定 prime `p` では carrier が exponent `j` に対して

```text
2*log p * exp(-(j/2)*log p)
```

となることを記録する。

一方 `j = 1` では

```text
2*log p * exp(-(1/2)*log p)
```

となる。

これらの specialization theorem を追加してよい。

ただし以下は本段では禁止:

- fixed-prime Good credit tail の収束証明
- prime-axis weighted sum の発散/収束証明
- PNT / Mertens / Chebyshev を使った global mass claim
- density hit と weighted credit の自動結合

また、現時点の source 監査では

```text
a = cfzpModePhaseAbscissa W = W.rectangle.σ - 1/2
```

について positivity は使えるが、`a < 1/2` のような一般上界は確認できていない。
**`σ < 1` や `a < 1/2` を勝手に仮定・導出しないこと。**
必要なら future checkpoint の explicit hypothesis として扱う。

---

## 11. Firewall / Gap

証明してはいけないもの:

- cofinal Good hits -> weighted Good dominance
- fixed-prime hit existence -> sufficient total credit
- automatic Bad envelope -> Bad total is small
- prime-axis weighted sum の無条件 dominance
- arbitrary window subcriticality
- arbitrary prime/window rotation irrationality
- CFZP-024 cofinal certified dominance provider
- CFZP-018 unconditional provider
- infinite sum / joint limit / limit exchange
- RH

Gap marker 例:

```lean
inductive Cfzp030WeightedPrimePowerCreditDebtFactorizationGap : Prop
  | noIndependentWeightedFiniteBalanceProvider
  | noPrimeAxisWeightedMassProvider
  | noAutomaticSubcriticalWindowProvider
  | noIndependentPrimePhaseRotationIrrationalityProvider
```

---

## 12. roadmap / public import

- `DkMath/RH.lean` に新 module を追加。
- `0000-CFZP-roadmap.md` に CFZP-030 section を追加。

Green 条件:

```text
common critical carrier and positivity: CLOSED
prime-power critical-scale exponent factorization: CLOSED
Good local carrier factorization: CLOSED
Bad local carrier factorization: CLOSED
Good prefactor floor <= Bad prefactor ceiling sanity: CLOSED if feasible
finite automatic net balance: CLOSED
explicit finite Good/Bad weighted-sum identity: CLOSED
CFZP-024 dominance rewrite through net balance: CLOSED
independent weighted finite-balance provider: OPEN / GAP
prime-axis weighted mass provider: OPEN / GAP
```

---

## 13. 実装姿勢

CFZP-030 は「あと一個 provider を定義する」段ではない。

029 までで local analytic data は揃った。
ここから必要なのは、その local dataを arithmetic weightごとに整列させ、有限 block の収支を一つの quantity に圧縮することである。

最優先 spine:

```text
             2 log p * CriticalScale(p^j)
                  /                 \
                 /                   \
      Good normalized shape      Bad normalized shape
               |                       |
         Good local credit        Bad local envelope
                 \                   /
                  \                 /
                   finite weighted sums
                          ↓
                      NetBalance
                          ↓
             G_A ≤ NetBalance + η
                          ↓
                      G_B ≤ η
```

ここまで閉じれば、次段の敵は完全に一つになる。

```text
Can the explicit weighted Good sum dominate
start deficit + explicit weighted Bad sum?
```

その判定を fixed-prime exponent 軸で行うのか、prime 軸で行うのか、あるいは両者を組み合わせるのかを、CFZP-030 の exact normal form を基準に決める。