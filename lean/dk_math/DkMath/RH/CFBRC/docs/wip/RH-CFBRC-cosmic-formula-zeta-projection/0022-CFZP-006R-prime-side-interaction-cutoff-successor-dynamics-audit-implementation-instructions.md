# CFZP-0022 — CFZP-006R prime-side interaction cutoff successor dynamics audit 実装指示書

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
e5b9c0ddbd7a228bfb380598a65dfc08c8641d45
Add: CFZP-0021: CFZP-006Q zero-cutoff radial budget / correction orientation audit
```

直前 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaZeroCutoffRadialBudgetAudit
```

006Q で finite contact ledger は exact に

```text
π * FixedRadialSecondMoment
  = π * IndependentCorrectionSourceReal
    + AggregateRayInteractionEnergy(X)
```

という radial-budget balance へ整理された。

ここで重要なのは、左辺の fixed radial reference と correction source は cutoff `X` に依存しない一方、

```text
pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X
```

だけが `X` とともに動くことである。

今回 CFZP-006R では、この moving side の **finite cutoff successor dynamics** を exact に公開する。

中心式は

```text
I_{X+1}
  = I_X + 2 * Λ(X+1) * K_{X+1}
```

である。

ここで

```text
I_X := AggregateRayInteractionEnergy ε W X
K_n := pascalCenteredXiPrimeSideFiniteModeKernel ε W n
Λ(n) := ArithmeticFunction.vonMangoldt n
```

と略記する。

この式から radial contact / radial-budget residual は逆向きに

```text
Residual_{X+1}
  = Residual_X - 2 * Λ(X+1) * K_{X+1}
```

と更新される。

重要:

- successor law 自体は `hε : 0 < ε` だけで閉じることを優先する。
- 006Q の巨大な top/Mellin integrability hypotheses を dynamics の基礎 theorem に持ち込まない。
- increment は signed。正とも負とも仮定しない。
- monotonicity / reach / zeta-zero / RH は今回証明しない。

---

# 1. 現行 source で確認済みの exact API

Module:

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit
```

Public theorem:

```lean
pascalCenteredXiPrimeSideAggregateRayInteractionEnergy_eq_two_modeSum
```

内容:

```text
AggregateRayInteractionEnergy ε W X
  = 2 * Σ n in range (X + 1),
      (vonMangoldt n : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W n
```

ここで `pascalCenteredXiPrimeSideFiniteModeKernel ε W n` は cutoff `X` を引数に持たない。

したがって `Finset.sum_range_succ` により `X → X+1` の追加項は exact に `n = X+1` の一項だけになる。

同 module の public theorem:

```lean
pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_zeroCutoff_deficit_sub_interaction
```

内容:

```text
G_X = G_0 - I_X
```

も successor dynamics に利用できる。

006P public theorem:

```lean
cfzpZeroCutoffRadialContactBaseline_eq_pi_mul_fixedMoment_sub_correctionSource
```

006Q public theorem:

```lean
cfzpIntegratedPolarizedContactSlack_eq_four_mul_radialBudgetResidual
```

がある。

ただし最後の ContactSlack theorem は top/Mellin integrability hypotheses を必要とするため、低依存 successor theorem と分離して扱う。

---

# 2. 推奨 module

```text
DkMath.RH.CFBRC.CosmicFormulaZetaInteractionCutoffDynamicsAudit
```

推奨 path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaInteractionCutoffDynamicsAudit.lean
```

最低限 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaZeroCutoffRadialBudgetAudit
import Mathlib.Tactic
```

`DkMath/RH.lean` に public import を追加する。

---

# 3. Gate A — signed interaction increment の命名

新しい一項更新量を first-class にする。

推奨:

```lean
noncomputable def cfzpPrimeSideInteractionCutoffIncrement
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (n : ℕ) : ℝ :=
  2 * (ArithmeticFunction.vonMangoldt n : ℝ) *
    pascalCenteredXiPrimeSideFiniteModeKernel ε W n
```

これは signed quantity。

禁止命名:

```text
PositiveIncrement
InteractionMassIncrement
InteractionGapIncrement
```

など positivity を暗示する名前。

単純 fold theorem は必要なら置いてよい。

---

# 4. Gate B — aggregate interaction の exact finite-sum fold

既存 `two_modeSum` theorem を `InteractionCutoffIncrement` notation へ fold して、可能なら public theorem として

```text
I_X
  = Σ n in range (X + 1), InteractionIncrement(n)
```

を置く。

推奨 theorem 名:

```lean
cfzpAggregateRayInteractionEnergy_eq_sum_cutoffIncrement
```

これは既存 theorem の normalization layer であり、新しい数学ではない。

`hε : 0 < ε` だけを要求する。

---

# 5. Gate C — interaction successor law

今回の最重要 theorem 1。

`hε : 0 < ε` の下で exact に

```text
AggregateRayInteractionEnergy ε W (X + 1)
  = AggregateRayInteractionEnergy ε W X
    + cfzpPrimeSideInteractionCutoffIncrement ε W (X + 1)
```

を証明する。

推奨 theorem 名:

```lean
cfzpAggregateRayInteractionEnergy_succ
```

差分形も安価なら置く。

```text
I_{X+1} - I_X = InteractionIncrement(X+1)
```

推奨:

```lean
cfzpAggregateRayInteractionEnergy_succ_sub
```

Proof 方針:

```text
1. X+1 と X の two_modeSum / sum_cutoffIncrement theorem を rewrite
2. Finset.sum_range_succ
3. Nat arithmetic を simp
4. ring
```

indexing を最優先で audit する。

`I_X` は `range (X+1)` なので追加 index は **`X+1`**。`X` ではない。

---

# 6. Gate D — zero-cutoff base point

006P にはすでに

```lean
cfzpAggregateRayInteractionEnergy_zeroCutoff
```

があり、

```text
I_0 = 0
```

を与える。

必要なら今回の sum notation と整合する corollary を置いてよいが、同じ theorem の複製は不要。

この base point と Gate C により finite interaction は完全な successor recursion を持つ。

---

# 7. Gate E — first-class radial-budget residual

006Q は residual の式を theorem 内に直接書いた。

今回、cutoff dynamics を扱うためだけに first-class alias を一つ追加してよい。

推奨:

```lean
noncomputable def cfzpRadialBudgetResidual
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
    (Real.pi * pascalCenteredXiPrimeSideIndependentCorrectionSourceReal ε W +
      pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X)
```

これは signed residual。

`Mass`, `Gap`, `PositiveResidual` と呼ばない。

---

# 8. Gate F — residual = radial contact deficit

今回の重要な低依存 bridge。

`hε : 0 < ε` の下で exact に

```text
cfzpRadialBudgetResidual ε W X
  = pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X
```

を証明する。

推奨 theorem 名:

```lean
cfzpRadialBudgetResidual_eq_radialContactDeficit
```

Proof の安全な経路:

```text
Baseline
  = π * (FixedRadialSecondMoment - CorrectionSource)

G_X
  = G_0 - Interaction_X

G_0 = Baseline
```

を使い、ring / linarith で閉じる。

巨大な CFZP top-edge hypotheses は不要。

この theorem は 006Q の budget residual が単なる記号上の差ではなく、既存 radial contact deficit と exact に同じ signed quantityであることを public API にする。

---

# 9. Gate G — radial contact / residual successor law

今回の最重要 theorem 2。

Gate C と Gate F から exact に

```text
cfzpRadialBudgetResidual ε W (X + 1)
  = cfzpRadialBudgetResidual ε W X
    - cfzpPrimeSideInteractionCutoffIncrement ε W (X + 1)
```

を証明する。

推奨 theorem 名:

```lean
cfzpRadialBudgetResidual_succ
```

さらに existing radial deficit 自身についても、安価なら public theorem を置く。

```text
RadialContactDeficit(ε,W,X+1)
  = RadialContactDeficit(ε,W,X)
    - InteractionIncrement(ε,W,X+1)
```

推奨 theorem 名:

```lean
cfzpRadialContactDeficit_succ
```

こちらも `hε` だけで閉じる。

---

# 10. Gate H — von Mangoldt zero による no-update theorem

prime-power support の exact Mathlib theorem 名を推測しない。

まず確実な API として、仮定

```text
hΛ : (ArithmeticFunction.vonMangoldt (X + 1) : ℝ) = 0
```

の下で

```text
InteractionIncrement(X+1) = 0
I_{X+1} = I_X
Residual_{X+1} = Residual_X
RadialContactDeficit_{X+1} = RadialContactDeficit_X
```

を証明する。

推奨 theorem family:

```lean
cfzpPrimeSideInteractionCutoffIncrement_eq_zero_of_vonMangoldt_eq_zero
cfzpAggregateRayInteractionEnergy_succ_eq_of_vonMangoldt_eq_zero
cfzpRadialBudgetResidual_succ_eq_of_vonMangoldt_eq_zero
cfzpRadialContactDeficit_succ_eq_of_vonMangoldt_eq_zero
```

この時点で exact に言える意味は

> von Mangoldt coefficient が zero の cutoff step は moving interaction ledger を更新しない

まで。

「したがって素数冪以外では更新しない」と Lean theorem として言うには、`vonMangoldt = 0` と prime-power support を結ぶ現行 public theorem を確認する必要がある。

---

# 11. Gate I — optional prime-power sparsity bridge

これは **optional**。

現行 pinned Mathlib / DkMath に public theorem が実在し、無理な再証明なしで

```text
vonMangoldt n ≠ 0 → n is a positive prime power
```

または同等の support classification が得られる場合だけ、InteractionIncrement の support を prime-power step へ bridge してよい。

実在 theorem が見つからなければ Gate H の `vonMangoldt = 0` no-update API で止める。

禁止:

- theorem 名を推測する
- von Mangoldt の定義を大規模に再構成する
- この module のためだけに prime-power arithmetic library を作り直す

---

# 12. Gate J — nonzero update support containment

prime-power theorem が無くても安価に証明できるなら、次を置いてよい。

```text
InteractionIncrement(n) ≠ 0
  → (ArithmeticFunction.vonMangoldt n : ℝ) ≠ 0
```

推奨 theorem 名:

```lean
cfzpPrimeSideInteractionCutoffIncrement_ne_zero_implies_vonMangoldt_ne_zero
```

これは support containment であり、prime-power classification そのものではない。

さらに

```text
InteractionIncrement(n) ≠ 0
  → pascalCenteredXiPrimeSideFiniteModeKernel ε W n ≠ 0
```

も安価なら可。

---

# 13. Gate K — ContactSlack fold は heavy hypotheses と分離

006Q の theorem

```lean
cfzpIntegratedPolarizedContactSlack_eq_four_mul_radialBudgetResidual
```

は既に exact に

```text
ContactSlack_X = 4 * RadialBudgetResidual_X
```

を与えている。

今回、successor law の基礎 theorem に 006Q の巨大 hypotheses を再導入しない。

もし ContactSlack の successor theorem を追加するなら **optional** とし、`X` と `X+1` の双方に必要な integrability hypotheses を正直に供給すること。

その場合 exact coefficient は

```text
ContactSlack_{X+1}
  = ContactSlack_X
    - 4 * InteractionIncrement(X+1)
```

すなわち increment の展開後は

```text
ContactSlack_{X+1}
  = ContactSlack_X
    - 8 * Λ(X+1) * K_{X+1}
```

となる。

仮定管理が煩雑なら実装しなくてよい。006R の本質は low-dependency interaction/residual dynamics にある。

---

# 14. Dynamics が示すもの / 示さないもの

006R が Green になると finite ledger は exact に

```text
I_0 = 0
I_{X+1} = I_X + ΔI_{X+1}

Residual_0 = ZeroCutoffBaseline
Residual_{X+1} = Residual_X - ΔI_{X+1}

ΔI_n = 2 * Λ(n) * K_n
```

となる。

したがって moving side は von-Mangoldt-weighted finite mode increments で駆動される。

しかし `K_n` の符号は未証明なので、以下はまだ言えない。

```text
I_X is monotone
Residual_X is monotone
I_X approaches the baseline
Residual_X approaches zero
```

今回これらを絶対に導かない。

---

# 15. Frontier markers

推奨:

```lean
inductive CfzpInteractionCutoffIncrementSignGap : Prop
  | noIndependentFiniteModeKernelSignProvider
```

```lean
inductive CfzpInteractionCutoffReachDynamicsGap : Prop
  | noIndependentSuccessorDynamicsToBaselineReachProvider
```

prime-power support theorem が見つからず optional Gate I を実装しない場合のみ、必要なら

```lean
inductive CfzpInteractionIncrementPrimePowerSupportBridgeGap : Prop
  | noPrimePowerSupportClassificationExposedHere
```

を置いてよい。

既存

```text
noIndependentCofinalInteractionReachProvider
```

を解決したと主張しない。

---

# 16. Firewall

今回も以下を禁止する。

- `InteractionIncrement >= 0` の無条件 theorem
- `FiniteModeKernel >= 0` の無条件 theorem
- `AggregateRayInteractionEnergy >= 0` の無条件 theorem
- interaction monotonicity
- residual monotonicity
- baseline reach の無条件 theorem
- cofinal reach provider の捏造
- `X → ∞`
- infinite Euler product
- successor recurrence から convergence を推論すること
- `ContactSlack = 0` がある cutoff で必ず起こると主張すること
- finite contact → pointwise balance
- finite contact → complex source zero
- finite contact → zeta zero
- finite contact → RH
- residual / increment を prime-mirror Gap または cosmic `δ²` と同一視すること
- `Complex.arg`
- 新しい global `Complex.log`
- `sorry` / `admit` / `axiom` / `native_decide`

---

# 17. 成功条件

最低限、次が Green なら CFZP-006R 完了とする。

```text
1. signed InteractionCutoffIncrement を定義
2. I_X を increment finite sum として fold
3. I_{X+1} = I_X + Increment(X+1)
4. indexing が X+1 で正しい
5. signed RadialBudgetResidual を first-class 化
6. RadialBudgetResidual = RadialContactDeficit を hε のみで証明
7. Residual_{X+1} = Residual_X - Increment(X+1)
8. 可能なら RadialContactDeficit 自身の同じ successor law
9. vonMangoldt(X+1)=0 → increment zero
10. vonMangoldt zero step → interaction/residual/deficit unchanged
11. optional prime-power support は実在 API がある場合だけ
12. increment/kernel の sign を仮定しない
13. monotonicity/reach/convergence を主張しない
14. 006Q radial-budget meaning を保持
15. DkMath.RH public import
16. target module build Green
17. lake build DkMath.RH Green
18. ./lean-build.sh Green
19. ./lean-test.sh Green
20. git diff --check Green
21. 新規 module に sorry/admit/axiom/native_decide/Complex.arg/Complex.log なし
```

---

# 18. 次 Gate への判断材料

006R が Green なら、finite dynamics の未知部分は一項 kernel

```text
K_n := pascalCenteredXiPrimeSideFiniteModeKernel ε W n
```

へ局在化する。

次 CFZP-006S の第一候補は、既存 CS25 / CS26 の prime-power ray / explicit phase API を監査し、

```text
2 * Λ(n) * K_n
```

の sign / oscillation / prime-power support がどこまで exact に読めるかを調べること。

特に重要なのは、successor recurrence が得られただけでは baseline reach は証明されない点。

次段階では

```text
「更新がどこで起きるか」
```

と

```text
「更新がどちら向きにどれだけ動くか」
```

を分離して audit する。
