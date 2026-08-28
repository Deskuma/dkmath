# CFZP-0025 — CFZP-006U prime-power closed-phase contact ledger audit 実装指示書

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
78804a6444f227b3dbc2e5bd4658ae15a731fa1c
Add: CFZP-0024: CFZP-006T prime-power mode-kernel phase-balance audit
```

直前 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaInteractionModeKernelPhaseBalanceAudit
```

006T で一つの prime-power event は exact に

```text
ΔI(p^k)
  = 2 * log(p) * K(p^k)

K(p^k)
  = positive_scale(p^k) * (P+(p^k) - P-(p^k))
```

まで分離された。

さらに

```text
ΔI(p^k) = 0  ↔  P+(p^k) = P-(p^k)
ΔI(p^k) > 0  ↔  P-(p^k) < P+(p^k)
ΔI(p^k) < 0  ↔  P+(p^k) < P-(p^k)
```

という local phase-balance classification も Green である。

今回 CFZP-006U では、local event を finite prime-power support 上で再総和し、

```text
aggregate interaction
  = finite sum of prime-power closed-phase events

radial residual
  = zero-cutoff baseline - finite prime-power closed-phase ledger
```

という cumulative contact ledger を first-class API として公開する。

今回の目的は **reach を証明することではない**。

目的は reach problem を

```text
finite signed prime-power phase ledger
  reaches
zero-cutoff contact baseline
```

という一つの exact equality / order problemへ落とすことである。

---

# 1. 006T 監査結果と今回利用する既存 API

## 1.1 006T local phase reduction

新 module

```text
CosmicFormulaZetaInteractionModeKernelPhaseBalanceAudit
```

には少なくとも次が存在する。

```lean
cfzpPrimeSideInteractionCutoffIncrement_eq_zero_iff_modeKernel_eq_zero_of_isPrimePow
cfzpPrimeSideInteractionCutoffIncrement_pos_iff_modeKernel_pos_of_isPrimePow
cfzpPrimeSideInteractionCutoffIncrement_neg_iff_modeKernel_neg_of_isPrimePow

cfzpPrimeSideFiniteModeKernel_eq_scaled_phasePrimitiveDifference
cfzpPrimeSideFiniteModeKernel_eq_zero_iff_phasePrimitive_eq
cfzpPrimeSideFiniteModeKernel_pos_iff_phasePrimitive_lt
cfzpPrimeSideFiniteModeKernel_neg_iff_phasePrimitive_gt

cfzpPrimePowerInteractionIncrement_eq_zero_iff_phasePrimitive_eq
cfzpPrimePowerInteractionIncrement_pos_iff_phasePrimitive_lt
cfzpPrimePowerInteractionIncrement_neg_iff_phasePrimitive_gt
```

また prime-power frequencies は

```text
r+(p^k) = ε - k log p
r-(p^k) = -ε - k log p
```

で、`r-` は `ε>0` の下で常に負、`r+=0` は exact に

```text
ε = k log p
```

という exceptional surface である。

## 1.2 CS26 closed phase boundary

`PascalCenteredXiPrimeSideInteractionPhaseBoundaryAudit` には既に public に

```lean
pascalCenteredXiPrimeSidePhasePrimitive_nonzero_frequency
pascalCenteredXiPrimeSidePhasePrimitiveClosedForm
pascalCenteredXiPrimeSidePhasePrimitive_eq_closedForm
pascalCenteredXiPrimeSideFiniteModeKernel_eq_closedPhaseBoundary_difference
pascalCenteredXiPrimeSideFiniteClosedPhaseModeTerm
pascalCenteredXiPrimeSideFiniteClosedPhaseModeTerm_eq_kernel
pascalCenteredXiPrimeSideAggregateInteraction_eq_closedPhaseLedger
```

がある。

特に closed form は

```text
ClosedPhase(a,r,T)
  = if r = 0 then a*T
    else exp(a*r) *
      (T*cos(r*T)/r + (a*r-1)*sin(r*T)/r^2)
```

である。

したがって 006U で新しい積分計算をやり直さない。

## 1.3 CS14 canonical prime-power pair support

`PascalCenteredXiPrimeSidePrimePowerRayAudit` には

```lean
pascalCenteredXiPrimeSideFiniteModeSum_eq_canonicalPrimePowerSupport
pascalCenteredXiPrimeSideCanonicalModeSum_eq_pairSupport
pascalPrimePowerPairSupportUpTo
mem_pascalPrimePowerPairSupportUpTo_iff
mem_pascalPrimeCoordinateSupportUpTo_iff
```

がある。

これを使えば自然数 cutoff の von-Mangoldt mode sum を

```text
(base prime p, positive exponent j)
```

の有限 pair supportへ exact に reindex できる。

独自の prime-power enumeration を新設しない。

## 1.4 zero-cutoff baseline と contact ledger

006P / 006R には

```lean
cfzpZeroCutoffRadialContactBaseline
cfzpZeroCutoffRadialContactBaseline_eq_pi_mul_fixedMoment_sub_correctionSource
cfzpRadialBudgetResidual_eq_radialContactDeficit
cfzpAggregateRayInteractionEnergy_succ
```

および本質的に

```text
G_X = G_0 - I_X
```

という finite interaction cancellation がある。

006P には heavy completed-zeta hypotheses の下で

```lean
cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_interaction_reaches_zeroCutoffBaseline
```

も存在する。

006U ではまず heavy hypotheses を使わない radial residual / deficit ledger を正本にする。
completed-zeta contact-threshold bridge は後段 optional とする。

---

# 2. 推奨 module

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerClosedPhaseContactLedgerAudit
```

推奨 path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaPrimePowerClosedPhaseContactLedgerAudit.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaInteractionModeKernelPhaseBalanceAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSidePrimePowerRayAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideInteractionPhaseBoundaryAudit
import Mathlib.Tactic
```

必要なら 006P / 006R が transitive に見えることを確認し、明示 import を追加してよい。

`DkMath/RH.lean` に public import を追加する。

---

# 3. Gate A — one prime-power closed-phase event を first-class 化

positive exponent `j>0` を持つ witnessed prime power `p^j` に対して、closed phase form を使った local event を定義する。

推奨形:

```lean
noncomputable def cfzpPrimePowerClosedPhaseEvent
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  2 * Real.log (p : ℝ) *
    ((2 * ε)⁻¹ * cfzpModeCriticalScale (p ^ j) *
      (pascalCenteredXiPrimeSidePhasePrimitiveClosedForm
          (cfzpModePhaseAbscissa W)
          (ε - (j : ℝ) * Real.log (p : ℝ))
          W.rectangle.T -
        pascalCenteredXiPrimeSidePhasePrimitiveClosedForm
          (cfzpModePhaseAbscissa W)
          (-ε - (j : ℝ) * Real.log (p : ℝ))
          W.rectangle.T))
```

名前は調整可。

これは signed event である。

`Mass`, `Gap`, `PositiveEvent` 等の名前を付けない。

次に

```text
hp : Nat.Prime p
hj : 0 < j
hε : 0 < ε
```

の下で exact に

```text
cfzpPrimePowerClosedPhaseEvent ε W p j
  = cfzpPrimeSideInteractionCutoffIncrement ε W (p^j)
```

を証明する。

推奨 theorem 名:

```lean
cfzpPrimePowerClosedPhaseEvent_eq_interactionIncrement
```

proof route は 006S/006T と CS26 closed-form theorem の rewrite だけにする。

新しい解析計算を入れない。

---

# 4. Gate B — pair-support cumulative closed-phase ledger

CS14 の zero-based pair support では exponent coordinate が `k`、実際の positive exponent は `k+1` である。

この convention を維持して累積 ledger を定義する。

推奨:

```lean
noncomputable def cfzpPrimePowerClosedPhaseLedger
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  ∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
    cfzpPrimePowerClosedPhaseEvent ε W pk.1 (pk.2 + 1)
```

重要:

- exponent を `pk.2` のまま使わない。
- 必ず `pk.2 + 1`。
- support の再実装は禁止。

---

# 5. Gate C — aggregate interaction = cumulative prime-power phase ledger

今回の中心 theorem 1。

`hε : 0 < ε` のみを基本 hypothesis として

```text
pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X
  = cfzpPrimePowerClosedPhaseLedger ε W X
```

を exact に証明する。

推奨 theorem 名:

```lean
cfzpAggregateRayInteractionEnergy_eq_primePowerClosedPhaseLedger
```

推奨 proof route:

```text
1. CS25
   AggregateInteraction
     = 2 * Σ_{n≤X} Λ(n) K(n)

2. CS14
   Σ_{n≤X} Λ(n) K(n)
     = Σ_{(p,k) in pairSupport} log(p) * K(p^(k+1))

3. Gate A
   2 * log(p) * K(p^(k+1))
     = PrimePowerClosedPhaseEvent(p,k+1)

4. Finset.sum_congr / ring
```

factor `2` の置き忘れに注意する。

これにより 006T の local phase balance が global finite interaction ledgerへ exact に戻る。

---

# 6. Gate D — residual / radial deficit の cumulative closed-phase form

今回の中心 theorem 2。

006R / 006P から

```text
Residual_X = Baseline - Interaction_X
```

を得て Gate C を代入する。

まず

```lean
cfzpRadialBudgetResidual_eq_zeroCutoffBaseline_sub_primePowerClosedPhaseLedger
```

を推奨する。

目標:

```text
cfzpRadialBudgetResidual ε W X
  = cfzpZeroCutoffRadialContactBaseline ε W
    - cfzpPrimePowerClosedPhaseLedger ε W X
```

必要 hypothesis は `hε : 0 < ε` のみ。

続いて

```lean
cfzpRadialContactDeficit_eq_zeroCutoffBaseline_sub_primePowerClosedPhaseLedger
```

を公開する。

目標:

```text
pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X
  = cfzpZeroCutoffRadialContactBaseline ε W
    - cfzpPrimePowerClosedPhaseLedger ε W X
```

これは

```lean
cfzpRadialBudgetResidual_eq_radialContactDeficit
```

と上の residual theorem だけでよい。

---

# 7. Gate E — finite contact / order を ledger reach へ exact classification

Gate D の正の係数すら不要な単純差分なので、exact に次を公開する。

```text
Residual_X = 0
  ↔ ClosedPhaseLedger_X = Baseline

G_X = 0
  ↔ ClosedPhaseLedger_X = Baseline

0 ≤ Residual_X
  ↔ ClosedPhaseLedger_X ≤ Baseline

Residual_X ≤ 0
  ↔ Baseline ≤ ClosedPhaseLedger_X
```

同様に radial contact deficit 側の order theorem も安価なら追加してよい。

推奨 theorem family:

```lean
cfzpRadialBudgetResidual_eq_zero_iff_primePowerClosedPhaseLedger_reaches_baseline
cfzpRadialContactDeficit_eq_zero_iff_primePowerClosedPhaseLedger_reaches_baseline
cfzpRadialBudgetResidual_nonneg_iff_primePowerClosedPhaseLedger_le_baseline
cfzpRadialBudgetResidual_nonpos_iff_baseline_le_primePowerClosedPhaseLedger
```

ここで `reaches` は theorem 名の equality semantics に限定される。

**存在 quantifier を導入して「ある X で reach する」とは主張しない。**

---

# 8. Gate F — completed-zeta contact threshold への optional bridge

既存 006P heavy hypotheses をそのまま受け取る section を設けてもよい。

既存 theorem

```lean
cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_interaction_reaches_zeroCutoffBaseline
```

と Gate C を接続し、

```text
IntegratedPolarizedImbalance_X = ContactThreshold_X
  ↔ PrimePowerClosedPhaseLedger_X = Baseline
```

を exact に公開してよい。

推奨 theorem 名:

```lean
cfzpIntegratedPolarizedImbalance_eq_contactThreshold_iff_primePowerClosedPhaseLedger_reaches_baseline
```

ただし heavy top/Mellin integrability hypotheses を Gate C–E に逆流させない。

この theorem は optional だが、既存 hypotheses の再利用だけで自然に閉じるなら実装価値が高い。

---

# 9. Gate G — safe-frequency regime の lightweight certificate

006T で

```text
r-(p^j) < 0
r+(p^j) = 0 ↔ ε = j log p
```

まで得ている。

さらに CS26 には

```lean
pascalCenteredXiPrimeSide_phase_frequencies_safe_cutoff
```

がある。

`hε2 : ε < Real.log 2` を仮定すると、すべての prime-power event `p^j`, `j>0` で

```text
r+(p^j) ≠ 0
r-(p^j) ≠ 0
```

となることを CFZP-facing に薄く公開してよい。

推奨 theorem 名:

```lean
cfzpPrimePowerPhaseFrequencies_nonzero_of_epsilon_lt_log_two
```

または pair-support 上の version:

```lean
cfzpPrimePowerPairSupport_phaseFrequencies_nonzero
```

これは次段で `PhasePrimitiveClosedForm` の `if r=0` branch を消すための certificate である。

006U では branch-free trigonometric expansion まで必須にしない。

---

# 10. Gate H — zero-frequency exceptional event は別 ledger として記録可能

もし実装が軽いなら witnessed prime power `p^j` で

```text
ε = j log p
```

を仮定し、

```text
r+ = 0
r- = -2ε
```

を exact に出してよい。

この場合 plus primitive は既存 zero-frequency theorem から

```text
P+ = a * T
```

へ落ちる。

ただしこれは exceptional local formula であり、符号 provider ではない。

実装が重くなるなら 006V へ送る。

---

# 11. 今回閉じる frontier / 残す frontier

## 11.1 今回閉じるもの

006R 以降の local dynamics を finite cumulative phase ledger へ戻す。

006U Green 後は exact に

```text
I_X = ClosedPhaseLedger_X
G_X = Baseline - ClosedPhaseLedger_X
```

となる。

したがって finite contact condition は

```text
ClosedPhaseLedger_X = Baseline
```

という一つの equality へ集約される。

## 11.2 必ず残すもの

以下は未解決:

- individual event の universal sign
- phase primitive の universal ordering
- cumulative ledger monotonicity
- cumulative ledger の boundedness / one-sidedness
- `∃ X, ClosedPhaseLedger_X = Baseline`
- cofinal / eventual baseline reach
- convergence of the cumulative ledger
- `X → ∞` を用いた新しい主張
- correction source positivity
- top-horizontal correction matching
- finite contact から pointwise source zero への短絡
- finite contact から zeta zero への短絡
- RH conclusion

推奨 frontier marker:

```lean
inductive CfzpPrimePowerClosedPhaseBaselineReachGap : Prop
  | noIndependentFiniteOrCofinalClosedPhaseLedgerReachProvider
```

006T の

```lean
CfzpPrimePowerPhasePrimitiveOrderingGap
```

は残す。

---

# 12. Dependency / firewall

006U は finite cumulative ledger layer である。

禁止:

- `Complex.arg`
- 新しい global `Complex.log` branch
- arbitrary complex-base branch analysis
- infinite Euler product
- 新規 `X → ∞` argument
- infinite sum / integral exchange
- unconditional event sign
- unconditional kernel sign
- unconditional primitive ordering
- unconditional aggregate interaction monotonicity
- unconditional residual monotonicity
- baseline reach existence
- zeta-zero conclusion
- RH conclusion
- `sorry`
- `admit`
- `axiom`
- `native_decide`

また

```text
ClosedPhaseLedger
```

を nonnegative mass / energy / Gap と呼ばない。

これは signed cumulative interaction ledger である。

---

# 13. 実装順序

推奨:

```text
1. new module / imports
2. one prime-power closed-phase event definition
3. local event = InteractionIncrement
4. cumulative pair-support closed-phase ledger definition
5. AggregateInteraction = ClosedPhaseLedger
6. Residual = Baseline - ClosedPhaseLedger
7. RadialDeficit = Baseline - ClosedPhaseLedger
8. zero/order classification
9. optional completed-zeta contact-threshold bridge
10. optional safe-frequency certificate
11. frontier marker
12. DkMath/RH.lean public import
```

---

# 14. 成功条件

006U Green 条件:

1. `CosmicFormulaZetaPrimePowerClosedPhaseContactLedgerAudit.lean` を追加。
2. `DkMath/RH.lean` に public import。
3. one prime-power closed-phase event を first-class 定義。
4. witnessed `p^j`, `j>0` で closed-phase event = interaction increment。
5. `pascalPrimePowerPairSupportUpTo X` を使う cumulative ledger を定義。
6. exponent convention は必ず `pk.2 + 1`。
7. Aggregate interaction = cumulative closed-phase ledger を exact に証明。
8. Residual = baseline - closed-phase ledger を exact に証明。
9. Radial contact deficit = baseline - closed-phase ledger を exact に証明。
10. residual zero iff closed-phase ledger = baseline。
11. radial deficit zero iff closed-phase ledger = baseline。
12. 少なくとも residual の two-sided order classification を公開。
13. optional heavy contact-threshold bridge は既存 hypotheses をそのまま再利用。
14. local/cumulative sign を無条件で主張しない。
15. monotonicity を主張しない。
16. reach existence を主張しない。
17. convergence を主張しない。
18. zeta-zero / RH を主張しない。
19. target module build Green。
20. `lake build DkMath.RH` Green。
21. `./lean-build.sh` Green。
22. `./lean-test.sh` Green。
23. `git diff --check` Green。
24. new module に `sorry`, `admit`, `axiom`, `native_decide` なし。
25. new module に新規 `Complex.arg` / global `Complex.log` branch なし。

---

# 15. 006V への候補

006U が Green になった後の第一候補は

```text
CFZP-006V — safe-frequency branch-free trigonometric phase-boundary audit
```

である。

006U により global reach problem は

```text
ClosedPhaseLedger_X = Baseline
```

へ落ちる。

次に `ε < log 2` の safe regime で各 prime-power event の `r+`, `r-` がともに非零であることを使い、

```text
PhasePrimitiveClosedForm(a,r,T)
```

の `if r=0` branch を消して

```text
exp(a*r) *
  (T*cos(r*T)/r + (a*r-1)*sin(r*T)/r^2)
```

という branch-free real trigonometric boundary valueへ exact に落とす。

006V の目的は sign を決めることではなく、remaining ordering problem を完全に explicit real scalar inequality へ変換すること。

---

# 16. 006U の位置づけ

006R:

```text
cutoff successor dynamics
```

006S:

```text
nonzero event support = prime-power ∩ nonzero kernel
```

006T:

```text
one prime-power event direction
  = two phase primitives の balance
```

006U:

```text
all finite prime-power events を再総和
  ↓
closed-phase cumulative interaction ledger
  ↓
radial contact deficit
  = baseline - cumulative ledger
```

ここまで Green になれば、CFZP finite contact problem は

```text
local arithmetic support
local phase direction
cumulative signed transport
baseline reach
```

の四層へ完全に分離される。

006U はそのうち local から cumulative への exact bridge を担当する。
