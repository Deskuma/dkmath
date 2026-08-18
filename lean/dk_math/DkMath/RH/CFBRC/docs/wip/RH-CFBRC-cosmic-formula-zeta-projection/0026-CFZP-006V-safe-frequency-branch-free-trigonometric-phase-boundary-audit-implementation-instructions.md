# CFZP-0026 — CFZP-006V safe-frequency branch-free trigonometric phase-boundary audit 実装指示書

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
97562c142416d74046a30e509ddbe25f21c62597
Add: CFZP-0025: CFZP-006U prime-power closed-phase contact ledger audit
```

直前 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerClosedPhaseContactLedgerAudit
```

006U で finite interaction / radial contact は exact に

```text
Interaction_X = ClosedPhaseLedger_X
Residual_X = Baseline - ClosedPhaseLedger_X
RadialDeficit_X = Baseline - ClosedPhaseLedger_X
```

まで戻った。

さらに

```text
RadialDeficit_X = 0
  ↔ ClosedPhaseLedger_X = Baseline
```

であり、reach existence 自体は未証明である。

006T / CS26 では各 prime-power event の kernel が二つの phase primitive の差へ還元され、CS26 には nonzero-frequency closed form

```text
PhasePrimitive(a,r,T)
  = exp(a*r) *
      (T*cos(r*T)/r + (a*r-1)*sin(r*T)/r^2)
```

が既に存在する。ただし generic closed form は `r = 0` branch を持つ。

今回 CFZP-006V では safe-frequency regime

```text
0 < ε
ε < log 2
```

の下で、すべての prime-power event の `r+`, `r-` が非零であることを exact に確認し、006U の closed-phase ledger を **branch-free real trigonometric boundary ledger** へ落とす。

目的は sign を証明することではない。

---

# 1. 監査済み既存 API

## 1.1 006T phase coordinates

既存:

```lean
cfzpModePhaseAbscissa
cfzpModePhaseFrequencyPlus
cfzpModePhaseFrequencyMinus
cfzpModeCriticalScale
cfzpModeCriticalScale_pos
cfzpModePhaseFrequencyPlus_eq_of_eq_prime_pow
cfzpModePhaseFrequencyMinus_eq_of_eq_prime_pow
cfzpModePhaseFrequencyMinus_neg_of_prime_pow
cfzpModePhaseFrequencyPlus_eq_zero_iff_of_prime_pow
```

prime power `p^j`, `j>0` では

```text
r+ = ε - j*log p
r- = -ε - j*log p
```

である。

## 1.2 CS26 nonzero-frequency primitive

`PascalCenteredXiPrimeSideInteractionPhaseBoundaryAudit` には public に

```lean
pascalCenteredXiPrimeSidePhasePrimitive_nonzero_frequency
```

があり、`hr : r ≠ 0` の下で

```text
PhasePrimitive(a,r,T)
  = exp(a*r) *
      (T*cos(r*T)/r + (a*r-1)*sin(r*T)/r^2)
```

を exact に与える。

さらに generic wrapper

```lean
pascalCenteredXiPrimeSidePhasePrimitiveClosedForm
pascalCenteredXiPrimeSidePhasePrimitive_eq_closedForm
```

もある。

## 1.3 CS26 safe-frequency certificate

既存:

```lean
pascalCenteredXiPrimeSide_phase_frequencies_safe_cutoff
```

は

```text
0 < ε
ε < log 2
2 ≤ n
```

から

```text
ε < log n
r+(n) ≠ 0
r-(n) ≠ 0
```

を与える。

006V では可能な限りこれを再利用する。

---

# 2. 推奨 module

```text
DkMath.RH.CFBRC.CosmicFormulaZetaSafeFrequencyTrigonometricPhaseBoundaryAudit
```

推奨 path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaSafeFrequencyTrigonometricPhaseBoundaryAudit.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerClosedPhaseContactLedgerAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideInteractionPhaseBoundaryAudit
import Mathlib.Tactic
```

`DkMath/RH.lean` に public import を追加する。

---

# 3. Gate A — branch-free real phase boundary value を first-class 化

006V 用に、`if r = 0` を含まない real scalar boundary value を定義する。

推奨:

```lean
noncomputable def cfzpPhasePrimitiveNonzeroBoundary
    (a r T : ℝ) : ℝ :=
  Real.exp (a * r) *
    (T * Real.cos (r * T) / r +
      (a * r - 1) * Real.sin (r * T) / r ^ 2)
```

その上で

```lean
cfzpPhasePrimitive_eq_nonzeroBoundary
```

を public にする。

目標:

```text
r ≠ 0
  → PhasePrimitive(a,r,T)
      = cfzpPhasePrimitiveNonzeroBoundary(a,r,T)
```

proof は既存

```lean
pascalCenteredXiPrimeSidePhasePrimitive_nonzero_frequency
```

の薄い adapter だけでよい。

新しい積分計算をしない。

---

# 4. Gate B — prime-power safe-frequency certificate

`hε : 0 < ε`, `hε2 : ε < Real.log 2`, `hp : Nat.Prime p`, `hj : 0 < j` の下で

```text
r+(p^j) ≠ 0
r-(p^j) ≠ 0
```

を CFZP-facing theorem として公開する。

推奨 theorem:

```lean
cfzpPrimePowerPhaseFrequencies_nonzero_of_epsilon_lt_log_two
```

できれば stronger に

```text
r+(p^j) < 0
r-(p^j) < 0
```

まで exact に出してよい。

理由:

```text
p ≥ 2
j ≥ 1
log 2 ≤ log p ≤ j*log p
ε < log 2
```

なので

```text
ε - j*log p < 0
-ε - j*log p < 0
```

となる。

ただし proof が既存 API だけで軽く閉じる範囲にする。符号 theorem を新しい大きな解析へ発展させない。

重要:

ここで得るのは **frequency の符号** であって phase primitive / kernel / event の符号ではない。

---

# 5. Gate C — witnessed prime-power event の branch-free trig formula

006U の

```lean
cfzpPrimePowerClosedPhaseEvent
```

を safe regime で branch-free boundary difference に rewrite する。

推奨 theorem:

```lean
cfzpPrimePowerClosedPhaseEvent_eq_branchFreeTrigBoundaryDifference
```

目標構造:

```text
Event(p,j)
  = 2 * log p *
      ((2*ε)^(-1) * CriticalScale(p^j) *
        (B(a,r+,T) - B(a,r-,T)))
```

ここで

```text
a := cfzpModePhaseAbscissa W
r+ := ε - j*log p
r- := -ε - j*log p
T := W.rectangle.T
B := cfzpPhasePrimitiveNonzeroBoundary
```

である。

proof route:

```text
1. cfzpPrimePowerClosedPhaseEvent を unfold
2. Gate B で r+, r- 非零を取得
3. pascalCenteredXiPrimeSidePhasePrimitiveClosedForm の if branch を消す
   または PhasePrimitive 経由で Gate A を使う
4. ring / simp で exact formula を閉じる
```

今回の本質は branch elimination であり、式を不必要に再展開しすぎない。

---

# 6. Gate D — pair-support branch-free event ledger

safe-frequency event を pair-support 上で再総和する。

推奨 definition:

```lean
noncomputable def cfzpPrimePowerBranchFreeTrigLedger
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  ∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
    <branch-free event using pk.1 and pk.2 + 1>
```

指数規約は必ず

```text
pk.2 + 1
```

とする。

次を exact に証明する。

```lean
cfzpPrimePowerClosedPhaseLedger_eq_branchFreeTrigLedger
```

hypotheses:

```text
hε : 0 < ε
hε2 : ε < Real.log 2
```

のみを global safe assumptions とする。

pair support membership から base prime と positive exponent を既存 API で回収する。

---

# 7. Gate E — aggregate interaction / residual / contact deficit の branch-free form

Gate D と006Uを接続し、最低限次を public にする。

```text
AggregateInteraction_X = BranchFreeTrigLedger_X
Residual_X = Baseline - BranchFreeTrigLedger_X
RadialDeficit_X = Baseline - BranchFreeTrigLedger_X
```

推奨 theorem family:

```lean
cfzpAggregateRayInteractionEnergy_eq_branchFreeTrigLedger
cfzpRadialBudgetResidual_eq_zeroCutoffBaseline_sub_branchFreeTrigLedger
cfzpRadialContactDeficit_eq_zeroCutoffBaseline_sub_branchFreeTrigLedger
```

heavy rectangle / top-edge hypothesesをここへ追加しない。

---

# 8. Gate F — exact balance/order classification を explicit trig ledger へ移す

006U の equality/order classification を branch-free trig ledger へ rewrite する。

最低限:

```text
RadialDeficit_X = 0
  ↔ BranchFreeTrigLedger_X = Baseline
```

さらに安価なら

```text
0 ≤ RadialDeficit_X
  ↔ BranchFreeTrigLedger_X ≤ Baseline

RadialDeficit_X ≤ 0
  ↔ Baseline ≤ BranchFreeTrigLedger_X
```

を公開する。

これは sign provider ではない。

remaining problem は explicit に

```text
finite sum of real exp/cos/sin boundary values
  versus
zero-cutoff baseline
```

の equality/order problemになる。

---

# 9. Gate G — optional one-event sign adapter

branch-free event formulaから、positive prefactor を剥がして one-event sign を

```text
B(a,r+,T) - B(a,r-,T)
```

の sign へ還元する theorem を追加してよい。

例:

```lean
cfzpPrimePowerClosedPhaseEvent_pos_iff_branchFreeBoundary_lt
cfzpPrimePowerClosedPhaseEvent_neg_iff_branchFreeBoundary_gt
cfzpPrimePowerClosedPhaseEvent_eq_zero_iff_branchFreeBoundary_eq
```

ただしこれは **conditional sign reduction** であり universal ordering theorem ではない。

proof が長くなるなら 006W へ送ってよい。

---

# 10. Exceptional zero-frequency surface との関係

006T で

```text
r+(p^j) = 0 ↔ ε = j*log p
```

を得ている。

safe regime

```text
0 < ε < log 2
```

では prime `p ≥ 2`, `j ≥ 1` より

```text
j*log p ≥ log 2 > ε
```

なので exceptional surface は pair-support 上で発生しない。

006V ではこの意味を doc comment / theorem として明示してよい。

ただし generic CS26 の zero-frequency branch を削除しない。006V の safe regime で不要になるだけである。

---

# 11. 今回閉じる frontier / 残す frontier

## 11.1 今回閉じるもの

safe regime `0 < ε < log 2` の下で、prime-power event と cumulative ledger の `r=0` branch ambiguity を閉じる。

006V Green 後は contact condition を

```text
finite branch-free exp/cos/sin prime-power ledger
  = zero-cutoff baseline
```

へ exact に書ける。

## 11.2 必ず残すもの

以下は未解決:

- branch-free boundary value の universal ordering
- one-event の universal sign
- kernel の universal sign
- cumulative ledger monotonicity
- cumulative ledger boundedness / one-sidedness
- finite baseline reach existence
- cofinal reach
- convergence
- new `X → ∞` argument
- correction source sign
- top-horizontal matching
- zeta-zero conclusion
- RH conclusion

006U marker

```lean
CfzpPrimePowerClosedPhaseBaselineReachGap
```

および006T marker

```lean
CfzpPrimePowerPhasePrimitiveOrderingGap
```

は残す。

必要なら006Vで

```lean
inductive CfzpBranchFreeTrigBoundaryOrderingGap : Prop
  | noIndependentPrimePowerBranchFreeBoundaryOrderingProvider
```

を一つだけ追加してよい。

---

# 12. Dependency / firewall

禁止:

- `Complex.arg`
- 新しい global `Complex.log` branch
- arbitrary complex-base branch analysis
- infinite Euler product
- 新規 `X → ∞` argument
- infinite sum/integral exchange
- unconditional event sign
- unconditional kernel sign
- unconditional boundary ordering
- monotonicity
- baseline reach existence
- zeta-zero conclusion
- RH conclusion
- `sorry`
- `admit`
- `axiom`
- `native_decide`

今回使う phase formula は real `exp/cos/sin`, `Real.log` と既存 positive natural-base transportに限定する。

---

# 13. 実装順序

推奨:

```text
1. new module / imports
2. branch-free nonzero-frequency boundary definition
3. PhasePrimitive = boundary adapter under r ≠ 0
4. prime-power safe-frequency certificate
5. one prime-power event branch-free formula
6. pair-support branch-free ledger definition
7. ClosedPhaseLedger = BranchFreeTrigLedger
8. AggregateInteraction = BranchFreeTrigLedger
9. Residual / RadialDeficit branch-free identities
10. zero/order classification
11. optional one-event sign adapter
12. frontier marker
13. DkMath/RH.lean public import
```

---

# 14. 成功条件

006V Green 条件:

1. `CosmicFormulaZetaSafeFrequencyTrigonometricPhaseBoundaryAudit.lean` を追加。
2. `DkMath/RH.lean` に public import。
3. branch-free real phase boundary valueを first-class 定義。
4. `r ≠ 0` で PhasePrimitive と branch-free boundary が一致。
5. `0 < ε < log 2` と witnessed prime powerから `r+ ≠ 0`, `r- ≠ 0` を exact に得る。
6. 可能なら `r+ < 0`, `r- < 0` も公開。
7. witnessed prime-power event を branch-free exp/cos/sin formulaへ exact 展開。
8. pair-support ledger の指数は `pk.2 + 1`。
9. ClosedPhaseLedger = BranchFreeTrigLedger を exact に証明。
10. AggregateInteraction = BranchFreeTrigLedger を exact に証明。
11. Residual = Baseline - BranchFreeTrigLedger を exact に証明。
12. RadialDeficit = Baseline - BranchFreeTrigLedger を exact に証明。
13. contact zero iff BranchFreeTrigLedger = Baseline を公開。
14. universal sign / ordering を主張しない。
15. monotonicity / reach existence / convergence を主張しない。
16. zeta-zero / RH を主張しない。
17. target module build Green。
18. `lake build DkMath.RH` Green。
19. `./lean-build.sh` Green。
20. `./lean-test.sh` Green。
21. `git diff --check` Green。
22. new module に `sorry`, `admit`, `axiom`, `native_decide` なし。
23. new module に新規 `Complex.arg` / global `Complex.log` branch なし。

---

# 15. 006W への候補

006V が Green になった後の第一候補は

```text
CFZP-006W — branch-free prime-power event sign-cell / boundary-order audit
```

である。

006V で remaining local sign problem は完全に real scalar な

```text
B(a,r+,T) ? B(a,r-,T)
```

へ落ちる。

006W では、既存の rectangle constraints

```text
a = σ - 1/2 > 0
T > 0
r+ < 0
r- < 0
```

の下で、どの追加条件なら one-event sign / order が証明可能かを監査する。

重要: 006W でも最初から universal ordering を仮定しない。まず exact sign-cell decomposition、counterexample surface、または必要十分条件の抽出を優先する。

---

# 16. 006V の位置づけ

```text
006R  cutoff dynamics
006S  event support = prime powers
006T  one-event sign = phase primitive balance
006U  cumulative contact = closed-phase ledger reaches baseline
006V  safe regime で closed phase を branch-free exp/cos/sin ledgerへ展開
```

006V は証明の sign provider ではない。

役割は、remaining contact problem を branch / opaque integral のない有限 real trigonometric scalar ledger として固定することにある。
