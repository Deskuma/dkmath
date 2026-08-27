# CFZP-0027 — CFZP-006W branch-free prime-power event sign-cell / centered-displacement audit 実装指示書

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
a92c8bae503375e8a949d168baaac06024f12d50
Add: CFZP-0026: CFZP-006V safe-frequency branch-free trigonometric phase-boundary audit
```

直前 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaSafeFrequencyTrigonometricPhaseBoundaryAudit
```

006V で safe regime

```text
0 < ε < log 2
```

の下、witnessed prime power `p^j`, `j > 0` に対し二つの周波数

```text
r+ = ε - j*log p
r- = -ε - j*log p
```

がともに strictly negative となり、one-event と finite ledger は branch-free real `exp/cos/sin` 境界式へ exact に降りた。

006V の exact finite contact ledger は

```text
AggregateInteraction_X = BranchFreeTrigLedger_X
Residual_X = Baseline - BranchFreeTrigLedger_X
RadialDeficit_X = Baseline - BranchFreeTrigLedger_X
```

であり、finite contact は

```text
BranchFreeTrigLedger_X = Baseline
```

と同値である。

今回 CFZP-006W では universal sign を証明しない。

狙いは one prime-power event をさらに

```text
positive event scale
  ×
[ F(L-ε) - F(L+ε) ]
```

という **centered finite displacement** に正規化し、remaining event sign problem を一変数 real profile の左右比較へ exact に落とすことである。

ここで

```text
L := j * log p
F(u) := negative-frequency branch-free boundary at r = -u
```

とする。

重要:

- `L-ε > 0` と `L+ε > 0` は safe regime から exact に得る。
- universal monotonicity of `F` は証明しない。
- universal event sign は証明しない。
- sign-cell sufficient conditions / exact sign adapters / explicit counterexample surfaces は実装してよい。
- contact reach existence / convergence / zeta-zero / RH は扱わない。

---

# 1. 監査済み既存 API

006V には branch-free nonzero-frequency boundary

```lean
cfzpPhasePrimitiveNonzeroBoundary
```

があり、

```text
B(a,r,T)
  = exp(a*r) *
      (T*cos(r*T)/r + (a*r - 1)*sin(r*T)/r^2)
```

を表す。

また witnessed prime power について

```lean
cfzpPrimePowerPhaseFrequencies_negative_of_epsilon_lt_log_two
```

があり、safe regime では `r+ < 0`, `r- < 0` が exact に利用できる。

one-event は

```lean
cfzpPrimePowerBranchFreeTrigEvent
```

finite ledger は

```lean
cfzpPrimePowerBranchFreeTrigLedger
```

として既に public である。

006V では event ordering 自体は未解決であり、

```lean
CfzpBranchFreeTrigBoundaryOrderingGap.noIndependentPrimePowerBranchFreeBoundaryOrderingProvider
```

が残されている。

---

# 2. 推奨 module

```text
DkMath.RH.CFBRC.CosmicFormulaZetaBranchFreePrimePowerSignCellAudit
```

推奨 path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaBranchFreePrimePowerSignCellAudit.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaSafeFrequencyTrigonometricPhaseBoundaryAudit
import Mathlib.Tactic
```

`DkMath/RH.lean` に public import を追加する。

---

# 3. Gate A — negative-frequency magnitude profile

006V の boundary を `r = -u` へ正規化する。

推奨 definition:

```lean
noncomputable def cfzpNegativeFrequencyBoundaryCore
    (a u T : ℝ) : ℝ :=
  (a * u + 1) * Real.sin (u * T) -
    u * T * Real.cos (u * T)

noncomputable def cfzpNegativeFrequencyBoundaryProfile
    (a T u : ℝ) : ℝ :=
  Real.exp (-a * u) / u ^ 2 *
    cfzpNegativeFrequencyBoundaryCore a u T
```

命名は多少調整してよい。

`hu : u ≠ 0` の下で exact に

```text
cfzpPhasePrimitiveNonzeroBoundary a (-u) T
  = cfzpNegativeFrequencyBoundaryProfile a T u
```

を証明する。

推奨 theorem 名:

```lean
cfzpPhasePrimitiveNonzeroBoundary_neg_eq_negativeFrequencyProfile
```

proof は `Real.cos_neg`, `Real.sin_neg`, field/ring normalization だけで閉じる。

この theorem は sign theorem ではない。

---

# 4. Gate B — positive prefactor と core sign classification

`hu : 0 < u` の下で

```text
0 < Real.exp (-a*u) / u^2
```

を証明し、profile の sign / zero を core へ exact に還元する。

最低限:

```text
F(u) = 0 ↔ Core(a,u,T) = 0
0 < F(u) ↔ 0 < Core(a,u,T)
F(u) < 0 ↔ Core(a,u,T) < 0
0 ≤ F(u) ↔ 0 ≤ Core(a,u,T)
F(u) ≤ 0 ↔ Core(a,u,T) ≤ 0
```

推奨 theorem family:

```lean
cfzpNegativeFrequencyBoundaryProfile_eq_zero_iff_core_eq_zero
cfzpNegativeFrequencyBoundaryProfile_pos_iff_core_pos
cfzpNegativeFrequencyBoundaryProfile_neg_iff_core_neg
cfzpNegativeFrequencyBoundaryProfile_nonneg_iff_core_nonneg
cfzpNegativeFrequencyBoundaryProfile_nonpos_iff_core_nonpos
```

`a` の符号はこの prefactor positivity には不要である。`Real.exp` は常に正。

---

# 5. Gate C — prime-power center / left-right magnitude

witnessed prime power `p^j` に対し center frequency magnitude を first-class にしてよい。

推奨:

```lean
noncomputable def cfzpPrimePowerPhaseCenter
    (p j : ℕ) : ℝ :=
  (j : ℝ) * Real.log (p : ℝ)

noncomputable def cfzpPrimePowerPhaseMagnitudeLeft
    (ε : ℝ) (p j : ℕ) : ℝ :=
  cfzpPrimePowerPhaseCenter p j - ε

noncomputable def cfzpPrimePowerPhaseMagnitudeRight
    (ε : ℝ) (p j : ℕ) : ℝ :=
  cfzpPrimePowerPhaseCenter p j + ε
```

safe regime

```text
hε : 0 < ε
hε2 : ε < Real.log 2
hp : Nat.Prime p
hj : 0 < j
```

の下で exact に

```text
0 < uLeft
uLeft < uRight
0 < uRight

r+ = -uLeft
r- = -uRight
```

を公開する。

推奨 theorem family:

```lean
cfzpPrimePowerPhaseMagnitudes_pos_of_epsilon_lt_log_two
cfzpPrimePowerPhaseMagnitude_left_lt_right
cfzpPrimePowerPhaseFrequencies_eq_neg_magnitudes
```

この部分は 006V の negative-frequency theorem の再証明ではなく、centered-displacement notation への adapter である。

---

# 6. Gate D — one-event を centered profile displacement へ exact 化

今回の中心 theorem 1。

まず event の positive scalar を必要なら first-class にする。

推奨:

```lean
noncomputable def cfzpPrimePowerEventPositiveScale
    (ε : ℝ) (p j : ℕ) : ℝ :=
  2 * Real.log (p : ℝ) *
    ((2 * ε)⁻¹ * cfzpModeCriticalScale (p ^ j))
```

safe hypotheses と `hp`, `hj` の下で

```text
0 < EventPositiveScale
```

を証明する。

次に exact に

```text
PrimePowerBranchFreeTrigEvent(ε,W,p,j)
  = EventPositiveScale(ε,p,j) *
      (
        F(a,T,L-ε) -
        F(a,T,L+ε)
      )
```

を証明する。

ここで

```text
a := cfzpModePhaseAbscissa W
T := W.rectangle.T
L := j*log p
F := cfzpNegativeFrequencyBoundaryProfile
```

である。

推奨 theorem 名:

```lean
cfzpPrimePowerBranchFreeTrigEvent_eq_positiveScale_mul_centeredProfileDifference
```

この theorem により、one-event の remaining sign problem は

```text
F(L-ε) ? F(L+ε)
```

という左右対称二点比較へ exact に局所化される。

---

# 7. Gate E — event sign / zero を centered boundary orderへ exact classification

Gate D の prefactor が strictly positive なので、safe hypotheses の下で exact に

```text
Event = 0
  ↔ F(L-ε) = F(L+ε)

0 < Event
  ↔ F(L+ε) < F(L-ε)

Event < 0
  ↔ F(L-ε) < F(L+ε)

0 ≤ Event
  ↔ F(L+ε) ≤ F(L-ε)

Event ≤ 0
  ↔ F(L-ε) ≤ F(L+ε)
```

を公開する。

推奨 theorem family:

```lean
cfzpPrimePowerBranchFreeTrigEvent_eq_zero_iff_centeredProfile_eq
cfzpPrimePowerBranchFreeTrigEvent_pos_iff_centeredProfile_gt
cfzpPrimePowerBranchFreeTrigEvent_neg_iff_centeredProfile_lt
cfzpPrimePowerBranchFreeTrigEvent_nonneg_iff_centeredProfile_ge
cfzpPrimePowerBranchFreeTrigEvent_nonpos_iff_centeredProfile_le
```

orientation を theorem 名と statement で読み違えないこと。

これは universal sign provider ではない。

---

# 8. Gate F — simple trigonometric sign cells for one boundary profile

`Core(a,u,T)` は

```text
(a*u + 1) * sin(u*T) - u*T*cos(u*T)
```

である。

ここから、追加の explicit sign assumptions の下で安全な sufficient sign-cell theorem を作ってよい。

### Cell P: `sin ≥ 0`, `cos ≤ 0`

例えば

```text
0 ≤ a
0 < u
0 ≤ T
0 ≤ sin(u*T)
cos(u*T) ≤ 0
```

なら

```text
0 ≤ Core(a,u,T)
0 ≤ F(u)
```

を証明できる。

### Cell N: `sin ≤ 0`, `cos ≥ 0`

同様に

```text
0 ≤ a
0 < u
0 ≤ T
sin(u*T) ≤ 0
0 ≤ cos(u*T)
```

なら

```text
Core(a,u,T) ≤ 0
F(u) ≤ 0
```

を証明してよい。

推奨 theorem 名:

```lean
cfzpNegativeFrequencyBoundaryProfile_nonneg_of_sin_nonneg_cos_nonpos
cfzpNegativeFrequencyBoundaryProfile_nonpos_of_sin_nonpos_cos_nonneg
```

必要なら strict version を追加してよいが、条件を無理に弱めない。

重要:

これらは **local sign cells** であり、すべての `u,T` を覆う universal sign theorem ではない。

---

# 9. Gate G — optional explicit sign-change witnesses

実装が軽ければ generic real profile に対し、`u > 0` の下で phase height を選ぶと core の符号が変わる explicit witness を記録してよい。

候補:

```text
T = π / u
```

では `u*T = π` なので

```text
Core(a,u,π/u) = π > 0
```

一方

```text
T = 2π / u
```

では `u*T = 2π` なので

```text
Core(a,u,2π/u) = -2π < 0
```

が期待される。

Mathlib の `sin_pi`, `cos_pi`, `sin_two_pi`, `cos_two_pi` 周辺 API で自然に閉じる場合のみ実装する。

推奨 theorem family:

```lean
cfzpNegativeFrequencyBoundaryCore_at_pi_div_pos
cfzpNegativeFrequencyBoundaryCore_at_two_pi_div_neg
```

これは fixed rectangle `W` の実際の `T` が任意に選べるという主張ではない。

意味は

> `a ≥ 0`, `u > 0` だけでは generic branch-free boundary の universal sign は出ない

ことを明示する local scalar audit である。

proof が不自然ならこの Gate は省略してよい。

---

# 10. Gate H — cumulative ledger へは sign を逆流させない

006W では one-event centered-displacement classification を作るが、そこから

```text
BranchFreeTrigLedger_X monotone
```

や

```text
∃ X, BranchFreeTrigLedger_X = Baseline
```

を推論してはならない。

個々の event は `p,j,W,ε` に依存し signed のままである。

必要なら frontier marker を一つ追加する。

推奨:

```lean
inductive CfzpPrimePowerBoundaryProfileMonotonicityGap : Prop
  | noIndependentSafeFrequencyBoundaryProfileMonotonicityProvider
```

この marker が次段の本質を表す。

006V の

```lean
CfzpBranchFreeTrigBoundaryOrderingGap
```

および006U の baseline reach marker は残す。

---

# 11. Dependency / firewall

006W は finite local real sign-cell audit である。

禁止:

- `Complex.arg`
- 新しい global `Complex.log` branch
- arbitrary complex-base branch analysis
- infinite Euler product
- 新規 `X → ∞` argument
- infinite sum/integral exchange
- unconditional event sign
- unconditional profile monotonicity
- unconditional branch-free boundary ordering
- cumulative ledger monotonicity
- baseline reach existence
- convergence
- zeta-zero conclusion
- RH conclusion
- `sorry`
- `admit`
- `axiom`
- `native_decide`

real `exp/cos/sin`, `Real.log`, finite prime-power support のみを使う。

---

# 12. 実装順序

推奨:

```text
1. new module / imports
2. negative-frequency boundary core/profile
3. B(a,-u,T) = profile adapter
4. positive prefactor and profile/core sign iff
5. prime-power center L and left/right magnitudes
6. safe regime under 0 < L-ε < L+ε
7. event positive scale
8. event = positive scale * [F(L-ε)-F(L+ε)]
9. event zero/sign/order iff centered profile comparison
10. optional simple sign-cell sufficient theorems
11. optional π/u, 2π/u scalar witnesses
12. frontier marker
13. DkMath/RH.lean public import
```

---

# 13. 成功条件

006W Green 条件:

1. `CosmicFormulaZetaBranchFreePrimePowerSignCellAudit.lean` を追加。
2. `DkMath/RH.lean` に public import。
3. negative-frequency boundary profile を first-class 化。
4. `u > 0` で branch-free boundary at `r=-u` と profile の exact bridge。
5. profile の sign/zero を trigonometric core の sign/zeroへ exact reduction。
6. witnessed prime power center `L=j log p` と `L-ε`, `L+ε` を公開。
7. safe regime で `0 < L-ε < L+ε` を exact に証明。
8. one-event を positive scale × centered profile difference へ exact 化。
9. event zero iff centered profile equality。
10. event positive/negative iff centered profile order を少なくとも strict 方向で公開。
11. universal profile monotonicityを主張しない。
12. universal event signを主張しない。
13. cumulative ledger monotonicityを主張しない。
14. baseline reach existence / convergence を主張しない。
15. zeta-zero / RH を主張しない。
16. target module build Green。
17. `lake build DkMath.RH` Green。
18. `./lean-build.sh` Green。
19. `./lean-test.sh` Green。
20. `git diff --check` Green。
21. new module に `sorry`, `admit`, `axiom`, `native_decide` なし。
22. new module に新規 `Complex.arg` / global `Complex.log` branch なし。

---

# 14. 006X への候補

006W が Green になった後の第一候補は

```text
CFZP-006X — negative-frequency boundary profile derivative / local monotonicity audit
```

である。

006W で one-event は

```text
F(L-ε) - F(L+ε)
```

という centered finite displacementへ落ちる。

したがって次の本質的問いは

> `F(u)` はどの `u`-interval / phase cell で増減方向を証明できるか？

となる。

006X では universal monotonicityを仮定せず、まず

```text
F'(u)
```

の exact branch-free formulaを計算し、符号を決めるために必要な追加条件を抽出する。

可能なら mean-value / monotonicity adapter により

```text
F decreasing on [L-ε, L+ε]
  → Event ≥ 0
```

などの conditional theoremへ進む。

ただし universal derivative sign、global monotonicity、reach existence はまだ禁止。

---

# 15. 006W の位置づけ

```text
006R  cutoff dynamics
006S  event support = prime powers
006T  one-event sign = phase primitive balance
006U  cumulative contact = closed-phase ledger reaches baseline
006V  safe regimeで branch-free exp/cos/sin ledger
006W  one-event = centered profile displacement F(L-ε)-F(L+ε)
```

これはユーザーの直感的な「左右二量の balance / 差し引き差分」に最も近い finite real formである。

ただし現段階では `F(L-ε)` と `F(L+ε)` の universal ordering は未証明であり、その orderingを仮定して RH 結論へ進んではならない。
