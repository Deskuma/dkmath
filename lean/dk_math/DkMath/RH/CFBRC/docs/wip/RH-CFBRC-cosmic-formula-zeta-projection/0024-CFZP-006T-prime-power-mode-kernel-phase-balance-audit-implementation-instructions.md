# CFZP-0024 — CFZP-006T prime-power mode-kernel phase-balance audit 実装指示書

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
74abcda5cddab1feda546e1edc6c61bc656aace3
Add: CFZP-0023: CFZP-006S von Mangoldt prime-power event classification audit
```

直前 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaInteractionPrimePowerEventAudit
```

006S で finite cutoff event は exact に

```text
ΔI(n) ≠ 0
  ↔ IsPrimePow n ∧ K(n) ≠ 0

n = p^k,  k > 0
  → ΔI(n) = 2 * log p * K(n)
```

まで分離された。

ここで

```text
K(n) := pascalCenteredXiPrimeSideFiniteModeKernel ε W n
```

である。

したがって prime-power event 上で arithmetic coefficient `2 * log p` は strictly positive であり、更新方向に残る未解決量は `K(p^k)` の符号だけである。

今回 CFZP-006T では、この kernel を既存 CS13 phase API へ exact に降ろし、

```text
mode-kernel sign problem
  ↓
two real phase primitives の balance problem
```

として公開する。

重要:

- kernel の unconditional sign は証明しない。
- prime power だから kernel 非零、とは言わない。
- prime power だから increment 正、とは言わない。
- `Complex.arg` は使わない。
- 新しい global `Complex.log` branch は導入しない。
- 使う対数は正の自然数に対する既存 `Real.log` / positive-base `Complex.cpow` API に限定する。
- 今回は有限 window / 有限 mode の exact phase ledger だけを扱う。

---

# 1. 監査済み既存 API

## 1.1 CS12 finite mode kernel

`PascalCenteredXiPrimeSideFiniteTailProjectionAudit` には exact に

```lean
noncomputable def pascalCenteredXiPrimeSideFiniteModeIntegrand
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (n : ℕ) (t : ℝ) : ℝ :=
  if n = 0 then 0 else
    Complex.re
      ((pascalCenteredXiMellinSecondDifferenceWeight ε 0
          (pascalOrdinaryToCentered
            (pascalSymmetricRectangleRightEdge W.rectangle.σ t))) *
        ((n : ℂ) ^
          (-(pascalSymmetricRectangleRightEdge W.rectangle.σ t))))

noncomputable def pascalCenteredXiPrimeSideFiniteModeKernel
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (n : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..W.rectangle.T,
    pascalCenteredXiPrimeSideFiniteModeIntegrand ε W n t
```

がある。

kernel は既に real signed integral であり、符号は未証明である。

## 1.2 CS13 centered phase node

`PascalCenteredXiPrimeSideModeKernelPhaseAudit` には

```lean
pascalCenteredXiPrimeSideModePhaseNode W t
```

と exact affine form

```text
z(t) = a + i t

a := W.rectangle.σ - 1/2
```

がある。

既存 theorem:

```lean
pascalCenteredXiPrimeSideModePhaseNode_eq_affine
```

を利用する。

## 1.3 CS13 boundary phase kernel

positive natural mode では既に

```lean
pascalCenteredXiPrimeSideFiniteModeKernel_eq_boundaryPhaseKernel
```

があり、

```text
K(n) = BoundaryPhaseKernel(n)
```

へ exact に移せる。

さらに既存 theorem

```lean
pascalCenteredXiPrimeSideModePhaseTransport
```

は一つの positive natural mode を

```text
critical-line scale
  × centered node
  × [exp((ε-log n)z) - exp((-ε-log n)z)]
```

へ branch-free に展開する。

## 1.4 CS13 real phase primitive

既存 theorem:

```lean
real_part_affine_exp_phase
```

は

```text
Re((a+i t) * exp(r(a+i t)))
  = exp(a r) * (a cos(r t) - t sin(r t))
```

を exact に与える。

さらに

```lean
pascalCenteredXiPrimeSidePhasePrimitive a r T
```

は

```text
∫ t in 0..T,
  exp(a r) * (a cos(r t) - t sin(r t))
```

であり、zero-frequency theorem

```lean
pascalCenteredXiPrimeSidePhasePrimitive_zero_frequency
```

も既にある。

CS13 の

```lean
PascalCenteredXiPrimeSideModePhaseClosedFormGap
  | nonzeroFrequencyClosedFormPending
```

は nonzero-frequency closed form が未実装であることを明示する。

006T ではこの marker を削除する必要はない。今回の必須目標は primitive 差への exact reduction であり、非零周波数の閉形式そのものは optional とする。

---

# 2. 推奨 module

```text
DkMath.RH.CFBRC.CosmicFormulaZetaInteractionModeKernelPhaseBalanceAudit
```

推奨 path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaInteractionModeKernelPhaseBalanceAudit.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaInteractionPrimePowerEventAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideModeKernelPhaseAudit
import Mathlib.Tactic
```

必要な API が transitive import で既に見える場合でも、006T の数学的依存を明示するため CS13 import を残してよい。

`DkMath/RH.lean` に public import を追加する。

---

# 3. Gate A — prime-power event の increment sign を kernel sign へ exact reduction

006S では optional だった sign reduction を 006T の入口として public にする。

`hPP : IsPrimePow n` の下では

```text
0 < 2 * Λ(n)
```

なので exact に

```text
0 < ΔI(n) ↔ 0 < K(n)
ΔI(n) < 0 ↔ K(n) < 0
0 ≤ ΔI(n) ↔ 0 ≤ K(n)
ΔI(n) ≤ 0 ↔ K(n) ≤ 0
ΔI(n) = 0 ↔ K(n) = 0
```

を証明してよい。

推奨 theorem family:

```lean
cfzpPrimeSideInteractionCutoffIncrement_pos_iff_modeKernel_pos_of_isPrimePow
cfzpPrimeSideInteractionCutoffIncrement_neg_iff_modeKernel_neg_of_isPrimePow
cfzpPrimeSideInteractionCutoffIncrement_nonneg_iff_modeKernel_nonneg_of_isPrimePow
cfzpPrimeSideInteractionCutoffIncrement_nonpos_iff_modeKernel_nonpos_of_isPrimePow
cfzpPrimeSideInteractionCutoffIncrement_eq_zero_iff_modeKernel_eq_zero_of_isPrimePow
```

proof は `ArithmeticFunction.vonMangoldt_pos_iff` と positive scalar multiplication だけで閉じる。

これは sign provider ではない。

意味は

```text
prime-power event 上の update direction problem
  ↔ mode-kernel sign problem
```

への exact reduction だけである。

---

# 4. Gate B — phase 座標と二つの周波数を CFZP-facing に命名

以下の lightweight helper を new module に置いてよい。

```lean
noncomputable def cfzpModePhaseAbscissa
    (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  W.rectangle.σ - (1 / 2 : ℝ)

noncomputable def cfzpModePhaseFrequencyPlus
    (ε : ℝ) (n : ℕ) : ℝ :=
  ε - Real.log (n : ℝ)

noncomputable def cfzpModePhaseFrequencyMinus
    (ε : ℝ) (n : ℕ) : ℝ :=
  -ε - Real.log (n : ℝ)
```

名前は調整可。

重要なのは

```text
a = σ - 1/2
r+(n) = ε - log n
r-(n) = -ε - log n
```

という二周波数構造を public ledger にすること。

`n=0` は phase reduction の対象にしない。以降 `hn : 0 < n` を要求する。

---

# 5. Gate C — positive critical-line scale を明示

`pascalCenteredXiPrimeSideModePhaseTransport` には

```text
(n : ℂ)^(-(1/2))
```

が real positive scale として現れる。

006T では必要なら real helper を一つ定義する。

推奨:

```lean
noncomputable def cfzpModeCriticalScale (n : ℕ) : ℝ :=
  Real.exp (-(1 / 2 : ℝ) * Real.log (n : ℝ))
```

`hn : 0 < n` の下で

```text
0 < cfzpModeCriticalScale n
```

を証明する。

さらに実装上自然なら

```text
((n : ℂ) ^ (-(1 / 2 : ℂ)))
```

と real-cast `cfzpModeCriticalScale n` の exact bridge を証明してよい。

この bridge は positive natural base に限定する。

新しい arbitrary-complex-base `Complex.log` branch を作らない。

もしこの bridge が theorem-name 探索で不自然なら、Gate D では既存 `pascalCenteredXiPrimeSideModePhaseTransport` の complex scalarを局所的に扱い、最終 real factor の positivity が必要な Gate E までに最小 bridge を作る。

---

# 6. Gate D — finite mode integrand を二周波数 real phase density へ exact 展開

今回の中心 local identity。

`hn : 0 < n` の下で、

```text
a := σ - 1/2
r+ := ε - log n
r- := -ε - log n
c_n := exp(-(1/2) log n)
```

と置く。

目標構造は

```text
FiniteModeIntegrand(ε,W,n,t)
  = (2ε)^(-1) * c_n *
      [
        exp(a r+) * (a cos(r+ t) - t sin(r+ t))
        -
        exp(a r-) * (a cos(r- t) - t sin(r- t))
      ]
```

である。

推奨 theorem 名:

```lean
cfzpPrimeSideFiniteModeIntegrand_eq_phaseDensityDifference
```

proof route:

```text
1. n ≠ 0 で FiniteModeIntegrand の if を除去
2. centered right-edge node を affine form a + i t へ rewrite
3. pascalCenteredXiPrimeSideModePhaseTransport を利用
4. exp の二項差を real part の差へ分配
5. real_part_affine_exp_phase を r+, r- に適用
6. real critical-line scaleを外へ出す
```

同じ内容を既存 `FiniteModeBoundaryPhaseIntegrand` から始めてもよい。

この Gate は finite pointwise identity であり sign claim ではない。

---

# 7. Gate E — kernel を二つの PhasePrimitive の差へ exact reduction

Gate D を interval integral へ持ち上げる。

目標:

```text
K(n)
  = (2ε)^(-1) * c_n *
      (
        PhasePrimitive(a, r+(n), T)
        - PhasePrimitive(a, r-(n), T)
      )
```

ただし

```text
a = W.rectangle.σ - 1/2
T = W.rectangle.T
```

である。

推奨 theorem 名:

```lean
cfzpPrimeSideFiniteModeKernel_eq_scaled_phasePrimitiveDifference
```

必要 hypotheses:

```text
hε : 0 < ε
hn : 0 < n
```

を基本とする。

proof は interval integral の linearity と Gate D から構成する。

既存

```lean
pascalCenteredXiPrimeSideFiniteModeKernel_eq_boundaryPhaseKernel
```

を入口に使ってよい。

ここで得たい本質は

```text
K(n) の signed mystery
  ↓
P+(n) - P-(n)
```

という exact 二項 balance である。

---

# 8. Gate F — kernel sign / zero を phase primitive order / equality へ分類

Gate E の prefactor は

```text
(2ε)^(-1) * c_n > 0
```

である。

したがって `hε : 0 < ε`, `hn : 0 < n` の下で exact に

```text
K(n) = 0
  ↔ PhasePrimitive(a,r+,T) = PhasePrimitive(a,r-,T)

0 < K(n)
  ↔ PhasePrimitive(a,r-,T) < PhasePrimitive(a,r+,T)

K(n) < 0
  ↔ PhasePrimitive(a,r+,T) < PhasePrimitive(a,r-,T)

0 ≤ K(n)
  ↔ PhasePrimitive(a,r-,T) ≤ PhasePrimitive(a,r+,T)

K(n) ≤ 0
  ↔ PhasePrimitive(a,r+,T) ≤ PhasePrimitive(a,r-,T)
```

を public にする。

推奨 theorem family:

```lean
cfzpPrimeSideFiniteModeKernel_eq_zero_iff_phasePrimitive_eq
cfzpPrimeSideFiniteModeKernel_pos_iff_phasePrimitive_lt
cfzpPrimeSideFiniteModeKernel_neg_iff_phasePrimitive_gt
cfzpPrimeSideFiniteModeKernel_nonneg_iff_phasePrimitive_le
cfzpPrimeSideFiniteModeKernel_nonpos_iff_phasePrimitive_ge
```

命名は orientation が読み違えにくい形へ調整してよい。

特に equality theorem は 006T の主成果の一つ。

これは

> kernel vanishing は二つの real phase primitive の一致

という exact balance condition である。

ただし両 primitive は非負量とは限らない。`Mass`, `Big`, `Body`, `Gap` と命名してはならない。

---

# 9. Gate G — prime-power specialization

witnessed prime power

```text
hp : Nat.Prime p
hk : 0 < k
hn : n = p ^ k
```

では既存

```lean
real_log_prime_pow_eq_mul
```

または同等 public API を用いて

```text
log n = k * log p
```

へ展開する。

したがって二周波数を exact に

```text
r+(p^k) = ε - k log p
r-(p^k) = -ε - k log p
```

へ落とす。

推奨 theorem family:

```lean
cfzpModePhaseFrequencyPlus_eq_of_eq_prime_pow
cfzpModePhaseFrequencyMinus_eq_of_eq_prime_pow
cfzpPrimeSideFiniteModeKernel_eq_scaled_primePowerPhasePrimitiveDifference
```

最後の theorem は Gate E の prime-power-facing specialization である。

さらに Gate A + Gate F を合成し、prime-power event の increment sign を phase primitive balance へ直接接続してよい。

例:

```text
0 < ΔI(p^k)
  ↔ P-(p^k) < P+(p^k)

ΔI(p^k) = 0
  ↔ P+(p^k) = P-(p^k)
```

推奨 theorem 名:

```lean
cfzpPrimePowerInteractionIncrement_eq_zero_iff_phasePrimitive_eq
cfzpPrimePowerInteractionIncrement_pos_iff_phasePrimitive_lt
cfzpPrimePowerInteractionIncrement_neg_iff_phasePrimitive_gt
```

ただし theorem の引数は witnessed equality `X+1 = p^k` または general `n=p^k` のどちらか一方に統一する。

---

# 10. Gate H — zero-frequency exceptional surface を明示

prime-power mode では

```text
r-(p^k) = -ε - k log p
```

である。

`hε : 0 < ε`, `hp : Nat.Prime p`, `hk : 0 < k` の下では

```text
r-(p^k) < 0
```

を exact に証明できるので、minus frequency は zero にならない。

一方

```text
r+(p^k) = ε - k log p
```

は zero になり得る。

exact classification:

```text
r+(p^k) = 0
  ↔ ε = k log p
```

を公開してよい。

zero-frequency branch では既存

```lean
pascalCenteredXiPrimeSidePhasePrimitive_zero_frequency
```

により

```text
PhasePrimitive(a,0,T) = a*T
```

が利用できる。

これにより future closed-form audit が `r+=0` と `r+≠0` を安全に分岐できる。

今回この exceptional surface から kernel sign を結論してはならない。

---

# 11. Gate I — optional: nonzero-frequency PhasePrimitive closed form

これは optional。

CS13 marker

```lean
PascalCenteredXiPrimeSideModePhaseClosedFormGap.nonzeroFrequencyClosedFormPending
```

を一段進めたい場合、`r ≠ 0` の下で

```text
PhasePrimitive(a,r,T)
  = exp(a*r) *
      (
        a * sin(r*T) / r
        + T * cos(r*T) / r
        - sin(r*T) / r^2
      )
```

相当の closed form を証明してよい。

同値な整理形でもよい。

これは elementary real-calculus identity であり、符号 provider ではない。

実装負荷が大きい、または interval-integral antiderivative API の theorem-name 探索が本題を圧迫する場合は **006U へ送る**。

006T Green に必須なのは Gate A–H のうち phase primitive difference reduction とその order/equality classification まで。

既存 CS13 marker を無理に消さない。

---

# 12. 006T 後の exact dynamics picture

006T Green 後は prime-power step `n=p^k` の dynamics が

```text
ΔI(p^k)
  = positive arithmetic scale
      * K(p^k)

K(p^k)
  = positive analytic scale
      * [P+(p^k) - P-(p^k)]
```

まで分解される。

したがって

```text
sign ΔI(p^k)
  = sign K(p^k)
  = sign [P+(p^k) - P-(p^k)]
```

という意味の exact sign-equivalence chain が得られる。

ここで `P+`, `P-` は

```text
r+ = ε - k log p
r- = -ε - k log p
```

という二つの real phase primitive である。

これはユーザー側の構造語彙で言えば

```text
二つの位相寄与が一致する一点
  ↔ K(p^k)=0
  ↔ prime-power increment=0
```

という balance surface を exact に露出する。

ただしこれはまだ radial contact

```text
Residual(X)=0
```

そのものではない。

一つの prime-power event が zero increment であることと、累積 residual が zero になることを混同しない。

---

# 13. 今回閉じる frontier / 残す frontier

## 13.1 今回閉じてよいもの

006S marker:

```lean
CfzpPrimePowerModeKernelSignGap.noIndependentPrimePowerModeKernelSignProvider
```

が指している「符号問題の所在」を、006T ではより精密に

```text
kernel sign
  ↔ phase primitive order
```

へ reduction する。

marker 自体を削除する必要はない。

unconditional sign provider は依然存在しないためである。

## 13.2 必ず残すもの

次は未解決のまま:

```text
P+(p^k) と P-(p^k) の universal ordering
K(p^k) の universal sign
K(p^k) の universal nonvanishing
interaction monotonicity in X
baseline reach
finite contact existence
cofinal/eventual reach
pointwise source zero
zeta zero
RH
```

006T 後の新 marker 候補:

```lean
inductive CfzpPrimePowerPhasePrimitiveOrderingGap : Prop
  | noIndependentPrimePowerPhasePrimitiveOrderingProvider
```

marker は一つで十分。

---

# 14. Dependency / firewall

禁止:

- `Complex.arg`
- arbitrary complex base に対する新しい global `Complex.log` branch
- infinite Euler product
- `X → ∞` の新規議論
- limit exchange
- unconditional kernel positivity / negativity
- unconditional prime-power increment positivity / negativity
- prime-power だけから kernel 非零を導くこと
- prime-power だけから increment 非零を導くこと
- phase primitive を nonnegative mass と呼ぶこと
- `normSq(Σ d_q) = Σ normSq(d_q)` 型の cross-term 消去
- local zero increment から radial contact への短絡
- finite contact から pointwise source zero / zeta zero / RH への短絡
- `sorry`
- `admit`
- `axiom`
- `native_decide`

許可:

- existing positive-natural-base `Complex.cpow`
- `Real.log (n : ℝ)`
- `Real.exp`, `Real.sin`, `Real.cos`
- finite interval integrals
- existing CS13 boundary/phase APIs
- pure real algebra/order classification

---

# 15. 実装順序

推奨:

```text
1. new module / imports
2. prime-power increment sign ↔ kernel sign
3. phase abscissa / r+ / r- helper
4. positive critical-line scale helper
5. pointwise integrand = scaled phase-density difference
6. kernel = scaled PhasePrimitive difference
7. kernel zero/sign ↔ primitive equality/order
8. prime-power frequency specialization
9. prime-power increment zero/sign ↔ primitive equality/order
10. zero-frequency exceptional classification
11. optional nonzero-frequency primitive closed form
12. frontier marker / doc comment
13. DkMath/RH.lean public import
```

最初に Gate A を通して arithmetic coefficient の問題を完全に外し、その後 CS13 phase ledger を一段ずつ real form へ剥く。

---

# 16. 成功条件

006T Green 条件:

1. `CosmicFormulaZetaInteractionModeKernelPhaseBalanceAudit.lean` を追加。
2. `DkMath/RH.lean` に public import。
3. prime-power event 上で increment sign/zero を kernel sign/zero へ exact reduction。
4. centered phase abscissa `a = σ - 1/2` を明示。
5. two frequencies `r+ = ε-log n`, `r- = -ε-log n` を明示。
6. positive natural mode の integrand を二周波数 phase-density difference へ exact 展開。
7. `K(n)` を positive scale × `PhasePrimitive(a,r+,T)-PhasePrimitive(a,r-,T)` へ exact 展開。
8. `K(n)=0` iff primitive equality を証明。
9. kernel positive/negative/nonnegative/nonpositive を primitive order へ分類。
10. witnessed prime power で `log(p^k)=k log p` を使い frequency を specialize。
11. prime-power increment zero/sign を primitive equality/order へ接続。
12. minus frequency が prime-power 上 zero でないことを必要なら公開。
13. plus zero-frequency branch を `ε = k log p` として分類可能にする。
14. unconditional kernel sign theorem を追加しない。
15. monotonicity / reach / contact existence を追加しない。
16. zeta-zero / RH conclusion を追加しない。
17. target module build Green。
18. `lake build DkMath.RH` Green。
19. `./lean-build.sh` Green。
20. `./lean-test.sh` Green。
21. `git diff --check` Green。
22. new module に `sorry`, `admit`, `axiom`, `native_decide` なし。
23. new module に新規 `Complex.arg` / arbitrary-complex-base global `Complex.log` branch なし。

---

# 17. 006U への候補

006T Green 後の第一候補は

```text
CFZP-006U — nonzero-frequency primitive closed-form / event-phase cell audit
```

である。

006T で

```text
K(p^k)
  = positive scale * [P+(p^k)-P-(p^k)]
```

まで閉じた後、006U では `r ≠ 0` の primitive closed form を実装し、

```text
r+ = ε-k log p
r- = -ε-k log p
```

の phase cell ごとに何が exact に分類可能かを監査する。

ただし closed form が得られても universal sign は自動ではない。

三角関数の位相反転が残るなら、それを新しい provider frontier として正直に記録する。

---

# 18. 006T の位置づけ

006R は dynamics を

```text
ΔI(n)=2Λ(n)K(n)
```

まで局所化した。

006S は arithmetic support を

```text
nonzero event
  ↔ prime power ∧ K(n)≠0
```

まで分類した。

006T の役割は残った `K(n)` を

```text
positive scale
  ×
(two real phase primitives の差)
```

へ exact に解体することである。

これにより「素数冪がいつ現れるか」と「そのイベントがどちら向きへ動くか」がさらに分離される。

次の frontier は arithmetic support ではなく、二つの explicit real phase primitive の ordering である。
