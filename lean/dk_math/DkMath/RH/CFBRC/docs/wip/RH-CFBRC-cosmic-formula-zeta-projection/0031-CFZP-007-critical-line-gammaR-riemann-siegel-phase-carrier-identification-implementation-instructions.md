# CFZP-0031 — CFZP-007 critical-line GammaR / Riemann–Siegel phase-carrier identification 実装指示

## 0. Status

- Repository: `Deskuma/dkmath`
- Working branch: `wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`
- Parent implementation: CFZP-006Z
- Expected parent commit: `7a022af0c0e0d6e2b5de99f0da9656939796d617`
- 日本語を正本とする。

CFZP-006 は Green-B closeout とする。

006Z で exact に

```text
pi * CompletionRemainder_X
  = RayMinusEnergy_X + CommonBaselineDefect_X
```

まで整理され、未解決なのは

```text
CommonBaselineDefect_X = 0
```

と

```text
amplitude-side Gap -> source ray-minus whole
```

の exact bridge である。

この二点は backlog として保持し、007 で勝手に仮定しない。

一方、OOL-KND で観測された `Re s = 1/2` の drift-free phase carrier の正体を見極めるため、007 は completed-zeta の Archimedean factor `Complex.Gammaℝ` を臨界線上で branch-free に回収する。

007 は prime-power event の単調性を追わない。

---

# 1. 007 の出口条件

007 は一つの module で次の三層を exact に閉じることを目標とする。

```text
critical line s(t) = 1/2 + i t
  ↓
GammaR(s(t))
  ↓ exact half-argument
Gamma(1/4 + i t/2) and pi^(-s/2)
  ↓ normalization
unit GammaR phase carrier U(t)
  ↓ completed-zeta functional equation / conjugation
U(t) * zeta(1/2 + i t) is real
  ↓ existing Archimedean log derivative
smooth phase-rate carrier
```

これを Riemann–Siegel theta の **branch-free unit carrier / rate surface** として扱う。

実数値の連続 angle lift `theta(t)` 自体は今回必須にしない。

`Complex.arg` や global `Complex.log` branch を導入してまで angle を定義してはならない。

---

# 2. 推奨 module

新規:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineGammaRPhaseCarrierAudit
```

path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaCriticalLineGammaRPhaseCarrierAudit.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaSourceProjectionCloseoutAudit
import DkMath.RH.CFBRC.PascalCenteredXiCompletedZetaLogDerivBridge
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic
```

`Mathlib.NumberTheory.Harmonic.ZetaAsymp` は `riemannZeta_conj` が必要な場合に使う。
既存 import chain だけで conjugation が閉じるなら import を増やさなくてよい。

---

# 3. Gate A — critical-line point と `1/4` の exact recovery

first-class coordinate を置く。

候補:

```lean
noncomputable def cfzpCriticalLinePoint (t : ℝ) : ℂ :=
  criticalLineCenter + (t : ℂ) * Complex.I
```

基本:

```text
Re(s(t)) = 1/2
Im(s(t)) = t
1 - s(t) = conj(s(t))
s(t) / 2 = 1/4 + i*(t/2)
```

を exact theorem にする。

特に最後の theorem は 007 の重要な幾何 bridge である。

推奨:

```lean
cfzpCriticalLinePoint_re
cfzpCriticalLinePoint_im
cfzp_one_sub_criticalLinePoint_eq_conj
cfzpCriticalLinePoint_div_two_eq_quarter_add_half_im
```

数式上の `1/4` は外から挿入した定数ではなく、`1/2` の critical-line center を `Gammaℝ` の `s/2` に通した結果として出す。

---

# 4. Gate B — `Gammaℝ` carrier の exact factorization

定義:

```lean
noncomputable def cfzpCriticalLineGammaRCarrier (t : ℝ) : ℂ :=
  Complex.Gammaℝ (cfzpCriticalLinePoint t)
```

Mathlib の

```lean
Complex.Gammaℝ_def
```

を使い、exact に

```text
GammaR(s(t))
  = pi^(-s(t)/2) * Gamma(s(t)/2)
```

を公開する。

さらに Gate A を使って Gamma argument を

```text
1/4 + i*(t/2)
```

へ rewrite する theorem を公開する。

期待 surface:

```text
cfzpCriticalLineGammaRCarrier t
  = (Real.pi : C)^(-(cfzpCriticalLinePoint t)/2)
      * Complex.Gamma ((1/4 : C) + (t/2 : C) * I)
```

係数・cast・division は Lean に決めさせる。

また `Re(s(t)) = 1/2 > 0` から

```lean
cfzpCriticalLineGammaRCarrier_ne_zero
```

を `Complex.Gammaℝ_ne_zero_of_re_pos` で閉じる。

---

# 5. Gate C — branch-free unit phase carrier

実数 angle の branch を選ばず、GammaR の direction だけを正規化する。

定義候補:

```lean
noncomputable def cfzpRiemannSiegelUnitCarrier (t : ℝ) : ℂ :=
  cfzpCriticalLineGammaRCarrier t /
    (Complex.abs (cfzpCriticalLineGammaRCarrier t) : ℂ)
```

`Complex.abs` では proof ergonomics が悪ければ `norm` / coercion の既存 API に合わせてよい。

必須:

```text
GammaR carrier != 0
abs GammaR carrier > 0
norm U(t) = 1
U(t) != 0
```

可能なら

```text
U(-t) = conj(U(t))
```

も公開する。

これは conventional real-valued `theta(t)` そのものではなく、

```text
exp(i * theta(t))
```

に相当する branch-free unit-circle carrier として扱う。

実数 angle lift の存在・正規化は別 frontier とする。

---

# 6. Gate D — critical-line completed-zeta realness

中心 theorem 1。

まず

```text
1 - s(t) = conj(s(t))
```

と Mathlib の

```lean
completedRiemannZeta_one_sub
```

を使う。

必要なら次の conjugation bridge を有限・局所的に証明する。

```text
completedRiemannZeta(conj s)
  = conj(completedRiemannZeta(s))
```

既存 theorem が無い場合は、critical line の `Re s > 0` を使って

```text
completedRiemannZeta s = riemannZeta s * GammaR s
```

へ展開し、

```text
riemannZeta(conj s) = conj(riemannZeta s)
Gamma(conj z) = conj(Gamma z)
```

および positive-real base `pi` の cpow conjugationを使う。

新しい global complex-log branch は導入しない。

最終的に

```lean
cfzpCompletedRiemannZeta_criticalLine_im_eq_zero
```

または equivalent theorem として

```text
completedRiemannZeta(s(t)) = conj(completedRiemannZeta(s(t)))
```

を得る。

これは zeta zero の仮定なしで臨界線全体に対して証明する。

---

# 7. Gate E — branch-free Hardy / Riemann–Siegel real carrier

中心 theorem 2。

既存

```lean
completedRiemannZeta_eq_riemannZeta_mul_Gamma_of_ne_zero
```

を再利用し、critical line で

```text
riemannZeta(s(t)) * GammaR(s(t))
```

が real であることを exact に示す。

次に positive real scalar `abs GammaR(s(t))` で割り、

```text
U(t) * riemannZeta(s(t)) is real
```

を証明する。

推奨 API:

```lean
noncomputable def cfzpRiemannSiegelHardyCarrier (t : ℝ) : ℂ :=
  cfzpRiemannSiegelUnitCarrier t * riemannZeta (cfzpCriticalLinePoint t)

theorem cfzpRiemannSiegelHardyCarrier_im_eq_zero
    (t : ℝ) :
    (cfzpRiemannSiegelHardyCarrier t).im = 0
```

または

```text
carrier = conj carrier
```

でもよい。

可能なら real-valued wrapper

```lean
cfzpRiemannSiegelHardyReal (t : ℝ) : ℝ :=
  (cfzpRiemannSiegelHardyCarrier t).re
```

と

```text
HardyCarrier = ofReal(HardyReal)
```

まで公開する。

ここで零点は

```text
riemannZeta(s(t)) = 0
  iff HardyCarrier(t) = 0
```

までなら `U(t) != 0` から exact に閉じてよい。

これは RH statement ではない。

---

# 8. Gate F — existing Archimedean log-derivative と smooth phase-rate

中心 theorem 3。

既存:

```lean
pascalXiArchimedeanLogDeriv s :=
  -logDeriv Complex.Gammaℝ s
```

を使う。

branch-free phase-rate candidate を

```lean
noncomputable def cfzpRiemannSiegelPhaseRate (t : ℝ) : ℝ :=
  (logDeriv Complex.Gammaℝ (cfzpCriticalLinePoint t)).re
```

と定義してよい。

そして exact に

```text
cfzpRiemannSiegelPhaseRate t
  = -(pascalXiArchimedeanLogDeriv (cfzpCriticalLinePoint t)).re
```

を公開する。

これは `theta'(t)` と解釈するための branch-free rate surface である。

もし chain rule の proof が安価なら、GammaR path の logarithmic derivative along `t` からこの real part が unit phase angular velocity に対応する theorem を追加してよい。

ただし calculus が重い場合は、今回の Green 条件には含めない。

---

# 9. OOL-KND との比較で今回まだ言わないこと

007 では旧 OOL-KND plot と real-valued Riemann–Siegel theta の exact equalityをまだ宣言しない。

旧資料には位相規約として

```text
arg-like unwrapped phase
```

と

```text
2 * atan(Im/Re)
```

の表現差があるため、factor 2 / branch / pi-jump normalization の監査が別途必要である。

007 の成果はまず

```text
smooth GammaR unit carrier U(t)
+ real Hardy carrier
+ Archimedean phase rate
```

を exact に固定すること。

次段で OOL-KND 曲線を

```text
smooth carrier
+ discrete sign / zero jump ledger
```

へ分解できるか監査する。

---

# 10. 006 backlog を忘れない

007 は次を証明したことにしてはならない。

```text
cfzp006CommonBaselineDefect = 0
```

または

```text
cfzpAggregateMirrorGapUpTo = normalized ray-minus energy
```

これらは006 Green-Bの残余 obstruction である。

007 の GammaR phase-carrier identification がこれらの bridge にどう関係するかは、007 closeout 後に改めて判定する。

---

# 11. Frontier marker

一個だけ置く。

候補:

```lean
inductive Cfzp007ContinuousThetaAndOolNormalizationGap : Prop
  | noContinuousRealThetaLiftAndOOLPhaseNormalizationProvided
```

意味:

- unit-circle carrier は exact に得た。
- real-valued continuous angle lift の branch normalization はまだしない。
- OOL-KND の旧 phase convention との factor / jump normalization はまだしない。

marker を増殖させない。

---

# 12. ROADMAP 更新

`0000-CFZP-roadmap.md` の Section 19 の末尾に追記し、矛盾を残さない。

明記すること:

1. 006 は Green-B で closed。
2. common-baseline alignment と amplitude-Gap/ray-minus bridge は backlog として保持。
3. CFZP-007 は OOL-KND drift-free carrier の候補を completed-zeta の Archimedean factorから exact に同定する段階へ再誘導。
4. 007 は prime-power event monotonicity を追わない。
5. 007 Green 後に、OOL normalization auditへ行くか、006 backlogへ戻るかを改めて判定する。

---

# 13. Dependency / firewall

禁止:

- `Complex.arg`
- 新しい global `Complex.log` branch
- arbitrary complex-base branch analysis
- prime-power event monotonicity
- equidistribution
- infinite Euler product
- 新しい `X -> infinity` argument
- source Gap の無条件 nonnegativity
- `cfzp006CommonBaselineDefect = 0` の仮定を provider として追加
- amplitude Gap と ray-minus whole の rename 同一視
- OOL plot = Riemann–Siegel theta の無監査宣言
- zeta-zero から `Re s = 1/2` を結論する theorem
- RH conclusion / RH wrapper
- `sorry`
- `admit`
- `axiom`
- `native_decide`

使用してよい:

- `Complex.Gammaℝ_def`
- `Complex.Gammaℝ_ne_zero_of_re_pos`
- `Complex.Gamma_conj`
- `riemannZeta_conj`
- `completedRiemannZeta_one_sub`
- 既存 DkMath completed-zeta / Archimedean log-derivative bridges
- finite real/complex algebra and conjugation

---

# 14. 実装順序

```text
1. new module / imports
2. critical-line point
3. 1/2 -> 1/4 exact half-argument theorem
4. GammaR critical-line factorization
5. GammaR nonzero
6. normalized unit carrier U(t)
7. norm-one / nonzero / optional conjugation symmetry
8. completed-zeta critical-line realness
9. U(t) * zeta(s(t)) realness
10. optional real Hardy wrapper and zero iff
11. Archimedean log-derivative phase-rate bridge
12. single frontier marker
13. DkMath/RH.lean public import
14. ROADMAP Section 19 append
```

---

# 15. Green 条件

007 Green 条件:

1. `CosmicFormulaZetaCriticalLineGammaRPhaseCarrierAudit.lean` を追加。
2. `DkMath/RH.lean` に public import。
3. critical-line point `s(t)` を first-class 化。
4. `s(t)/2 = 1/4 + i*t/2` を exact theorem 化。
5. `GammaR(s(t))` を `pi^(-s/2) * Gamma(1/4+i*t/2)` へ exact factorization。
6. GammaR carrier nonzero。
7. normalized unit carrier `U(t)` を定義。
8. `norm U(t) = 1` または同値の unit-circle theorem。
9. completed zeta が critical line 上で real である exact theorem。
10. `U(t) * zeta(s(t))` が real である exact theorem。
11. `cfzpRiemannSiegelPhaseRate = -Re ArchimedeanLogDeriv` を exact theorem 化。
12. `Complex.arg` / global `Complex.log` branch なし。
13. prime-event monotonicityなし。
14. OOL equality の無監査宣言なし。
15. 006 backlog を解決済み扱いしない。
16. RH conclusionなし。
17. target module build Green。
18. `lake build DkMath.RH` Green。
19. `./lean-build.sh` Green。
20. `./lean-test.sh` Green。
21. `git diff --check` Green。
22. new module に `sorry`, `admit`, `axiom`, `native_decide` なし。

---

# 16. 007 の位置づけ

006Z のあとに再び局所 prime event を追わない。

007 の問いは一つ。

```text
OOL-KND で観測された Re(s)=1/2 の drift-free smooth carrier は、
completed-zeta が既に持つ GammaR critical-line unit phase carrier として
branch-free に exact 回収できるか？
```

`1/4` が `GammaR` の `s/2` から exact に出て、normalized GammaR carrier が zeta を実軸へ固定し、既存 Archimedean log derivative がその smooth phase rateを与えるなら、007 は Green とする。

その時点で初めて、次段で OOL-KND の旧 unwrapped phase / pi-jump convention とこの canonical carrier の normalization を比較する。