# CFZP-0035 — critical-line completed-zeta angular-balance amendment 実装指示

## 0. Status

- Repository: `Deskuma/dkmath`
- Working branch: `wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`
- Parent implementation: CFZP-0034 angular-velocity amendment
- Expected parent commit: `192ce96fe33ad1a10a0520a0e83b9346b8ab9807`
- 日本語を正本とする。

CFZP-009 は Green-A のまま閉じている。

CFZP-0034 も Gate A〜D を Green-A とする。

0034 で零点以外の critical line に対して exact に

```text
omega_zeta(t)
  = (x y' - y x') / (x^2 + y^2)
  = Re(zeta'(s(t)) / zeta(s(t)))
  = -Re(pascalXiOrdinaryZetaNegLogDeriv(s(t)))
```

まで閉じた。

残る Gate E は、新しい phase 仮説ではなく、0031 で既に証明済みの completed-zeta critical-line realness と product differentiation を接続する技術 bridge である。

0035 はこの一穴だけを閉じる。

`Complex.arg`、global `Complex.log`、continuous angle lift、zero-counting、RH、006/009 source-side backlog を導入しない。

---

## 1. 0035 の中心 identity

critical-line point を

```text
s(t) = 1/2 + i t
```

とする。

0031 には exact に

```text
completedRiemannZeta(s(t)) is real
completedRiemannZeta(s(t))
  = zeta(s(t)) * GammaR(s(t))
```

がある。

したがって product path

```text
F(t) := zeta(s(t)) * GammaR(s(t))
```

は全ての `t` で実数値である。

よって

```text
Im(F(t)) = 0
```

は恒等的であり、その real derivative も `0`。

一方 chain/product rule から

```text
F'(t)
  = i * (zeta'(s(t)) * GammaR(s(t))
      + zeta(s(t)) * GammaR'(s(t)))
```

である。

したがって `Im(F'(t)) = 0` は

```text
Re(
  zeta'(s(t)) * GammaR(s(t))
    + zeta(s(t)) * GammaR'(s(t))
) = 0
```

を与える。

`zeta(s(t)) != 0` と `GammaR(s(t)) != 0` の下で割れば

```text
Re(zeta'(s(t)) / zeta(s(t)))
  + Re(GammaR'(s(t)) / GammaR(s(t)))
  = 0
```

となる。

0031 の

```text
cfzpRiemannSiegelPhaseRate t
  = Re(logDeriv GammaR (s(t)))
```

と 0034 の

```text
cfzpCriticalLineZetaAngularVelocity t
  = Re(zeta'(s(t)) / zeta(s(t)))
```

を合わせ、最終的に

```text
cfzpCriticalLineZetaAngularVelocity t
  = - cfzpRiemannSiegelPhaseRate t
```

を exact theorem として公開する。

これは real-valued `arg` を一切導入しない Riemann–Siegel phase-rate balance である。

---

## 2. 推奨 module

新規:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineAngularVelocityBalanceAudit
```

path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaCriticalLineAngularVelocityBalanceAudit.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineAngularVelocityAudit
import Mathlib.Tactic
```

必要なら Gamma derivative 用 Mathlib import を追加してよいが、既存 import chain で閉じるなら増やさない。

`DkMath.RH` に公開 import を追加する。

---

## 3. Gate A — factorized critical-line product path

first-class に product path を置く。

候補:

```lean
noncomputable def cfzpCriticalLineCompletedProductPath (t : ℝ) : ℂ :=
  riemannZeta (cfzpCriticalLinePoint t) *
    Complex.Gammaℝ (cfzpCriticalLinePoint t)
```

0031 の factorization bridge を使って

```text
cfzpCriticalLineCompletedProductPath t
  = completedRiemannZeta (cfzpCriticalLinePoint t)
```

を exact に証明する。

critical line では `s(t) != 0`、`GammaR(s(t)) != 0` が既存 theorem から得られる。

続いて既存

```lean
cfzpCompletedRiemannZeta_criticalLine_im_eq_zero
```

を用いて

```text
(cfzpCriticalLineCompletedProductPath t).im = 0
```

を全 `t` で証明する。

ここでは completed-zeta の derivative API は使わなくてよい。

---

## 4. Gate B — product path derivative

critical line の zeta path derivative は0034で実装済みだが、複素 `HasDerivAt` helper が private の場合は、この module 内で最小限再構成してよい。

GammaR についても critical line では `Re(s)=1/2>0` なので非零。

必要なら既存 `PascalCenteredXiCompletedZetaLogDerivBridge` と同じ方法で局所的に

```text
DifferentiableAt C GammaR s(t)
```

を得る。

推奨 route:

```text
Complex.differentiable_GammaR_inv
+ GammaR(s(t)) != 0
```

から GammaR の differentiability を回収する。

critical-line coordinate の real derivativeは `i`。

zeta と GammaR を real-parameter path として chain rule し、product rule により

```text
deriv (fun u : R =>
  riemannZeta (s(u)) * GammaR (s(u))) t
=
I * (deriv riemannZeta (s(t)) * GammaR(s(t))
   + riemannZeta(s(t)) * deriv GammaR (s(t)))
```

相当の exact theorem を得る。

Lean の multiplication order は theorem に合わせてよい。

注意:
- `deriv GammaR` の記法は Mathlib の exact type に合わせる。
- product path derivative を `Complex.deriv` と real `deriv` で混同しない。
- critical-line path は `R -> C` なので外側の derivative は real derivative。

---

## 5. Gate C — real-path derivative forces zero angular balance

Gate A で

```text
fun u => (cfzpCriticalLineCompletedProductPath u).im
```

が pointwise `0` である。

したがってその real derivativeも `0`。

Gate B の product derivativeを imaginary-part CLM に通し、

```text
Re(
  deriv riemannZeta(s(t)) * GammaR(s(t))
    + riemannZeta(s(t)) * deriv GammaR(s(t))
) = 0
```

相当を exact に固定する。

ここではまだ division しなくてよい。

推奨 theorem family:

```lean
cfzpCriticalLineCompletedProduct_im_eq_zero
cfzpCriticalLineCompletedProduct_im_deriv_eq_zero
cfzpCriticalLineCompletedProduct_rate_numerator_re_eq_zero
```

名前は実装に合わせて調整可。

---

## 6. Gate D — logarithmic-rate balance

`hzeta : riemannZeta (cfzpCriticalLinePoint t) != 0` を仮定する。

GammaR は既存 theorem

```lean
cfzpCriticalLineGammaRCarrier_ne_zero t
```

で非零。

Gate C の numerator equality を割り算へ整理して

```text
Re(deriv riemannZeta(s(t)) / riemannZeta(s(t)))
  + Re(logDeriv GammaR (s(t)))
  = 0
```

を証明する。

`logDeriv_apply` 等、既存 Mathlib API を使う。

可能なら中間 theorem として

```text
Re(zeta'/zeta)
  = - Re(GammaR'/GammaR)
```

も公開する。

分母非零性を明示し、field simplification で totalized quotient の zero case を混ぜない。

---

## 7. Gate E — final angular-velocity / Riemann–Siegel phase-rate equality

0034 の

```lean
cfzpCriticalLineZetaAngularVelocity_eq_zetaLogDeriv_re
```

および0031の

```lean
cfzpRiemannSiegelPhaseRate
```

を接続して、必須の最終 theorem を得る。

推奨:

```lean
theorem cfzpCriticalLineZetaAngularVelocity_eq_neg_riemannSiegelPhaseRate
    (t : ℝ)
    (hzeta : riemannZeta (cfzpCriticalLinePoint t) ≠ 0) :
    cfzpCriticalLineZetaAngularVelocity t =
      - cfzpRiemannSiegelPhaseRate t := by
  ...
```

これは0034で Gap にした

```lean
CfzpCriticalLineCompletedZetaAngularVelocityBalanceGap
```

の技術内容を閉じる theorem である。

既存 inductive marker 自体を削除する必要はない。
新 theorem が provider になったことを doc/roadmap で明示すればよい。

---

## 8. OOL interpretation theorem surface

安価なら、0034 の Cartesian theorem と Gate E をまとめる closeout theorem を追加する。

概念:

```text
((Re zeta) * d(Im zeta)/dt
 - (Im zeta) * d(Re zeta)/dt)
/
((Re zeta)^2 + (Im zeta)^2)

= - RiemannSiegelPhaseRate(t)
```

ただし theorem statement が極端に長くなるなら、既存二 theorem の composition で十分。

重要なのは、OOL の historical derivative formula が branch-free に GammaR / Riemann–Siegel smooth phase-rate と exact 接続したことを公開 surface に残すこと。

---

## 9. Firewall

0035 では以下を禁止する。

- `Complex.arg`
- 新しい global `Complex.log` branch
- continuous real theta lift
- zero-crossing jump count / `N(T)` identification
- RH conclusion
- research-roadmap の RH-equivalent provider 利用
- 006/009 の common-baseline reach を仮定して phase balance を出すこと
- prime-event monotonicity

この theorem は critical-line nonzero point の局所 analytic identity であり、RH の新しい証明ステップではない。

---

## 10. 検証

最低限:

```bash
lake build DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineAngularVelocityBalanceAudit
lake build DkMath.RH
./lean-build.sh
./lean-test.sh
git diff --check
```

新規 module について

```text
sorry
admit
axiom
native_decide
Complex.arg
```

が無いことを確認する。

---

## 11. 完了後の進路

0035 Green 後は phase investigation を追加延長しない。

0031〜0035 により critical-line phase toolkit は

```text
GammaR unit carrier
  + Hardy real/sign decomposition
  + projective doubled phase
  + Cartesian angular velocity
  + zeta/GammaR phase-rate balance
```

まで閉じたとみなし、CFZP-009 の source-side backlog に戻る。

残る本筋は

```text
finite/cofinal common-baseline reach provider
amplitude-side Gap -> source ray-minus whole exact projection
```

である。
