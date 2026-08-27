# CFZP-0034 — critical-line zeta angular-velocity / phase-rate amendment 実装指示

## 0. Status

- Repository: `Deskuma/dkmath`
- Working branch: `wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`
- Parent implementation: CFZP-009
- Expected parent commit: `e3c29af8c91e0d0bfe60826deaba1981700aad57`
- 日本語を正本とする。

CFZP-009 は Green-A とみなす。

009 では common-baseline alignment の正しい量化を finite reach problem として exact に固定した。
この amendment は 009 を再オープンせず、0031–0032 で構築した critical-line phase toolkit に不足していた「局所位相速度」の exact identity を補完する。

この作業を CFZP-010 として source-side roadmap を曲げない。
実装完了後は source-side backlog へ戻る。

---

## 1. 目的

OOL-KND で使用した位相変化率の基本式

```text
dtheta/dt
  = (Re(zeta) * d(Im(zeta))/dt - Im(zeta) * d(Re(zeta))/dt)
      / (Re(zeta)^2 + Im(zeta)^2)
```

を、`Complex.arg` や global `Complex.log` を導入せず branch-free に形式化する。

数学的には、complex path `z(t)` の非零点で

```text
omega(t)
  := Im(z'(t) / z(t))
```

と置けば

```text
omega(t)
  = (x(t) * y'(t) - y(t) * x'(t))
      / (x(t)^2 + y(t)^2)
```

である。

critical-line zeta path

```text
s(t) = 1/2 + i t
z(t) = zeta(s(t))
```

では chain rule により

```text
z'(t) = i * zeta'(s(t))
```

なので

```text
omega_zeta(t)
  = Re(zeta'(s(t)) / zeta(s(t)))
```

となる。

既存定義

```lean
pascalXiOrdinaryZetaNegLogDeriv s :=
  -deriv riemannZeta s / riemannZeta s
```

を使えば

```text
omega_zeta(t)
  = -Re(pascalXiOrdinaryZetaNegLogDeriv(s(t)))
```

である。

さらに 0031 の

```text
cfzpRiemannSiegelPhaseRate(t)
  = Re(logDeriv GammaR(s(t)))
```

と critical-line Hardy/completed-zeta realness を組み合わせ、可能なら exact に

```text
omega_zeta(t) = -cfzpRiemannSiegelPhaseRate(t)
```

まで閉じる。

---

## 2. 推奨 module

新規:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineAngularVelocityAudit
```

path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaCriticalLineAngularVelocityAudit.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineProjectivePhaseNormalizationAudit
import DkMath.RH.CFBRC.PascalCenteredXiCompletedZetaLogDerivBridge
import DkMath.RH.CFBRC.CosmicFormulaZetaCommonBaselineAlignmentReachAudit
import Mathlib.Tactic
```

009 import は dependency ordering を保つためであり、source-side theorem を phase identity の証明に使う必要はない。

---

## 3. Gate A — generic branch-free angular velocity

まず zeta 専用にせず、complex state と velocity の純代数量を置く。

候補:

```lean
noncomputable def cfzpComplexAngularVelocity (z dz : ℂ) : ℝ :=
  (starRingEnd ℂ z * dz).im / Complex.normSq z
```

必須 theorem:

```text
cfzpComplexAngularVelocity z dz
  = (z.re * dz.im - z.im * dz.re)
      / (z.re^2 + z.im^2)
```

および `z != 0` の下で

```text
cfzpComplexAngularVelocity z dz
  = (dz / z).im
```

を exact に示す。

この generic identity は angle branch を必要としない。

推奨 theorem names:

```lean
cfzpComplexAngularVelocity_eq_cartesian
cfzpComplexAngularVelocity_eq_div_im
```

---

## 4. Gate B — critical-line zeta path と actual real derivatives

既存

```lean
cfzpCriticalLinePoint (t : ℝ) : ℂ
```

を再利用する。

候補:

```lean
noncomputable def cfzpCriticalLineZetaPath (t : ℝ) : ℂ :=
  riemannZeta (cfzpCriticalLinePoint t)

noncomputable def cfzpCriticalLineZetaComplexVelocity (t : ℝ) : ℂ :=
  Complex.I * deriv riemannZeta (cfzpCriticalLinePoint t)
```

critical line は `Re(s(t)) = 1/2` なので `s(t) != 1` は無条件に閉じる。
`differentiableAt_riemannZeta` を使用して chain rule を厳密に通す。

ユーザー式を literal に残すため、少なくとも次を theorem とする。

```text
deriv (fun u : ℝ => (riemannZeta (cfzpCriticalLinePoint u)).re) t
  = (cfzpCriticalLineZetaComplexVelocity t).re

deriv (fun u : ℝ => (riemannZeta (cfzpCriticalLinePoint u)).im) t
  = (cfzpCriticalLineZetaComplexVelocity t).im
```

Lean API 上 `deriv` 直書きが困難なら `HasFDerivAt` / `HasDerivAt` を先に証明してから `deriv` equality を導く。
単なる informal chain rule で済ませない。

推奨 theorem names:

```lean
cfzpCriticalLineZeta_re_deriv
cfzpCriticalLineZeta_im_deriv
```

---

## 5. Gate C — OOL Cartesian phase-velocity formula

first-class definition:

```lean
noncomputable def cfzpCriticalLineZetaAngularVelocity (t : ℝ) : ℝ :=
  cfzpComplexAngularVelocity
    (riemannZeta (cfzpCriticalLinePoint t))
    (cfzpCriticalLineZetaComplexVelocity t)
```

そして exact に、ユーザー式そのものを公開する。

```text
cfzpCriticalLineZetaAngularVelocity t
  =
    ( Re(zeta(s(t))) * deriv(Im o zeta o s)(t)
      - Im(zeta(s(t))) * deriv(Re o zeta o s)(t) )
    /
    ( Re(zeta(s(t)))^2 + Im(zeta(s(t)))^2 )
```

主要 theorem は zeta zero で phase interpretation をしないため

```lean
hzeta : riemannZeta (cfzpCriticalLinePoint t) ≠ 0
```

を受けてもよいが、純代数式が totalized division のまま無条件に成立するなら generic theorem と derivative theorem の組合せで無条件版を出してよい。

推奨:

```lean
cfzpCriticalLineZetaAngularVelocity_eq_cartesian_derivatives
```

---

## 6. Gate D — zeta logarithmic derivative surface

`hzeta` の下で

```text
cfzpCriticalLineZetaAngularVelocity t
  = Re(deriv riemannZeta (s(t)) / riemannZeta (s(t)))
```

を exact に示す。

理由は

```text
z_t'(t) = i * zeta'(s(t))
Im(i * q) = Re(q)
```

である。

さらに既存 named term へ接続する。

```text
cfzpCriticalLineZetaAngularVelocity t
  = - (pascalXiOrdinaryZetaNegLogDeriv (s(t))).re
```

推奨 theorem names:

```lean
cfzpCriticalLineZetaAngularVelocity_eq_zetaLogDeriv_re
cfzpCriticalLineZetaAngularVelocity_eq_neg_ordinaryZetaNegLogDeriv_re
```

---

## 7. Gate E — Riemann–Siegel GammaR phase-rate balance

0031 では

```text
cfzpRiemannSiegelPhaseRate t
  = Re(logDeriv GammaR (s(t)))
```

が既にある。

0031 の completed-zeta critical-line realness と

```text
completedRiemannZeta(s) = riemannZeta(s) * GammaR(s)
```

を局所微分して、zero でない critical-line point では completed-zeta path の angular velocity が zero であることを示す。

その結果

```text
Re(zeta'(s)/zeta(s))
  + Re(GammaR'(s)/GammaR(s))
  = 0
```

を得て、最終的に

```text
cfzpCriticalLineZetaAngularVelocity t
  = -cfzpRiemannSiegelPhaseRate t
```

を目標とする。

推奨 theorem:

```lean
cfzpCriticalLineZetaAngularVelocity_eq_neg_riemannSiegelPhaseRate
```

証明は `Complex.arg` や angle lift を使ってはならない。
completed-zeta realness、local differentiation、log-derivative/product algebra のみで閉じる。

もし現行 Mathlib API 上、completed-zeta path の real derivative transportだけが独立した技術障害になる場合は、Gate A–D を Green として閉じた上で

```lean
inductive CfzpCriticalLineCompletedZetaAngularVelocityBalanceGap : Prop
  | noCompletedZetaRealPathDerivativeBalanceProvided
```

のように一個の marker に限定する。
別の phase 枝を増やさない。

---

## 8. OOL-KND との意味

この amendment が Gate D まで Green なら、OOL-KND で用いていた局所位相速度

```text
(Re zeta * d Im zeta/dt - Im zeta * d Re zeta/dt)
  / (Re zeta^2 + Im zeta^2)
```

は branch-free に `Re(zeta'/zeta)` と同一視される。

Gate E まで Green なら critical line の nonzero interval 上で

```text
zeta angular velocity
  = -GammaR / Riemann-Siegel angular velocity
```

が exact になる。

これは 0031–0032 の unit/projective carrier equality の infinitesimal counterpart である。

zero crossing の jump ledger は依然として別問題であり、この theorem から零点計数を導かない。

---

## 9. Firewall

禁止:

- new `Complex.arg`;
- global `Complex.log` branch;
- zero point で phase quotient を非零点と同様に解釈すること;
- angle lift の存在を仮定すること;
- zero-jump / zero-counting theorem をこの identity から導くこと;
- RH または RH-equivalent provider の使用;
- 009 common-baseline reach を phase theorem の仮定として混ぜること。

許可:

- `deriv`, `logDeriv`;
- `Complex.normSq`, conjugation;
- critical-line nonzero hypotheses;
- existing completed-zeta/GammaR factorization and conjugation identities。

---

## 10. Public API / build

新規 module を `DkMath.RH` に公開 import する。

検証:

```bash
lake build DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineAngularVelocityAudit
lake build DkMath.RH
./lean-build.sh
./lean-test.sh
git diff --check
```

新規 module について `sorry`, `admit`, `axiom`, `native_decide` を導入しない。

ROADMAP には 009 を Green-A のまま維持し、0034 を cross-cutting phase-rate amendment として追記する。
この amendment の後は source-side finite/cofinal reach provider と amplitude-Gap → ray-minus-whole bridge の大局へ戻る。
