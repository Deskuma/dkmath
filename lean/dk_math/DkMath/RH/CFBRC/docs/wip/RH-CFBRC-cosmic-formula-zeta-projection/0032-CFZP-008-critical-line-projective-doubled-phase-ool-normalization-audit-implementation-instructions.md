# CFZP-0032 — CFZP-008 critical-line projective doubled-phase / OOL normalization audit 実装指示

## 0. Status

- Repository: `Deskuma/dkmath`
- Working branch: `wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`
- Parent implementation: CFZP-007
- Expected parent commit: `d4ca140ec74311da2e5cc038a0e9011765ad757a`
- 日本語を正本とする。

CFZP-007 は Green-A closeout とする。

007 で exact に次が確定した。

```text
s(t) = 1/2 + i t
s(t)/2 = 1/4 + i t/2
GammaR(s(t)) != 0
U(t) := GammaR(s(t)) / ||GammaR(s(t))||
||U(t)|| = 1
completedRiemannZeta(s(t)) is real
H(t) := U(t) * zeta(s(t)) is real
H(t) = 0 iff zeta(s(t)) = 0
phaseRate(t) = Re(logDeriv GammaR(s(t)))
```

007 では real-valued continuous angle lift `theta(t)` は導入していない。
また OOL-KND の旧位相規約との exact normalization は deliberate Gap として残した。

008 はこの Gap を `Complex.arg` なしで projective に閉じる。

---

# 1. 008 の中心仮説

OOL-KND には歴史的に二つの位相規約がある。

1. supplement 側は `arg zeta` を unwrap し、zero crossing で pi-jump を追う。
2. Prime Counting 側の実コードは `2 * atan2(Im zeta, Re zeta)` を使う。

007 の Hardy realness から、zero でない critical-line point では概念的に

```text
zetaUnit(t) = sign(H(t)) * conj(U(t))
```

となるはずである。

ここで `sign(H(t))` は `+1` または `-1`。

したがって二乗すれば sign は消えて

```text
zetaUnit(t)^2 = conj(U(t))^2
```

となる。

これは angle language では

```text
2 * phase(zeta(1/2 + i t))
  == -2 * phase(GammaR(1/2 + i t))   mod 2*pi
```

に相当する。

つまり OOL の factor `2` は、pi-jump/sign ambiguity を projective に消す操作として説明できる可能性が高い。

008 はこの statement を branch-free unit-circle equality として Lean に固定する。

---

# 2. 008 の出口条件

008 は一つの module で次を exact に閉じる。

```text
critical-line zeta nonzero
  ↓
normalized zeta unit carrier ZU(t)
  ↓ 007 Hardy realness
ZU(t) = HardySign(t) * conj(U(t))
  ↓ HardySign(t)^2 = 1
ZU(t)^2 = conj(U(t))^2
  ↓
projective doubled-phase carrier equality
```

この equality が Green なら、OOL-KND の `2*atan2` critical-line carrier は

```text
GammaR / Riemann-Siegel smooth projective carrier
```

として exact に説明できる。

実数 angle `arg`, `atan2`, unwrap の equality は今回必須ではない。

---

# 3. 推奨 module

新規:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineProjectivePhaseNormalizationAudit
```

path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaCriticalLineProjectivePhaseNormalizationAudit.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineGammaRPhaseCarrierAudit
import Mathlib.Tactic
```

必要以上に import を増やさない。

---

# 4. Gate A — critical-line zeta unit carrier

定義候補:

```lean
noncomputable def cfzpCriticalLineZetaUnitCarrier (t : ℝ) : ℂ :=
  riemannZeta (cfzpCriticalLinePoint t) /
    (‖riemannZeta (cfzpCriticalLinePoint t)‖ : ℂ)
```

zero point では quotient の totalization により意味が変わるため、主要 theorem は

```lean
hzeta : riemannZeta (cfzpCriticalLinePoint t) ≠ 0
```

の下で述べる。

必須:

```text
zeta norm denominator != 0
norm ZU(t) = 1
ZU(t) != 0
```

zero を phase に含めない。

---

# 5. Gate B — Hardy real sign carrier

007 には

```text
Hc(t) = U(t) * zeta(s(t))
Hc(t) = (H(t) : C)
```

がある。

`hzeta` から既存 zero iff を使って

```text
H(t) != 0
```

を得る。

real sign carrier を first-class に置く。

候補:

```lean
noncomputable def cfzpRiemannSiegelHardySignCarrier (t : ℝ) : ℝ :=
  cfzpRiemannSiegelHardyReal t /
    |cfzpRiemannSiegelHardyReal t|
```

proof ergonomics が悪ければ equivalent な定義を採用してよい。

主要 theorem は nonzero hypothesis の下で

```text
HardySign(t) = 1 or HardySign(t) = -1
HardySign(t)^2 = 1
abs(HardySign(t)) = 1
```

を得ること。

`Real.sign` 等の Mathlib API を使う場合も、zero 時の意味を混ぜない。

---

# 6. Gate C — exact smooth/sign decomposition

008 の中心 theorem 1。

zero でない critical-line pointについて

```text
ZU(t)
  = (HardySign(t) : C) * conj(U(t))
```

を exact に証明する。

導出は 007 の

```text
U(t) * zeta(s(t)) = (H(t) : C)
```

から行う。

`norm U(t) = 1` より

```text
conj(U(t)) * U(t) = 1
```

を使い、

```text
zeta(s(t)) = H(t) * conj(U(t))
```

を回収する。

さらに norm を取り

```text
||zeta(s(t))|| = |H(t)|
```

を exact に示して unit normalization を閉じる。

係数・conjugation の向きを Lean に決めさせる。

推奨 theorem family:

```lean
cfzpCriticalLineZeta_eq_hardyReal_mul_conj_unitCarrier
cfzpCriticalLineZeta_norm_eq_abs_hardyReal
cfzpCriticalLineZetaUnitCarrier_eq_hardySign_mul_conj_riemannSiegelUnitCarrier
```

---

# 7. Gate D — projective doubled-phase equality

008 の中心 theorem 2。

Gate C と `HardySign^2 = 1` から

```text
ZU(t)^2 = conj(U(t))^2
```

を exact に証明する。

first-class carrier を置いてよい。

```lean
noncomputable def cfzpOOLCriticalLineProjectiveDoubledPhaseCarrier (t : ℝ) : ℂ :=
  cfzpCriticalLineZetaUnitCarrier t ^ 2

noncomputable def cfzpRiemannSiegelSmoothProjectiveDoubledPhaseCarrier (t : ℝ) : ℂ :=
  (starRingEnd ℂ (cfzpRiemannSiegelUnitCarrier t)) ^ 2
```

主要 theorem:

```text
hzeta ->
OOLProjectiveDoubledPhaseCarrier(t)
  = RiemannSiegelSmoothProjectiveDoubledPhaseCarrier(t)
```

これは `Complex.arg` を使用しない OOL normalization の正本とする。

さらに可能なら等価な形

```text
(ZU(t) * U(t))^2 = 1
```

も公開する。

こちらは

```text
critical-line zeta phase relative to GammaR is projectively real
```

という意味になる。

---

# 8. Gate E — pi-jump interpretation boundary

supplement の unwrapped `arg zeta` は zero crossing における pi-jump を保持する。

一方 projective doubled carrier は

```text
(+1)^2 = (-1)^2 = 1
```

によりその sign jump を消す。

この区別を module docstring と theorem names で明記する。

Lean では今回、次を主張しない。

```text
continuous real theta lift exists globally
OOL plotted angle equals a chosen theta pointwise as R-valued equality
zero crossing jump count equals zero-counting function
```

これらは separate normalization / lift problem である。

ただし projective statement 自体は branch-free に exact であり、zero でない点では角度を選ばずに OOL factor-2 の数学的意味を固定できる。

frontier marker 候補:

```lean
inductive Cfzp008RealAngleLiftAndZeroJumpLedgerGap : Prop
  | noGlobalRealAngleLiftOrZeroJumpCountingIdentificationProvided
```

007 の `Cfzp007ContinuousThetaAndOolNormalizationGap` は、この008により

```text
projective normalization: solved
real angle lift / unwrapped jump ledger: open
```

へ細分化される。

---

# 9. 006 backlog との関係

008 は phase normalization audit であり、006 の source projection backlog を勝手に閉じない。

未解決のまま保持する。

```text
cfzp006CommonBaselineDefect ε W X = 0
amplitude-side Gap -> source ray-minus whole exact projection
```

008 の projective phase equality からこれらを導いてはならない。

逆に008終了後、大局監査で projective carrier が source alignment に使える exact bridgeを提供するかを評価する。

使えない場合は phase枝をこれ以上掘らず、006 backlogへ戻る。

---

# 10. OOL-KND との正規化上の注意

OOL の歴史資料は位相記法が統一されていない。

- supplement: `theta(t;sigma) := arg zeta(sigma+i t)` と continuous unwrap / pi-jump
- Prime Counting implementation: `theta = 2 * atan2(Im zeta, Re zeta)`

したがって008では文献の実数 angle を定義として取り込まない。

正本は unit-circle/projective equality とする。

概念上

```text
arg convention:
  phase zeta = - phase GammaR + {0, pi}

doubled/projective convention:
  2 phase zeta = -2 phase GammaR mod 2pi
```

であり、後者のみを branch-free に formalize する。

---

# 11. Green-A 判定

Green-A iff:

1. 新規 module が公開 import される。
2. zeta unit carrier が zero-free hypothesis の下で unit norm。
3. Hardy real nonzero / sign carrier が exact。
4. `zeta = HardyReal * conj(U)` が exact。
5. `norm zeta = abs HardyReal` が exact。
6. `zetaUnit = HardySign * conj(U)` が exact。
7. `HardySign^2 = 1` が exact。
8. `zetaUnit^2 = conj(U)^2` が exact。
9. OOL projective doubled-phase carrier equality が first-class theorem。
10. real angle lift / unwrap / zero-jump count は未証明のまま境界化。
11. `Complex.arg` を新規導入しない。
12. global `Complex.log` branch を新規導入しない。
13. 006 source backlog を解決済み扱いしない。
14. RH / zeta-zero location / universal phase-drift uniquenessを結論しない。
15. local Green suite が clean。

---

# 12. 実装後 ROADMAP 更新

`0000-CFZP-roadmap.md` に短く追記する。

内容:

```text
CFZP-007: Green-A.
critical-line GammaR unit carrier / Hardy real carrier / phase-rate identified.

CFZP-008:
zero-free critical-line zeta unit splits into
Hardy sign × conjugate GammaR unit.
After projectivization by squaring, Hardy sign disappears.
This gives the branch-free normalization corresponding to the historical OOL doubled-phase convention.
```

008終了時に必ず次を再判定する。

```text
A. projective carrier が 006 common-baseline / amplitude-Gap bridge に接続可能
B. 接続しないので phase investigation を closeout して 006 backlog に戻る
```

新しい phase subdivisionを自動的に増やさない。

---

# 13. Verification

最低限:

```bash
lake build DkMath.RH.CFBRC.CosmicFormulaZetaCriticalLineProjectivePhaseNormalizationAudit
lake build DkMath.RH
./lean-build.sh
./lean-test.sh
git diff --check
```

禁止監査:

```text
sorry
admit
axiom
native_decide
Complex.arg
```

既存依存由来の warning と新規 module の warning を区別して報告する。
