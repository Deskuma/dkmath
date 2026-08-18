# CFZP-0001 — CFZP-002 mirror Gap analytic Beam 実装指示書

## 0. 作業対象

Repository:

```text
Deskuma/dkmath
```

Working branch:

```text
wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0
```

この指示書作成直前に確認した実装 checkpoint:

```text
5f5d1522dfdd8020a23e8309a76d25277e3b43c4
fix: error
```

対象既存 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerModeProjection
```

現 CFZP-001 は、positive natural label `q` の mode を

```text
common critical radial carrier
× left/right prime-mirror amplitude
× unit cycle state
```

へ exact factorization するところまで実装済みである。

今回の修正 commit では数学的主張を変えず、

- cycle state の exponent の実部が `0` であることを直接展開して unit norm を証明
- `1 - s` の実部を `Complex.sub_re` / `Complex.one_re` で明示展開
- 不要な `Complex.log` branch 条件生成を回避

している。

この CFZP-001 を再設計しない。

---

# 1. 今回の目的

CFZP-002 の目的は、宇宙式 coordinate Gap

```text
δ^2
```

と既存 prime-mirror amplitude Gap

```text
primeMirrorOffsetGap q δ
```

の間に、量そのものの exact factorization を作ることである。

既存定義は

```text
L_q(δ) = exp (-δ * log q)
R_q(δ) = exp ( δ * log q)
MirrorGap_q(δ) = (L_q(δ) - R_q(δ))^2
```

である。

今回得るべき中心式は、概念的に

```text
MirrorGap_q(δ)
  = δ^2 * MirrorGapBeam_q(δ)
```

である。

ただし `MirrorGapBeam_q` は `δ = 0` でも regular な divided-difference Beam とする。

重要:

```text
primeMirrorOffsetGap_eq_zero_iff_delta_eq_zero
```

のような既存 zero-set theorem を factorization の代用にしてはならない。

今回は零点集合の一致ではなく、**量そのものを宇宙式 Gap から prime-mirror Gap へ射影する Beam** を作る。

---

# 2. 数学的正本

`a := Real.log (q : ℝ)` とする。

amplitude difference を

```text
D_q(δ) := exp (-δ a) - exp (δ a)
```

と見る。

すると

```text
D_q(0) = 0
```

であり、微分は

```text
D_q'(0) = -2 a
```

である。

したがって regularized divided difference を概念的に

```text
AmplitudeDifferenceBeam_q(δ)
  := if δ = 0 then -2 * log q
     else D_q(δ) / δ
```

と置ける。

このとき exact に

```text
D_q(δ)
  = δ * AmplitudeDifferenceBeam_q(δ)
```

であり、二乗して

```text
MirrorGap_q(δ)
  = δ^2 * (AmplitudeDifferenceBeam_q(δ))^2
```

を得る。

したがって

```text
MirrorGapBeam_q(δ)
  := (AmplitudeDifferenceBeam_q(δ))^2
```

とする。

中心 `δ = 0` では

```text
MirrorGapBeam_q(0)
  = 4 * (log q)^2
```

となる。

`1 < q` なら `log q > 0` なので、中心でも Beam は消えない。

この事実は重要である。

```text
MirrorGap_q(δ) = δ^2 * MirrorGapBeam_q(δ)
```

において `1 < q` なら、critical center で消えているのは analytic Beam ではなく **宇宙式 coordinate Gap `δ^2`** であることを示す。

---

# 3. 実装方針

## 3.1 新規 module

推奨 filename:

```text
lean/dk_math/DkMath/RH/CFBRC/
  CosmicFormulaZetaMirrorGapBeamProjection.lean
```

推奨 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaMirrorGapBeamProjection
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerModeProjection
import DkMath.CosmicFormula.PowerGapBeam
import Mathlib.Tactic
```

ただし実際に不要な import は削ってよい。

`PowerGapBeam` は、

```text
z^d - x^d = (z - x) * powerBeam
```

という DkMath の既存 `Gap × Beam` 正本である。

今回の theorem はその解析関数版として位置づける。ただし多項式 theorem を無理に適用しない。

---

## 3.2 定義候補

命名は repository の既存 style に合わせて多少調整してよいが、意味を変えないこと。

### amplitude difference

```lean
noncomputable def cfzpMirrorAmplitudeDifference
    (q : ℕ) (δ : ℝ) : ℝ :=
  primeMirrorLeftAmplitude q δ -
    primeMirrorRightAmplitude q δ
```

### regularized analytic Beam

```lean
noncomputable def cfzpMirrorAmplitudeDifferenceBeam
    (q : ℕ) (δ : ℝ) : ℝ :=
  if δ = 0 then
    -2 * Real.log (q : ℝ)
  else
    cfzpMirrorAmplitudeDifference q δ / δ
```

### squared Gap Beam

```lean
noncomputable def cfzpMirrorGapBeam
    (q : ℕ) (δ : ℝ) : ℝ :=
  (cfzpMirrorAmplitudeDifferenceBeam q δ) ^ 2
```

重要:

`cfzpMirrorGapBeam` を単に

```text
if δ = 0 then ... else primeMirrorOffsetGap q δ / δ^2
```

として定義するのは避ける。

それでは factorization がほぼ定義展開だけになり、amplitude difference から Beam が生じる構造を隠してしまう。

まず一次の amplitude difference Beam を作り、その二乗として Gap Beam を得ること。

---

# 4. 必須 theorem surface

## Gate A — source difference の一致

```lean
@[simp] theorem cfzpMirrorAmplitudeDifference_eq
    (q : ℕ) (δ : ℝ) :
    cfzpMirrorAmplitudeDifference q δ =
      primeMirrorLeftAmplitude q δ -
        primeMirrorRightAmplitude q δ := by
  rfl
```

これは API surface 用。不要なら `[simp]` の付与は調整してよい。

---

## Gate B — Beam の中心値

```lean
@[simp] theorem cfzpMirrorAmplitudeDifferenceBeam_zero
    (q : ℕ) :
    cfzpMirrorAmplitudeDifferenceBeam q 0 =
      -2 * Real.log (q : ℝ)
```

および

```lean
@[simp] theorem cfzpMirrorGapBeam_zero
    (q : ℕ) :
    cfzpMirrorGapBeam q 0 =
      4 * (Real.log (q : ℝ)) ^ 2
```

後者の RHS は ring normalization により同値形へ多少変えてよい。

---

## Gate C — amplitude difference の exact Gap × Beam

最重要一次 theorem:

```lean
theorem cfzpMirrorAmplitudeDifference_eq_delta_mul_beam
    (q : ℕ) (δ : ℝ) :
    cfzpMirrorAmplitudeDifference q δ =
      δ * cfzpMirrorAmplitudeDifferenceBeam q δ
```

`δ = 0` / `δ ≠ 0` の場合分けで閉じてよい。

この theorem は source amplitude difference 自身について証明する。

---

## Gate D — prime-mirror Gap の exact factorization

中心 theorem:

```lean
theorem primeMirrorOffsetGap_eq_delta_sq_mul_cfzpMirrorGapBeam
    (q : ℕ) (δ : ℝ) :
    primeMirrorOffsetGap q δ =
      δ ^ 2 * cfzpMirrorGapBeam q δ
```

証明は、

```text
primeMirrorOffsetGap
= (amplitude difference)^2
= (δ * amplitudeDifferenceBeam)^2
= δ^2 * GapBeam
```

という順で行う。

既存

```text
primeMirrorOffsetGap_eq_zero_iff_delta_eq_zero
```

から逆算して証明しない。

---

## Gate E — complex point / critical-center specialization

```lean
theorem primeMirrorOffsetGapAt_eq_centeredSigma_sq_mul_cfzpMirrorGapBeam
    (q : ℕ) (s : ℂ) :
    primeMirrorOffsetGapAt q s =
      (centeredSigma s.re) ^ 2 *
        cfzpMirrorGapBeam q (centeredSigma s.re)
```

これが今回の宇宙式 → RH 座標 bridge の主要 surface である。

概念的には

```text
Cosmic coordinate Gap
  (centeredSigma s.re)^2
        ↓
cfzpMirrorGapBeam
        ↓
primeMirrorOffsetGapAt q s
```

となる。

---

# 5. regularity Gate

今回の Beam は `δ = 0` に手で値を埋めただけの不連続関数であってはならない。

少なくとも、次の極限を証明すること。

```lean
theorem tendsto_cfzpMirrorAmplitudeDifferenceBeam_zero
    (q : ℕ) :
    Tendsto
      (cfzpMirrorAmplitudeDifferenceBeam q)
      (nhds 0)
      (nhds (-2 * Real.log (q : ℝ)))
```

または同値な `ContinuousAt` theorem:

```lean
theorem continuousAt_cfzpMirrorAmplitudeDifferenceBeam_zero
    (q : ℕ) :
    ContinuousAt (cfzpMirrorAmplitudeDifferenceBeam q) 0
```

そして Gap Beam 側も

```lean
theorem tendsto_cfzpMirrorGapBeam_zero
    (q : ℕ) :
    Tendsto
      (cfzpMirrorGapBeam q)
      (nhds 0)
      (nhds (4 * (Real.log (q : ℝ)) ^ 2))
```

を得る。

### 実装上の推奨

`cfzpMirrorAmplitudeDifference q` の `HasDerivAt` at `0` をまず証明し、その difference quotient limit を Mathlib の derivative / slope API から取得することを優先する。

Mathlib に既存の normalized `sinh` / divided-difference API があり、それを使う方が短く安定するなら再利用してよい。

ただし、既存 API の theorem 名を推測して無理に合わせない。local Mathlib source を確認して選ぶこと。

巨大な power-series infrastructure を新規に作ってまで `AnalyticAt` を証明する必要はない。

今回の必須 regularity は `Tendsto` または `ContinuousAt` at `0` までとする。

`AnalyticAt` が既存 API で自然に一行程度で得られる場合のみ追加してよい。

---

# 6. positivity / noncollapse Gate

`1 < q` の mode では Beam が中心で非零であることを固定する。

最低限:

```lean
theorem cfzpMirrorGapBeam_zero_pos
    {q : ℕ} (hq : 1 < q) :
    0 < cfzpMirrorGapBeam q 0
```

可能ならさらに全 `δ` について

```lean
theorem cfzpMirrorGapBeam_pos
    {q : ℕ} (hq : 1 < q) (δ : ℝ) :
    0 < cfzpMirrorGapBeam q δ
```

まで狙ってよい。

ただし後者で proof engineering が大きくなるなら、今回の必須 Gate は中心値 positivity まででよい。

最終的に強調したい数学的事実は、`1 < q` なら

```text
MirrorGap_q(δ)
  = δ^2 * MirrorGapBeam_q(δ)

MirrorGapBeam_q(0) > 0
```

であること。

つまり critical center における消失は Beam collapse ではなく coordinate Gap collapse である。

---

# 7. prime-power specialization

CFZP-001 では arithmetic prime-power label が

```text
q = p^k
```

として既に natural label `Complex.cpow` へ canonical fold されている。

今回の Core はまず任意 natural label `q` で完成させる。

その後、必要なら prime-power surface を薄い wrapper として追加する。

特に positive exponent を保証するには `k + 1` を使う方が自然である。

候補:

```lean
theorem cfzpPrimePowerMirrorGap_factorization
    {p : ℕ} (hp : Nat.Prime p) (k : ℕ) (δ : ℝ) :
    primeMirrorOffsetGap (p ^ (k + 1)) δ =
      δ ^ 2 *
        cfzpMirrorGapBeam (p ^ (k + 1)) δ
```

これは本質 theorem ではなく specialization なので、重複が大きいなら省略してよい。

---

# 8. Firewall

今回の module で禁止すること。

```text
- Complex.arg を導入しない
- phase unwrapping を導入しない
- infinite Euler product を導入しない
- riemannZeta / completed-zeta zero を使わない
- rectangle / Mellin / CS38 source をまだ使わない
- primeMirrorOffsetGap_eq_zero_iff_delta_eq_zero で量の factorization を代用しない
- Gap を rectangle remainder と同一視しない
- CFZP-001 の Green theorem を理由なく再設計しない
- sorry / admit / axiom を残さない
```

今回扱うのは real exponential amplitude の有限 mode-level theorem だけである。

---

# 9. `PowerGapBeam` との関係

既存 `DkMath.CosmicFormula.PowerGapBeam` は

```text
z^d - x^d
  = powerGap x z * powerBeam d x z
```

を持つ。

今回の構造は

```text
exp(-δ log q) - exp(+δ log q)
  = δ * analyticDifferenceBeam q δ
```

である。

したがって論文・docs 上の位置づけは

```text
PowerGapBeam
  ↓ analytic divided-difference generalization
CFZP mirror amplitude Beam
```

とする。

ただし一般解析関数用の巨大な抽象ライブラリを今回作らない。

まず `PrimeMirrorOffsetCore` の実在する source object について一例を完全に Green 化する。

汎用化は同型例が二つ以上現れてから検討する。

---

# 10. Export / validation

新 module 単体が Green になった後で、公開 root に import を追加する。

対象:

```text
lean/dk_math/DkMath/RH.lean
```

追加候補:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaMirrorGapBeamProjection
```

順序は CFZP-001 の直後が望ましい。

もし CFZP-001 がまだ `RH.lean` に export されていないなら、CFZP-001 と CFZP-002 を依存順に export する。

validation:

```bash
cd lean/dk_math
lake env lean DkMath/RH/CFBRC/CosmicFormulaZetaMirrorGapBeamProjection.lean
./lean-build.sh
./lean-test.sh
```

repository の通常手順が一括 script のみならそれに従ってよい。

最終報告には必ず次を含める。

```text
- branch head
- changed files
- new definitions
- new theorems
- exact factorization theorem 名
- regularity theorem 名
- center Beam positivity theorem 名
- build/test Green 結果
- sorry / axiom の有無
- 次 Gate へ残した frontier
```

---

# 11. 完了条件

CFZP-002 は、最低限次がすべて Green になった時点で完了とする。

```text
A. amplitude difference Beam が δ = 0 でも regular に定義される

B. amplitude difference
     = δ × amplitudeDifferenceBeam
   が exact

C. primeMirrorOffsetGap
     = δ^2 × cfzpMirrorGapBeam
   が exact

D. primeMirrorOffsetGapAt
     = centeredSigma(s.re)^2 × cfzpMirrorGapBeam(...)
   が exact

E. Beam の δ → 0 regularity が Tendsto / ContinuousAt で証明済み

F. q > 1 なら center Gap Beam が strictly positive

G. root export 後に full build / test Green

H. sorry / admit / axiom なし
```

---

# 12. 次 Gate はまだ実装しない

CFZP-002 が Green になるまで、CFZP-003 の finite aggregate Big / Gap へ進まない。

CFZP-003 の予定は、finite prime-power support 上で positive weight を用い、

```text
AggregateMirrorBig
AggregateMirrorBody
AggregateMirrorGap
```

を同じ support / same weight から構成し、

```text
AggregateMirrorBig
  = AggregateMirrorBody + AggregateMirrorGap
```

を exact に得ることである。

ただしこれは次回レビュー後に改めて指示する。

今回 Codex が勝手に finite sum / Mellin / rectangle まで拡張しないこと。

---

# 13. Codex への最短指示

```text
Deskuma/dkmath の branch
wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0
で作業する。

この文書
0001-CFZP-002-mirror-gap-beam-implementation-instructions.md
を正本とする。

既存 CFZP-001 と PrimeMirrorOffsetCore を再設計せず、
CFZP-002 として mirror amplitude difference の regularized divided-difference Beam を作る。

最重要 theorem は

primeMirrorOffsetGap q δ
  = δ^2 * cfzpMirrorGapBeam q δ

および complex-point specialization

primeMirrorOffsetGapAt q s
  = centeredSigma(s.re)^2 *
      cfzpMirrorGapBeam q (centeredSigma s.re)

である。

δ=0 の Beam 値を derivative-compatible に定義し、
Tendsto または ContinuousAt により regularity を証明する。
q>1 では center Beam が正であることも固定する。

Complex.arg、infinite Euler product、zeta zero、Mellin、rectangle は使わない。
zero-set theorem で量の factorization を代用しない。

新 module 単体を Green 化し、その後 RH.lean へ export、
full ./lean-build.sh && ./lean-test.sh を Green にする。
sorry / admit / axiom は禁止。

Green 後、実装内容と theorem surface を報告して終了する。
CFZP-003 へは進まない。
```
