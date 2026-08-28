# PPW-012 — zeta logarithmic-derivative meromorphic zero-signature bridge 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-011 Green
Lean toolchain: v4.32.2
```

PPW-011 までで、有限 Pascal prime-power PHZ は古典的 von Mangoldt Dirichlet polynomial に一致し、`s.re > 1` では

```text
pascalPrimePowerPHZFiniteUpTo X s
  -> - deriv riemannZeta s / riemannZeta s
```

へ収束することが Green になった。

PPW-012 の目的は、ここで得た右辺を **zeta の logarithmic derivative という meromorphic object として明示化し、零点側の局所特異構造まで exact に接続すること** である。

この checkpoint では explicit formula、Li criterion、Weil positivity、critical-strip 内での有限 PHZ cutoff の収束はまだ証明しない。

特に重要な注意として、Lean の除法は零点でも totalized されているため、`riemannZeta ρ = 0` の点で `deriv riemannZeta ρ / riemannZeta ρ` の point value を「無限大」と解釈してはいけない。零点の特異性は必ず punctured neighborhood の極限または meromorphic API で表現すること。

---

## 2. 新規 module

```text
DkMath.RH.CFBRC.PascalZetaLogDerivativeZeroBridge
```

候補 file:

```text
lean/dk_math/DkMath/RH/CFBRC/PascalZetaLogDerivativeZeroBridge.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.PascalVonMangoldtLSeriesBridge
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Tactic
```

単体 Green 後に `DkMath/RH.lean` へ公開 import を追加する。

---

## 3. Mathlib API audit

実装時には必ず `#check` で現在の imported API の型を確認すること。

利用候補:

```lean
logDeriv
logDeriv_apply
AnalyticOnNhd.meromorphicOn
MeromorphicOn.logDeriv
MeromorphicOn.fun_neg
AnalyticAt.tendsto_mul_logDeriv_simple_zero

riemannZetaZeros
mem_riemannZetaZeros
isClosed_riemannZetaZeros
isDiscrete_riemannZetaZeros
IsCompact.inter_riemannZetaZeros_finite

analyticOn_riemannZeta
riemannZeta_one_ne_zero
riemannZeta_conj
riemannZeta_one_sub
```

`riemannZeta_conj` と `riemannZeta_one_ne_zero` は `Mathlib.NumberTheory.Harmonic.ZetaAsymp` 側にある。

---

## 4. meromorphic target の定義

まず PPW-011 の極限値を logarithmic derivative として一つの名前に固定する。

```lean
noncomputable def pascalZetaNegLogDeriv (s : ℂ) : ℂ :=
  - logDeriv riemannZeta s
```

対応 theorem:

```lean
@[simp] theorem pascalZetaNegLogDeriv_eq_neg_deriv_div
    (s : ℂ) :
    pascalZetaNegLogDeriv s =
      - deriv riemannZeta s / riemannZeta s
```

`logDeriv_apply` と符号整理のみで閉じること。

PPW-011 の最終 theorem をこの target 名へ付け替える。

```lean
theorem tendsto_pascalPrimePowerPHZFiniteUpTo_pascalZetaNegLogDeriv
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto
      (fun X => pascalPrimePowerPHZFiniteUpTo X s)
      atTop
      (nhds (pascalZetaNegLogDeriv s))
```

ここでは新しい収束証明をしない。PPW-011 の

```lean
tendsto_pascalPrimePowerPHZFiniteUpTo_neg_deriv_riemannZeta_div
```

を exact に再利用する。

---

## 5. zeta logarithmic derivative の meromorphic 性

`riemannZeta` は `{1}ᶜ` 上 analytic なので、logarithmic derivative は同じ領域で meromorphic であることを theorem 化する。

目標形:

```lean
theorem meromorphicOn_pascalZetaNegLogDeriv :
    MeromorphicOn pascalZetaNegLogDeriv ({1}ᶜ : Set ℂ)
```

推奨経路:

```text
analyticOn_riemannZeta
  -> AnalyticOnNhd.meromorphicOn
  -> MeromorphicOn.logDeriv
  -> neg
```

実装例の形は API に合わせて調整してよい。

```lean
have hz : MeromorphicOn riemannZeta ({1}ᶜ : Set ℂ) :=
  analyticOn_riemannZeta.meromorphicOn
have hlog := hz.logDeriv
simpa [pascalZetaNegLogDeriv] using hlog.fun_neg
```

上記の exact syntax は `#check` 後に合わせる。

この theorem が PPW-012 の第一の load-bearing bridge である。

---

## 6. zeta zero set との theorem-facing bridge

Mathlib の零点集合を直接使う。

```lean
riemannZetaZeros : Set ℂ
mem_riemannZetaZeros : ρ ∈ riemannZetaZeros ↔ riemannZeta ρ = 0
```

まず零点は `1` ではないことを補題化する。

```lean
theorem ne_one_of_mem_riemannZetaZeros
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    ρ ≠ 1
```

`riemannZeta_one_ne_zero` と `mem_riemannZetaZeros` を使う。

次に零点で zeta が analytic であることを theorem-facing に出す。

```lean
theorem analyticAt_riemannZeta_of_mem_riemannZetaZeros
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    AnalyticAt ℂ riemannZeta ρ
```

`analyticOn_riemannZeta` と上の `ρ ≠ 1` を使う。

---

## 7. simple zero の局所 pole signature

PPW-012 の第二の load-bearing theorem。

Mathlib には

```lean
AnalyticAt.tendsto_mul_logDeriv_simple_zero
```

があり、analytic function `f` の simple zero `ρ` に対して

```text
(w - ρ) * logDeriv f w -> 1
```

を punctured neighborhood で与える。

これを zeta に適用し、符号付き target では residue signature `-1` を得る。

推奨 theorem:

```lean
theorem tendsto_mul_pascalZetaNegLogDeriv_simpleZero
    {ρ : ℂ}
    (hρ : ρ ∈ riemannZetaZeros)
    (hρsimple : deriv riemannZeta ρ ≠ 0) :
    Tendsto
      (fun w => (w - ρ) * pascalZetaNegLogDeriv w)
      (nhdsWithin ρ {ρ}ᶜ)
      (nhds (-1))
```

証明構造:

```text
hρ
 -> riemannZeta ρ = 0
 -> zeta analytic at ρ
 -> simple-zero logDeriv theorem
 -> negate
```

必要なら theorem-facing predicate を追加してよい。

```lean
def IsSimpleRiemannZetaZero (ρ : ℂ) : Prop :=
  ρ ∈ riemannZetaZeros ∧ deriv riemannZeta ρ ≠ 0
```

ただし既存 API で十分なら新定義は増やさなくてよい。

### 重要

零点 `ρ` そのものにおける

```lean
pascalZetaNegLogDeriv ρ
```

の値を pole の情報として使用してはいけない。

Lean の field division は zero denominator でも totalized されるため、point value は解析的な pole を表現しない。

必ず上記 punctured-neighborhood theorem を使う。

---

## 8. conjugation symmetry の zero-side bridge

次の exact symmetry を追加する。

```lean
theorem mem_riemannZetaZeros_conj_iff
    {s : ℂ} :
    conj s ∈ riemannZetaZeros ↔ s ∈ riemannZetaZeros
```

`riemannZeta_conj` と `mem_riemannZetaZeros` を使う。

少なくとも片方向 theorem でもよい。

```lean
theorem mem_riemannZetaZeros_conj
    {s : ℂ} (hs : s ∈ riemannZetaZeros) :
    conj s ∈ riemannZetaZeros
```

これは RH を使わない通常の共役対称性である。

---

## 9. open critical strip 内の functional mirror

可能なら同 checkpoint で、open critical strip に限定して `1 - s` の零点対称性を theorem 化する。

predicate 候補:

```lean
def InOpenCriticalStrip (s : ℂ) : Prop :=
  0 < s.re ∧ s.re < 1
```

目標:

```lean
theorem riemannZeta_zero_one_sub_of_openCriticalStrip
    {s : ℂ}
    (hstrip : InOpenCriticalStrip s)
    (hz : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0
```

`riemannZeta_one_sub` の side condition

```text
∀ n : ℕ, s ≠ -n
s ≠ 1
```

は `0 < s.re` と `s.re < 1` から処理する。

さらに共役と組み合わせて

```lean
theorem riemannZeta_zero_one_sub_conj_of_openCriticalStrip
    {s : ℂ}
    (hstrip : InOpenCriticalStrip s)
    (hz : riemannZeta s = 0) :
    riemannZeta (1 - conj s) = 0
```

まで行ければ、CFBRC の critical mirror と Mathlib zero set の exact bridge になる。

既存 CFBRC の `criticalMirror` が import 済みなら、`#check criticalMirror` 後に

```lean
riemannZeta (criticalMirror s) = 0
```

という alias theorem を追加してよい。

この mirror theorem は RH を意味しない。零点集合の対称性だけである。

---

## 10. finite zero-window infrastructure

explicit formula へ進む前段として、compact window に含まれる zeta zeros が有限であることを DkMath 側から使いやすくする。

Mathlib には

```lean
IsCompact.inter_riemannZetaZeros_finite
```

がある。

最低限、wrapper theorem を追加する。

```lean
theorem finite_riemannZetaZeros_in_compact
    {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ riemannZetaZeros).Finite :=
  hK.inter_riemannZetaZeros_finite
```

余裕があれば closed disk 版 Finset を定義する。

```lean
noncomputable def riemannZetaZeroDisk (R : ℝ) : Finset ℂ := ...
```

membership theorem 候補:

```lean
z ∈ riemannZetaZeroDisk R ↔
  z ∈ Metric.closedBall (0 : ℂ) R ∧ riemannZeta z = 0
```

これは optional。API friction が大きければ wrapper theorem までで Green としてよい。

---

## 11. PPW-012 完了条件

必須:

```text
pascalZetaNegLogDeriv
pascalZetaNegLogDeriv_eq_neg_deriv_div
tendsto_pascalPrimePowerPHZFiniteUpTo_pascalZetaNegLogDeriv
meromorphicOn_pascalZetaNegLogDeriv
ne_one_of_mem_riemannZetaZeros
analyticAt_riemannZeta_of_mem_riemannZetaZeros
tendsto_mul_pascalZetaNegLogDeriv_simpleZero
mem_riemannZetaZeros_conj_iff   または同等の共役 closure
finite_riemannZetaZeros_in_compact
```

推奨:

```text
InOpenCriticalStrip
riemannZeta_zero_one_sub_of_openCriticalStrip
riemannZeta_zero_one_sub_conj_of_openCriticalStrip
criticalMirror alias theorem
```

optional:

```text
riemannZetaZeroDisk
closed-disk membership theorem
```

---

## 12. Build / audit

```text
lake build DkMath.RH.CFBRC.PascalZetaLogDerivativeZeroBridge
lake build DkMath.RH
./lb
git diff --check
```

新規 module に

```text
sorry
admit
axiom
```

を追加しない。

---

## 13. Stop conditions

PPW-012 では次を禁止する。

- `s.re ≤ 1` で finite PHZ cutoff が `-ζ'/ζ` へ収束すると主張しない。
- analytic continuation of target と convergence of original Dirichlet partial sums を混同しない。
- zeta zero で `pascalZetaNegLogDeriv ρ` の point value を pole と解釈しない。
- simple zero theorem から「全 zeta zeros は simple」と推論しない。
- zero set symmetry から critical line を導かない。
- mirror pair の中心が `1/2` であることから endpoints が一致すると推論しない。
- scalar PHZ cancellation から prime-coordinate energy collapse を推論しない。
- explicit formula、Li criterion、Weil positivity を未証明のまま名前だけ bridge として使わない。
- RH-equivalent proposition を rename して進捗扱いしない。

---

## 14. この checkpoint の数学的位置

PPW-011 まで:

```text
Pascal / prime powers
  -> Λ(n)
  -> finite Dirichlet polynomial
  -> LSeries
  -> -ζ'/ζ       [Re(s) > 1]
```

PPW-012:

```text
-ζ'/ζ
  -> -logDeriv ζ
  -> meromorphic continuation target on ℂ \ {1}
  -> zeta zero set
  -> simple-zero punctured-neighborhood pole signature
  -> conjugation / functional mirror symmetry
  -> finite compact zero windows
```

この段階で初めて prime-side object と zero-side singularity object が同じ meromorphic target の両側として形式化される。

ただしまだ

```text
prime finite sums
  -> critical-strip zero sum / explicit formula
```

という global transport theorem はない。

PPW-013 は、PPW-012 が Green になった後に、Mathlib の contour / argument principle / meromorphic order API を監査し、有限 zero-window explicit-formula kernel を構成できるかを判定する checkpoint とする。
