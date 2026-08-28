# PPW-014 — zeta zero multiplicity / local log-derivative / contour audit 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-013 complete Green
Lean toolchain: v4.32.2
```

PPW-013 までで、有限 critical-mirror zero window `W_R` と非負 mirror energy

```text
E_{n,R} = Σ_{ρ ∈ W_R} primeMirrorOffsetGapAt n ρ
```

が構成され、`1 < n` のとき

```text
E_{n,R} = 0
  ↔ window 内の全 nontrivial zero が re = 1/2

0 < E_{n,R}
  ↔ window 内に off-critical zero が存在
```

まで Green になった。

一方 PPW-012 の pole signature は simple zero に限定されていた。

PPW-014 の第一目的は、この simple-zero 制限を外し、**任意 multiplicity の zeta zero を analytic order で表現し、logarithmic derivative の局所特異構造を multiplicity-aware にすること**である。

第二目的は、Mathlib 現行 API で contour / argument-principle 型の次段階がどこまで直接実装可能かを監査することである。

**重要:** 現行 Mathlib には `analyticOrderAt` / `meromorphicOrderAt` / circle integral / Cauchy integral の強い API がある。一方、一般形の residue theorem / argument principle を一発で呼ぶ完成 API を前提にしてはならない。PPW-014 ではまず局所 multiplicity と局所 circle contribution の基礎を閉じ、全 window の contour sum は次 checkpoint へ分離する。

---

## 2. 新規 module

```text
DkMath.RH.CFBRC.PascalZetaZeroMultiplicityBridge
```

候補 file:

```text
lean/dk_math/DkMath/RH/CFBRC/PascalZetaZeroMultiplicityBridge.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.PascalCriticalMirrorZeroWindowEnergyBridge
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic
```

単体 Green 後に `DkMath/RH.lean` へ公開 import を追加する。

---

## 3. Mathlib API audit — 実装前に `#check`

以下は current Mathlib に存在することを確認済みの主要候補である。exact namespace / implicit arguments は実装時に `#check` すること。

```lean
analyticOrderAt
analyticOrderNatAt
AnalyticAt.analyticOrderAt_eq_natCast
AnalyticAt.analyticOrderNatAt_eq_iff
AnalyticAt.analyticOrderAt_ne_top
AnalyticAt.analyticOrderAt_ne_zero
AnalyticAt.analyticOrderAt_deriv_add_one
AnalyticAt.meromorphicOrderAt_eq

meromorphicOrderAt
meromorphicOrderAt_div
meromorphicOrderAt_mul
meromorphicOrderAt_inv
meromorphicOrderAt_eq_int_iff

isDiscrete_riemannZetaZeros
isDiscrete_iff_forall_mem_exists_isOpen

logDeriv_mul
logDeriv_pow
Filter.EventuallyEq.deriv_eq
Set.EqOn.deriv

Complex.circleIntegral.integral_sub_center_inv
Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
```

### API reality check

- `analyticOrderAt f ρ : ℕ∞` は zero multiplicity の正本候補。
- `analyticOrderNatAt f ρ : ℕ` は finite order を証明したあと theorem-facing multiplicity として使える。
- `AnalyticAt.analyticOrderAt_eq_natCast` は局所因数分解
  `f(z) = (z-ρ)^m g(z)` を与える。
- `meromorphicOrderAt` は pole / zero の order を整数で扱える。
- circle integral / Cauchy integral は存在する。
- 一般 residue theorem / general argument principle が current Mathlib で即利用できるとは仮定しない。

---

## 4. Phase A — zeta zero multiplicity の定義

### 4.1 theorem-facing multiplicity

finite-order proof を通したあと、次を正本とする。

```lean
noncomputable def riemannZetaZeroMultiplicity (ρ : ℂ) : ℕ :=
  analyticOrderNatAt riemannZeta ρ
```

名称が repository 内で衝突する場合は `pascalRiemannZetaZeroMultiplicity` としてよい。

### 4.2 zero で analytic

PPW-012 の既存 theorem を再利用する。

```lean
analyticAt_riemannZeta_of_mem_riemannZetaZeros
```

`NontrivialRiemannZetaZero` からは PPW-013 の

```lean
nontrivialRiemannZetaZero_mem_riemannZetaZeros
```

を通す。

---

## 5. Phase B — analytic order が finite かつ positive であること

### 5.1 finite order

目標:

```lean
theorem analyticOrderAt_riemannZeta_ne_top_of_mem_riemannZetaZeros
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    analyticOrderAt riemannZeta ρ ≠ ⊤
```

推奨 route は zeta-zero set の discreteness を使う。

```text
isDiscrete_riemannZetaZeros
  ↓
ρ の近傍に zero set が {ρ} だけとなる open neighborhood U
  ↓
analyticOrderAt = ⊤ なら zeta は ρ の full neighborhood で恒等的に 0
  ↓
U 内に ρ 以外の zero が発生
  ↓ contradiction
```

`isDiscrete_iff_forall_mem_exists_isOpen` が

```lean
∀ y ∈ riemannZetaZeros,
  ∃ U, IsOpen U ∧ U ∩ riemannZetaZeros = {y}
```

を与える。

`ℂ` の open neighborhood が singleton ではないことの処理で API が煩雑なら、無理に topology を手作業せず、analytic identity / isolated-zero API により `analyticOrderAt ≠ ⊤` を出せる既存 theorem がないか追加監査すること。

**禁止:** `analyticOrderNatAt` は order `⊤` を `0` に潰すため、finite order を証明する前に multiplicity positivity の根拠として使用しない。

### 5.2 positive multiplicity

目標:

```lean
theorem riemannZetaZeroMultiplicity_pos
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    0 < riemannZetaZeroMultiplicity ρ
```

推奨 route:

1. `analyticAt_riemannZeta_of_mem_riemannZetaZeros hρ`
2. `mem_riemannZetaZeros.mp hρ`
3. `AnalyticAt.analyticOrderAt_ne_zero`
4. finite-order theorem
5. `Nat.cast_analyticOrderNatAt` または `analyticOrderNatAt` API

### 5.3 cast-back theorem

```lean
@[simp] theorem analyticOrderAt_riemannZeta_eq_multiplicity
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    analyticOrderAt riemannZeta ρ =
      (riemannZetaZeroMultiplicity ρ : ℕ∞)
```

これを後続 theorem の normalization point とする。

---

## 6. Phase C — exact local factorization at an arbitrary zeta zero

load-bearing theorem:

```lean
theorem exists_riemannZeta_local_factorization
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g ρ ∧
      g ρ ≠ 0 ∧
      riemannZeta =ᶠ[nhds ρ]
        (fun w => (w - ρ) ^ riemannZetaZeroMultiplicity ρ * g w)
```

原則として

```lean
AnalyticAt.analyticOrderNatAt_eq_iff
```

または

```lean
AnalyticAt.analyticOrderAt_eq_natCast
```

をそのまま使う。

独自 Laurent 展開を作らない。

この theorem が arbitrary multiplicity の正本局所モデルになる。

---

## 7. Phase D — multiplicity-aware logarithmic derivative signature

PPW-012 の simple-zero theorem

```lean
tendsto_mul_pascalZetaNegLogDeriv_simpleZero
```

を一般化する。

目標:

```lean
theorem tendsto_mul_pascalZetaNegLogDeriv_zeroMultiplicity
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    Tendsto
      (fun w => (w - ρ) * pascalZetaNegLogDeriv w)
      (nhdsWithin ρ {ρ}ᶜ)
      (nhds (-(riemannZetaZeroMultiplicity ρ : ℂ)))
```

数学的核は local factorization

```text
ζ(w) = (w - ρ)^m g(w),    g(ρ) ≠ 0
```

から

```text
logDeriv ζ(w)
  = m / (w - ρ) + logDeriv g(w)
```

を punctured neighborhood で得ること。

したがって

```text
(w - ρ) * (-logDeriv ζ(w))
  = -m - (w - ρ) * logDeriv g(w)
  → -m
```

となる。

### Lean proof route

局所 `EventuallyEq` をいったん open neighborhood 上の `Set.EqOn` へ落としてから derivative congruence を使う方が安全。

利用候補:

```lean
Filter.EventuallyEq.deriv_eq
Set.EqOn.deriv
logDeriv_mul
logDeriv_pow
```

`g ρ ≠ 0` と continuity/analyticity から `g w ≠ 0` を sufficiently near ρ で確保する。

`w ≠ ρ` は `nhdsWithin ρ {ρ}ᶜ` が供給する。

### fallback

この general limit の derivative congruence plumbing が大きく膨らむ場合、PPW-014A として Phase C まで Green にして止めてもよい。ただしその場合は PPW-014 complete とは呼ばず、`local factorization Green / multiplicity log-derivative pending` と明記する。

---

## 8. Phase E — meromorphic order of the PPW target at every zeta zero

general multiplicity で `pascalZetaNegLogDeriv` は常に simple pole order `-1` を持つ。residue coefficient は `-m` だが pole order 自体は multiplicity に依存しない。

目標候補:

```lean
theorem meromorphicOrderAt_pascalZetaNegLogDeriv_eq_neg_one
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    meromorphicOrderAt pascalZetaNegLogDeriv ρ = (-1 : ℤ)
```

実装 route は二候補。

### Route 1 — analytic orders of numerator / denominator

```text
logDeriv ζ = ζ' / ζ
order(ζ') = m - 1
order(ζ)  = m
order(ζ'/ζ) = -1
```

利用候補:

```lean
AnalyticAt.analyticOrderAt_deriv_add_one
AnalyticAt.meromorphicOrderAt_eq
meromorphicOrderAt_div
```

`WithTop` arithmetic が複雑なら無理にこの route を使わない。

### Route 2 — Phase D の local normal form

Phase D の

```text
(w-ρ) * pascalZetaNegLogDeriv w → -m ≠ 0
```

を local nonvanishing analytic factorへ強化し、`meromorphicOrderAt_eq_int_iff` で order `-1` を示す。

実装しやすい方を選ぶ。

この theorem は推奨だが、Phase D の multiplicity-aware signature が Green なら PPW-014 必須 checkpoint を満たす。

---

## 9. Phase F — finite window multiplicity packaging

次段階の contour accounting に備えて finite sum を用意する。

```lean
noncomputable def pascalCriticalMirrorZeroWindowMultiplicity
    (R : ℝ) : ℕ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    riemannZetaZeroMultiplicity ρ
```

最低限:

```lean
theorem pascalCriticalMirrorZeroWindowMultiplicity_nonneg
    (R : ℝ) :
    0 ≤ pascalCriticalMirrorZeroWindowMultiplicity R
```

これは `Nat` なら自明なので theorem が不要なら置かなくてよい。

より有用なのは:

```lean
theorem pascalCriticalMirrorZeroWindowMultiplicity_pos_of_nonempty
    {R : ℝ}
    (hW : (pascalCriticalMirrorZeroWindowFinset R).Nonempty) :
    0 < pascalCriticalMirrorZeroWindowMultiplicity R
```

ただし PPW-014 の主目的ではない。

### mirror multiplicity invariance

数学的には mirror pair の multiplicity も一致するはずだが、`criticalMirror` は conjugation を含むため complex-analytic composition theoremだけでは直接出ない。

したがって

```lean
riemannZetaZeroMultiplicity (criticalMirror ρ) =
  riemannZetaZeroMultiplicity ρ
```

は **optional research target** とする。

functional equation + conjugation symmetry + nonvanishing prefactorsを exact に追える場合のみ実装する。PPW-014 必須条件には含めない。

---

## 10. Phase G — local circle integral / contour feasibility audit

### 10.1 current Mathlib で使えるもの

circle integral については少なくとも以下がある。

```lean
Complex.circleIntegral.integral_sub_center_inv
Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
```

したがって local factorization を使えば、孤立 zero `ρ` の十分小さい円に対して

```text
∮ pascalZetaNegLogDeriv(w) dw
```

を multiplicity `m` で評価する local theorem は実装可能性が高い。

### 10.2 optional target

```lean
theorem exists_circleIntegral_pascalZetaNegLogDeriv_eq_neg_two_pi_I_mul_multiplicity
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    ∃ r : ℝ, 0 < r ∧
      (∮ w in C(ρ, r), pascalZetaNegLogDeriv w) =
        -(2 * Real.pi * Complex.I) *
          (riemannZetaZeroMultiplicity ρ : ℂ)
```

exact circle-integral notation / multiplication orderは Mathlib normalization に合わせる。

この theorem は **optional**。Phase D が Green なら先に checkpoint を切ってよい。

### 10.3 なぜ global argument principle を今回はやらないか

有限 window 内には複数 zero があり、global contour で一度に数えるには

```text
- boundary に zero / pole が無いこと
- interior zero multiplicity の有限和
- local circles と outer boundary の integral の関係
- annulus / punctured-domain の分割
```

が必要になる。

current Mathlib の Cauchy circle API から組み上げることは可能性があるが、一般 residue theorem を一発で呼ぶ前提は置けない。

よって global contour aggregation は PPW-015 に分離する。

---

## 11. 今回やらないこと

```text
全 zero の simplicity
RH
∀ R, windowEnergy = 0
critical strip での finite PHZ partial-sum convergence
一般 explicit formula
Weil positivity
Li criterion
global residue theorem の自作
全 zero を一つの contour で数える theorem
zero multiplicity から mirror energy = 0 を推論
```

特に multiplicity information は zero の「何重零点か」を測るが、horizontal offset

```text
re ρ - 1/2
```

をゼロへ強制するものではない。

したがって multiplicity theorem だけから PPW-013 energy を消してはならない。

---

## 12. Stop conditions / audit warnings

1. `analyticOrderNatAt` の値 `0` を、finite-order proof 前に「nonzero ではない」と解釈しない。`⊤` が `toNat` で潰れる点に注意。
2. simple-zero theorem を arbitrary zero へそのまま適用しない。
3. `meromorphicOrderAt = -1` だけから residue coefficient `-1` を結論しない。multiplicity `m` の場合 residue は `-m`。
4. `criticalMirror` が zero set を保存することから multiplicity equality を無証明で仮定しない。
5. local circle integral を global argument principle と呼ばない。
6. contour integral が zero count を与えても、それだけで zero の real part が `1/2` になるとは限らない。
7. PPW-013 finite mirror energy と multiplicity sum を同一視しない。前者は horizontal Gap、後者は analytic zero order。
8. RH-equivalent 全称条件を新しい独立 theorem として追加しない。

---

## 13. Build / acceptance criteria

最低限:

```text
lake build DkMath.RH.CFBRC.PascalZetaZeroMultiplicityBridge
lake build DkMath.RH
./lb
git diff --check
```

新規 module に

```text
sorry
axiom
admit
```

を追加しない。

### 必須 acceptance theorem 群

```lean
analyticOrderAt_riemannZeta_ne_top_of_mem_riemannZetaZeros
riemannZetaZeroMultiplicity_pos
analyticOrderAt_riemannZeta_eq_multiplicity
exists_riemannZeta_local_factorization

tendsto_mul_pascalZetaNegLogDeriv_zeroMultiplicity
```

### 推奨

```lean
meromorphicOrderAt_pascalZetaNegLogDeriv_eq_neg_one
pascalCriticalMirrorZeroWindowMultiplicity
```

### optional / feasibility success

```lean
exists_circleIntegral_pascalZetaNegLogDeriv_eq_neg_two_pi_I_mul_multiplicity
```

---

## 14. PPW-014 の意味

PPW-012 では simple zero に対してのみ

```text
(w - ρ) * (-ζ'/ζ)(w) → -1
```

を持っていた。

PPW-014 ではこれを

```text
m = multiplicity of ρ

(w - ρ) * (-ζ'/ζ)(w) → -m
```

へ一般化する。

これにより zeta zero の局所 meromorphic signature は simplicity 仮定から独立になる。

そのうえで PPW-015 は

```text
finite window
  ↓
各 zero の local multiplicity contribution
  ↓
small-circle integrals / outer boundary
  ↓
finite global contour accounting
```

を構築できるかを監査する。

ただし PPW-015 で得られる zero count / multiplicity count はまだ mirror energy をゼロへ落とさない。

その次に必要な本当の新規数学は、prime-side boundary expression または positivity identity が

```text
Σ horizontal mirror Gap
```

をどう拘束するか、である。
