# XDP-006 — Mellin centered dilation / second-difference Codex 実装指示書

作成日: 2026-08-12

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-fixed-Xi-defect-provider-260812-v0
Lean: v4.32.2
mathlib: repository pinned revision
```

作業 directory:

```text
lean/dk_math
```

XDP-005 までで、positive compact-support Mellin data `h : ℝ → ℂ` から

```text
centeredMellinSpectralWeight h z = mellin h (1/2 + z)
```

という globally differentiable spectral weightを作り、その weight を既存 fixed centered-Xi outer contour へ投入して、safe radius 内の有限 weighted zero momentを exact に取得できるようになった。

XDP-006 の目的は、centered spectral parameter `z` に対する二次 weight `z ^ 2` へ近づくため、**multiplicative dilation の Mellin scaling と symmetric second difference を一般 Mellin Core として形式化すること**である。

ただし XDP-006 では、ordinary compact-support Mellin transform が globally `z ^ 2` そのものになるとは主張しない。

本 phase の exact endpoint は次である。

$$
Q_{\tau,h}(z)
\longrightarrow
z^2 H_h(z),
\qquad
H_h(z):=\mathcal M h\left(\frac12+z\right),
$$

ここで `Q_{τ,h}` は multiplicatively dilated Mellin weights の symmetric second difference である。

さらに fixed safe radius の有限 centered-Xi zero set 上では、この pointwise convergence を finite weighted sumへ上げる。

`H_h(z) → 1` を実現する approximate-identity / interpolation 問題は **XDP-007 へ明示的に残す**。

---

# 1. 正本 — XDP-003〜005 Green API

最初に必ず次を読むこと。

```text
DkMath/Analysis/MellinCriticalMirror.lean
DkMath/Analysis/MellinCompactSupport.lean
DkMath/Analysis/MellinCompactSupportHolomorphic.lean
DkMath/RH/CFBRC/MellinCenteredMirrorAdapter.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWeightedOuterContourBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiOuterContourResidueBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiSafeRadiusAnnulusBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiWeilMirrorDefectBridge.lean
```

結果報告も読むこと。

```text
XDP-003-Mellin-centered-mirror-test-adapter-result.md
XDP-004-Safe-radius-annulus-and-compact-Mellin-admissibility-result.md
XDP-005-Mellin-spectral-weight-fixed-Xi-contour-adapter-result.md
```

最低限、次の既存 API を再利用する。

```lean
mellin
MellinConvergent
mellinCriticalMirror
centeredMellinSpectralWeight

differentiable_mellin_of_support_subset_Icc_pos
differentiable_centeredMellinSpectralWeight_of_support_subset_Icc_pos
centeredMellinSpectralWeight_mirror_of_support_subset_Icc_pos

mellinConvergent_of_support_subset_Icc_pos
mellinConvergent_mellinCriticalMirror_of_support_subset_Icc_pos

pascalCenteredXiZeroDiskWeightedMoment
pascalCenteredXiWeightedOuterContourMass
pascalCenteredXiWeightedOuterContourMass_eq
pascalCenteredXiNormalizedWeightedOuterContourMass_eq

pascalCenteredXiMellinWeightedOuterContourMass_eq
pascalCenteredXiNormalizedMellinWeightedOuterContourMass_eq

pascalCenteredXiZeroDiskSecondMoment
pascalCenteredXiSecondWeight
```

正確な theorem 名・引数順は repository head を正本とする。

既存 theorem を再証明しない。

---

# 2. 数学的 Core

## 2.1 multiplicative dilation

`λ > 0` に対して、まず非正規化 dilation を概念的に

$$
(D_\lambda h)(x):=h(x/\lambda)
$$

とする。

Mathlib の Mellin convention

$$
\mathcal M h(s)
=
\int_0^\infty x^{s-1}h(x)\,dx
$$

では、変数変換 `x = λu` により

$$
\mathcal M(D_\lambda h)(s)
=
\lambda^s\mathcal M h(s)
$$

となる。

centered spectral parameter `s = 1/2 + z` では、half-weight を除いた正規化 dilationを用いると

$$
\lambda^{-1/2}
\mathcal M(D_\lambda h)\left(\frac12+z\right)
=
\lambda^z H_h(z)
$$

となる。

`λ = exp τ` とすれば

$$
\lambda^z=e^{\tau z}.
$$

これが XDP-006 の first exact bridge である。

## 2.2 symmetric second difference

`τ ≠ 0` に対して、centered-normalized plus / minus dilation weights を

$$
H_{+,\tau}(z)
:=
e^{-\tau/2}
H_{D_{e^\tau}h}(z),
$$

$$
H_{-,\tau}(z)
:=
e^{\tau/2}
H_{D_{e^{-\tau}}h}(z)
$$

と読む。

上の scaling identity より

$$
H_{+,\tau}(z)=e^{\tau z}H_h(z),
$$

$$
H_{-,\tau}(z)=e^{-\tau z}H_h(z).
$$

そこで

$$
Q_{\tau,h}(z)
:=
\frac{H_{+,\tau}(z)-2H_h(z)+H_{-,\tau}(z)}{\tau^2}
$$

とすると exact に

$$
Q_{\tau,h}(z)
=
\frac{e^{\tau z}-2+e^{-\tau z}}{\tau^2}
H_h(z).
$$

さらに固定した `z` について

$$
\frac{e^{\tau z}-2+e^{-\tau z}}{\tau^2}
\longrightarrow z^2
\qquad(\tau\to0)
$$

なので

$$
Q_{\tau,h}(z)
\longrightarrow
z^2H_h(z).
$$

XDP-006 ではまず **pointwise limit** を Green 化する。

compact-uniform convergence を無理に要求しない。fixed Xi zero disk は finite なので、後の finite sum transport には pointwise convergence で十分である。

---

# 3. 重要な論理境界

次を禁止する。

1. compact-support Mellin transform が global に `1` であると仮定しない。
2. `centeredMellinSpectralWeight h z = z ^ 2` を仮定・主張しない。
3. Dirac delta を ordinary function として使用しない。
4. hard zero-window indicator を Mellin transform と同一視しない。
5. `Q_{τ,h} → z ^ 2` と書かない。正確な target は `z ^ 2 * H_h(z)` である。
6. XDP-006 の finite-sum limit を defect vanishing / RH provider と呼ばない。
7. `H_h = 1` を hidden simp assumption にしない。

本 phase は quadratic spectral multiplier の構成であり、unweighted second moment の realization は未完である。

---

# 4. Gate A — pinned Mathlib scaling API audit

新 theorem を書く前に pinned Mathlib を検索する。

検索語候補:

```text
mellin mul
mellin div
mellin scale
mellin comp_mul
mellin_comp
integral_comp_mul
setIntegral_comp_mul
MeasurePreserving mul
```

`Mathlib/Analysis/MellinTransform.lean` と measure/integral change-of-variables API を確認する。

既存 theorem があれば必ず再利用する。

既存 scaling theorem がない場合のみ、positive-ray set integral の change of variablesとして証明する。

### Gate A report requirement

結果報告に次を残すこと。

```text
- 採用した scaling theorem / substitution API
- λ > 0 がどこで必要か
- complex cpow の normalization convention
- totalized integral に依存した偽 equality がないこと
```

---

# 5. Gate B — generic multiplicative dilation Core

新規 module 第一候補:

```text
DkMath/Analysis/MellinCenteredDilation.lean
```

namespace:

```lean
namespace DkMath.Analysis
```

非正規化 dilation の候補 definition:

```lean
noncomputable def mellinDilate (λ : ℝ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  h (x / λ)
```

名称は既存 repository と衝突する場合変更してよい。

最初に support transport を固定する。

概念形:

```lean
theorem support_mellinDilate_subset
    {h : ℝ → ℂ} {a b λ : ℝ}
    (hλ : 0 < λ)
    (hsupp : Function.support h ⊆ Set.Icc a b) :
    Function.support (mellinDilate λ h) ⊆
      Set.Icc (λ * a) (λ * b) := by
  ...
```

必要なら endpoint order hypothesis を追加する。

同様に `ContinuousOn` transport を作り、XDP-004 の compact-support admissibility theorem が dilated data に適用できるようにする。

---

# 6. Gate C — exact Mellin dilation theorem

主 theorem 第一候補:

```lean
theorem mellin_mellinDilate
    {h : ℝ → ℂ} {λ : ℝ} (hλ : 0 < λ)
    (s : ℂ)
    (... convergence / support hypotheses ...) :
    mellin (mellinDilate λ h) s =
      (λ : ℂ) ^ s * mellin h s := by
  ...
```

ただし Mathlib の cpow notation / scalar normalizationに合わせること。

もし pinned API が `λ ^ s` の代わりに `Complex.cpow` の別 normal form を返すなら、無理に文書通りの RHS に正規化せず、次の centered theorem が clean に出る normal form を採用する。

### 必須安全条件

- `λ > 0` を明示する。
- `λ = 0` や negative scaling を含めない。
- positive integration domain の change-of-variables を使用する。
- convergence を totalized Mellin integral の値 `0` に隠さない。

---

# 7. Gate D — centered normalized dilation

log-dilation parameter `τ : ℝ` を使う layer を追加する。

第一候補:

```lean
noncomputable def centeredMellinDilatedSpectralWeight
    (h : ℝ → ℂ) (τ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(τ : ℂ) / 2) *
    centeredMellinSpectralWeight h_dilated z
```

ここで `h_dilated` は `λ = Real.exp τ` の dilation。

definition の実装形は proof ergonomics に合わせてよい。

必須 exact theorem:

```lean
theorem centeredMellinDilatedSpectralWeight_eq
    ... :
    centeredMellinDilatedSpectralWeight h τ z =
      Complex.exp ((τ : ℂ) * z) * centeredMellinSpectralWeight h z := by
  ...
```

`Real.exp τ > 0` は `Real.exp_pos τ` を使う。

ここで `exp(τ z)` の符号・`1/2` normalization を必ず theorem で固定する。

手計算のコメントだけで済ませない。

---

# 8. Gate E — symmetric second-difference spectral weight

新 definition 候補:

```lean
noncomputable def centeredMellinSecondDifferenceWeight
    (h : ℝ → ℂ) (τ : ℝ) (z : ℂ) : ℂ :=
  if hτ : τ = 0 then
    z ^ 2 * centeredMellinSpectralWeight h z
  else
    (centeredMellinDilatedSpectralWeight h τ z -
        2 * centeredMellinSpectralWeight h z +
        centeredMellinDilatedSpectralWeight h (-τ) z) /
      (τ : ℂ) ^ 2
```

`τ = 0` の値を target に patch しておくと、後の continuity / Tendsto が扱いやすい。

ただし `if` patch が proof を重くする場合、punctured function と `Tendsto` を別に定義してもよい。

最重要 exact theorem (`τ ≠ 0`):

```lean
theorem centeredMellinSecondDifferenceWeight_eq_kernel_mul
    ... (hτ : τ ≠ 0) :
    centeredMellinSecondDifferenceWeight h τ z =
      ((Complex.exp ((τ : ℂ) * z) - 2 +
          Complex.exp (-(τ : ℂ) * z)) /
        (τ : ℂ) ^ 2) *
      centeredMellinSpectralWeight h z := by
  ...
```

係数 `2` の coercion normal form は Lean に合わせる。

---

# 9. Gate F — exponential second-difference kernel limit

まず Mellin を外して pure complex analysis theorem を作る。

候補:

```lean
noncomputable def complexExpSecondDifferenceKernel
    (τ : ℝ) (z : ℂ) : ℂ :=
  if τ = 0 then z ^ 2 else
    (Complex.exp ((τ : ℂ) * z) - 2 +
      Complex.exp (-(τ : ℂ) * z)) / (τ : ℂ) ^ 2
```

主 theorem:

```lean
theorem tendsto_complexExpSecondDifferenceKernel_zero
    (z : ℂ) :
    Tendsto (fun τ : ℝ => complexExpSecondDifferenceKernel τ z)
      (𝓝 0) (𝓝 (z ^ 2)) := by
  ...
```

第一選択は Mathlib の derivative / second derivative / Taylor API を再利用する。

候補ルート:

```text
A. exp Taylor remainder theorem
B. second derivative characterization of symmetric difference
C. exp series and remainder bound
```

最小 proof を選ぶ。

### 禁止

- numerical approximation
- `native_decide`
- informal Taylor expansion only
- Real theoremを Complex に無根拠 coercion

---

# 10. Gate G — weighted quadratic pointwise limit

Gate E/F を合成し、固定 `h,z` に対し

```lean
theorem tendsto_centeredMellinSecondDifferenceWeight_zero
    ... (z : ℂ) :
    Tendsto
      (fun τ : ℝ => centeredMellinSecondDifferenceWeight h τ z)
      (𝓝 0)
      (𝓝 (z ^ 2 * centeredMellinSpectralWeight h z)) := by
  ...
```

を Green にする。

この theorem の数学的 target を弱めない。

`z ^ 2` 単独へ変更してはいけない。

---

# 11. Gate H — differentiability / fixed Xi contour admissibility

`τ ≠ 0` または patched definition 全体について、`z ↦ centeredMellinSecondDifferenceWeight h τ z` が `Differentiable ℂ` であることを示す。

compact-positive-support hypotheses は XDP-005 と同じ contract を優先する。

候補 theorem:

```lean
theorem differentiable_centeredMellinSecondDifferenceWeight
    {h : ℝ → ℂ} {a b τ : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b)) :
    Differentiable ℂ (centeredMellinSecondDifferenceWeight h τ) := by
  ...
```

もし `τ = 0` patch の branch で `z^2 * H_h(z)` の differentiability が必要なら既存 composition/product API を使う。

---

# 12. Gate I — fixed-Xi finite weighted moment limit

新 CFBRC module 第一候補:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinSecondDifferenceBridge.lean
```

fixed safe radius `R` について zero disk finset は有限である。

したがって Gate G の pointwise convergence を Finset sum へ上げる。

目標 theorem 概念形:

```lean
theorem tendsto_pascalCenteredXiZeroDiskMellinSecondDifferenceMoment
    {h : ℝ → ℂ} {a b R : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b)) :
    Tendsto
      (fun τ : ℝ =>
        pascalCenteredXiZeroDiskWeightedMoment
          (centeredMellinSecondDifferenceWeight h τ) R)
      (𝓝 0)
      (𝓝
        (pascalCenteredXiZeroDiskWeightedMoment
          (fun z => z ^ 2 * centeredMellinSpectralWeight h z) R)) := by
  ...
```

safe-radius hypothesisは finite sum limit 自体には不要な可能性がある。その場合は不要な hypothesis を追加しない。

Finset 上なので dominated convergence や infinite-series theorem を持ち込まない。

`Finset` の有限和 `Tendsto` composition を使う。

---

# 13. Gate J — fixed-Xi contour family

safe radius `R` に対し、Gate H の differentiabilityを既存 generic contour theoremへ接続する。

候補 theorem:

```lean
theorem pascalCenteredXiNormalizedMellinSecondDifferenceOuterContourMass_eq
    ...
    (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCenteredXiWeightedOuterContourMass
        (centeredMellinSecondDifferenceWeight h τ) R =
      -pascalCenteredXiZeroDiskWeightedMoment
        (centeredMellinSecondDifferenceWeight h τ) R := by
  ...
```

既存

```lean
pascalCenteredXiNormalizedWeightedOuterContourMass_eq
```

の thin application とする。

contour residue proof を再実装しない。

可能なら Gate I と組み合わせて normalized contour family の limitも置く。

概念形:

```lean
Tendsto
  (fun τ => normalized second-difference outer contour)
  (𝓝 0)
  (𝓝 (- weighted quadratic zero moment))
```

符号 `-` を落とさないこと。

---

# 14. Optional Gate K — finite interpolation contract だけを expose

XDP-007 への接続面として、固定 `R` について

```lean
(∀ z ∈ pascalCenteredXiZeroDiskFinset R,
  centeredMellinSpectralWeight h z = 1)
```

を仮定した場合、weighted quadratic moment が既存 second momentへ簡約する theoremを追加してよい。

概念形:

```lean
theorem pascalCenteredXiZeroDiskWeightedQuadraticMoment_eq_secondMoment_of_interpolates_one
    ... :
    pascalCenteredXiZeroDiskWeightedMoment
        (fun z => z ^ 2 * centeredMellinSpectralWeight h z) R =
      pascalCenteredXiZeroDiskSecondMoment R := by
  ...
```

これは **conditional adapter** に過ぎない。

この theorem をもって「interpolation が存在する」と主張してはいけない。

存在 theorem は XDP-007 の仕事である。

---

# 15. Mirror compatibility — optional but valuable

余力があれば、XDP-003 の mirror theoremと dilationを組み合わせ、plus / minus dilationが Mellin critical mirror により交換される構造を確認する。

期待構造は概念的に

```text
τ ↔ -τ
z ↦ -conj z
```

である。

ただし theorem statement は実計算で確定し、符号を推測で固定しない。

この層は XDP-006 completion gate ではない。

---

# 16. module/export 方針

第一候補:

```text
DkMath/Analysis/MellinCenteredDilation.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinSecondDifferenceBridge.lean
```

単体 Green 後、必要なら

```text
DkMath/Analysis.lean
DkMath/RH.lean
```

へ public import を追加する。

root import は module 単体が Green になる前に追加しない。

---

# 17. Build gate

最低限次を実施する。

```bash
cd lean/dk_math

lake env lean DkMath/Analysis/MellinCenteredDilation.lean
lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinSecondDifferenceBridge.lean

./lean-build.sh
./lean-test.sh
git diff --check
```

新規 module について次を確認する。

```bash
rg -n 'sorry|admit|axiom|native_decide' \
  DkMath/Analysis/MellinCenteredDilation.lean \
  DkMath/RH/CFBRC/PascalCenteredXiMellinSecondDifferenceBridge.lean
```

既存 unrelated `sorry` warning は区別して報告する。

---

# 18. XDP-006 completion criteria

最低限、次がすべて Green なら XDP-006 完了とする。

```text
[ ] pinned Mathlib scaling API audit
[ ] positive multiplicative dilation support/continuity transport
[ ] Mellin dilation exact scaling theorem
[ ] centered normalized dilation exact exp(τ z) theorem
[ ] symmetric second-difference exact kernel theorem
[ ] complex exponential second-difference kernel → z² pointwise
[ ] Q_{τ,h}(z) → z² H_h(z) pointwise
[ ] second-difference spectral weight differentiable
[ ] finite centered-Xi weighted zero moment limit
[ ] existing fixed-Xi normalized contourへの thin bridge
[ ] full build/test/diff-check Green
[ ] no new proof shortcuts
```

次は completion 条件に含めない。

```text
- H_h(z) → 1 の concrete approximate identity
- z² の unweighted exact/global Mellin realization
- Guinand–Weil explicit formula
- prime-side transport
- defect sign / vanishing
- RH
```

---

# 19. XDP-007 handoff

XDP-006 が成功すると、残る realization gap は明確に一つになる。

$$
H_{h_\nu}(z)
\longrightarrow 1
$$

を fixed finite Xi-zero set、または必要十分な compact spectral set 上で実現する positive compact-support Mellin family `h_ν` を構成することである。

その場合 XDP-006 の theorem と合成して

$$
Q_{\tau_\nu,h_\nu}(z)
\longrightarrow z^2
$$

を得る。

finite zero set 上の pointwise convergence で十分なら、uniform convergence を要求しないことで実装コストを下げられる。

XDP-007 の候補 route は次。

```text
A. x = 1 近傍の explicit positive compact-support approximate identity
B. log-variable approximate identity
C. fixed finite Xi-zero set に対する Mellin interpolation
```

Route A/B を primary とし、C は必要時の fallback とする。

---

# 20. 最終注意

XDP-006 は provider theorem ではない。

ここで証明するのは、Mellin multiplicative dilation が centered spectral plane 上で exponential multiplierを生み、その symmetric second difference が quadratic multiplierへ収束するという解析 Core である。

正確な到達点は

$$
Q_{\tau,h}(z)
\longrightarrow
z^2 H_h(z).
$$

`H_h(z)` を消して `z²` にする最後の一段を誤魔化さないこと。

この factor が残ること自体を、XDP-007 へ渡す **named realization gap** として記録すること。
