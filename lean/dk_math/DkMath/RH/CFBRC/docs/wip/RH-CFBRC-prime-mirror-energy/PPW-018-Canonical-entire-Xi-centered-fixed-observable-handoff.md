# PPW-018 — canonical entire Xi / centered fixed-observable bridge 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-017 complete Green
Lean toolchain: v4.32.2
```

PPW-017 までで、finite critical-mirror zero window `W_R` に対し、zero `ρ` ごとに frozen した holomorphic weight

```text
h_ρ(w) = (w - 1/2) * (criticalMirror ρ - 1/2)
```

を使うことで、normalized local contour charge が

```text
multiplicity(ρ) * |ρ - 1/2|²
```

を exact に読むこと、さらに finite sum が `CF2D.Vec.q2` radial mass と一致することまで Green になった。

しかし `h_ρ` は **zero `ρ` を知ってから作る weight** である。したがって PPW-017 の radial contour mass は、まだ zero list から独立した fixed observable ではない。

PPW-018 の目的は、この問題を無理に解いたことにせず、まず zeta の非自明零点を持つ **zero-independent / fixed / entire** な completed object を正本化することである。

Mathlib には既に、pole-subtracted completed zeta

```text
completedRiemannZeta₀
```

が entire であり、

```text
completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s
```

を満たす API がある。また

```text
completedRiemannZeta s
  = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)
```

も存在する。

そこで PPW-018 では、totalized division を global identity に持ち込まないため、次の entire polynomial-times-`completedRiemannZeta₀` object を定義する。

```text
Xi_Dk(s) := s * (1 - s) * completedRiemannZeta₀(s) - 1
```

` s ≠ 0, 1 ` では algebraically

```text
Xi_Dk(s) = s * (1 - s) * completedRiemannZeta(s)
```

である。

したがって open critical strip では `Xi_Dk(s) = 0` と `riemannZeta s = 0` が exact に同値となる。

さらに中心を `1/2` に移した

```text
Xi_centered(z) := Xi_Dk(1/2 + z)
```

は functional equation により even:

```text
Xi_centered(-z) = Xi_centered(z)
```

となる。

PPW-018 は、この **canonical entire centered Xi object** を zero-independent fixed observable の正本として確立する checkpoint である。

**重要:** PPW-018 では radial second moment を fixed contour から再構成しない。`Xi_centered` の evenness だけから RH を導かない。outer contour / argument principle / Xi multiplicity transport は次 checkpoint へ分離する。

---

## 2. 新規 module

```text
DkMath.RH.CFBRC.PascalCanonicalXiFixedObservableBridge
```

候補 file:

```text
lean/dk_math/DkMath/RH/CFBRC/PascalCanonicalXiFixedObservableBridge.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.PascalCriticalMirrorRadialContourCF2DBridge
import DkMath.RH.CFBRC.CompletedZetaBridge
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic
```

単体 Green 後に `DkMath/RH.lean` へ公開 import を追加する。

既存 PPW import 群と読みやすい位置に置くこと。今回 `RH.lean` の末尾付近へ単独追加する必要はない。

---

## 3. Mathlib / project API audit — exact current facts

### 3.1 Mathlib completed zeta

current Mathlib には次が存在する。

```lean
def completedRiemannZeta₀ (s : ℂ) : ℂ

def completedRiemannZeta (s : ℂ) : ℂ

theorem differentiable_completedZeta₀ :
    Differentiable ℂ completedRiemannZeta₀

lemma completedRiemannZeta_eq (s : ℂ) :
    completedRiemannZeta s =
      completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)

theorem completedRiemannZeta₀_one_sub (s : ℂ) :
    completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s

theorem completedRiemannZeta_one_sub (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s
```

`completedRiemannZeta₀` 自体を「zeta zeros の entire function」と読んではならない。これは pole subtraction を加えた entire function であり、zero locus は標準 zeta zero locus と同一とは限らない。

### 3.2 project completed-zeta bridge

既存:

```lean
theorem riemannZeta_eq_zero_iff_completedRiemannZeta_eq_zero
    {s : ℂ} (hs0 : s ≠ 0) (hGamma : Complex.Gammaℝ s ≠ 0) :
    riemannZeta s = 0 ↔ completedRiemannZeta s = 0

theorem completedRiemannZeta_eq_zero_of_nontrivialRiemannZetaZero ...
```

### 3.3 open critical strip

既存:

```lean
theorem nontrivialRiemannZetaZero_mem_openCriticalStrip
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    0 < s.re ∧ s.re < 1
```

および functional-equation reflection:

```lean
theorem riemannZeta_one_sub_eq_zero_of_nontrivialRiemannZetaZero ...
```

PPW-018 で functional equation をゼロから再実装しない。

---

## 4. Phase A — canonical entire Xi kernel

### 4.1 definition

```lean
/-- Entire pole-killed completed-zeta kernel used as the fixed PPW observable. -/
noncomputable def pascalRiemannXiKernel (s : ℂ) : ℂ :=
  s * (1 - s) * completedRiemannZeta₀ s - 1
```

名称に `Kernel` を付けるのは、古典文献の `ξ(s)` と normalization factor が異なり得るためである。zero locus / symmetry を利用するのが目的であり、古典的な `ξ` の正規化定数と同一だと主張しない。

### 4.2 entire

```lean
theorem differentiable_pascalRiemannXiKernel :
    Differentiable ℂ pascalRiemannXiKernel := by
  ...
```

`differentiable_completedZeta₀` と polynomial differentiability だけで閉じる。

可能なら

```lean
theorem analytic_pascalRiemannXiKernel :
    Analytic ℂ pascalRiemannXiKernel
```

相当の convenience theorem も current API が素直なら追加してよいが、必須ではない。

### 4.3 functional symmetry

```lean
@[simp] theorem pascalRiemannXiKernel_one_sub
    (s : ℂ) :
    pascalRiemannXiKernel (1 - s) = pascalRiemannXiKernel s := by
  ...
```

proof route:

```text
completedRiemannZeta₀_one_sub
(1 - s) * (1 - (1 - s)) = s * (1 - s)
ring
```

これは global theorem でよい。division を含まない entire definition だから、`s = 0,1` でも問題ない。

---

## 5. Phase B — ordinary completed zeta との exact bridge

### 5.1 off-pole identity

```lean
theorem pascalRiemannXiKernel_eq_mul_completedRiemannZeta
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    pascalRiemannXiKernel s =
      s * (1 - s) * completedRiemannZeta s := by
  ...
```

推奨 route:

1. `completedRiemannZeta_eq s` を rewrite。
2. `hs0` と `1 - s ≠ 0` を用意。
3. `field_simp` / `ring` で閉じる。

**停止線:** この theorem から仮定 `s ≠ 0,1` を消して global rewrite にしてはならない。Lean の division は totalized なので、`completedRiemannZeta_eq` の rational expression を pole 上で普通の cancellation として扱わない。

### 5.2 factor nonzero in open strip

薄い helper:

```lean
theorem ne_zero_of_pos_re
    {s : ℂ} (hs : 0 < s.re) : s ≠ 0
```

```lean
theorem ne_one_of_re_lt_one
    {s : ℂ} (hs : s.re < 1) : s ≠ 1
```

既存 theorem があれば再利用する。

### 5.3 GammaR nonzero on positive real half-plane

必要なら project-local helper:

```lean
theorem gammaR_ne_zero_of_pos_re
    {s : ℂ} (hs : 0 < s.re) :
    Complex.Gammaℝ s ≠ 0 := by
  ...
```

`Complex.Gammaℝ_eq_zero_iff` の witness は非正実軸側にあるため、positive real part と衝突させる。

既存 `gammaR_ne_zero_of_nontrivialRiemannZetaZero` より一般だが、duplicate theorem が既にあれば再利用する。

---

## 6. Phase C — open-strip zero equivalence

### 6.1 Xi kernel ↔ completed zeta

```lean
theorem pascalRiemannXiKernel_eq_zero_iff_completedRiemannZeta_eq_zero_of_openCriticalStrip
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    pascalRiemannXiKernel s = 0 ↔
      completedRiemannZeta s = 0 := by
  ...
```

`pascalRiemannXiKernel_eq_mul_completedRiemannZeta` と

```text
s ≠ 0
1 - s ≠ 0
```

から factor nonzero を取得し、`mul_eq_zero` で閉じる。

### 6.2 Xi kernel ↔ ordinary zeta

```lean
theorem pascalRiemannXiKernel_eq_zero_iff_riemannZeta_eq_zero_of_openCriticalStrip
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    pascalRiemannXiKernel s = 0 ↔
      riemannZeta s = 0 := by
  ...
```

proof route:

1. Phase C.1。
2. `riemannZeta_eq_zero_iff_completedRiemannZeta_eq_zero`。
3. `gammaR_ne_zero_of_pos_re hs0`。

方向を取り違えないこと。

### 6.3 nontrivial-zero packaging

必須 acceptance:

```lean
theorem pascalRiemannXiKernel_eq_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    pascalRiemannXiKernel s = 0 := by
  ...
```

`nontrivialRiemannZetaZero_mem_openCriticalStrip hs` と Phase C.2 を使用する。

可能ならさらに:

```lean
theorem pascalRiemannXiKernel_eq_zero_iff_nontrivialRiemannZetaZero_of_openCriticalStrip
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    pascalRiemannXiKernel s = 0 ↔
      NontrivialRiemannZetaZero s
```

を閉じる。

reverse packaging では:

- `riemannZeta s = 0`
- positive real part により trivial negative-even zero ではない
- `s.re < 1` により `s ≠ 1`

を組み立てる。

この iff が build complexity を大きくする場合、forward theorem を必須、iff を推奨に下げてよい。

---

## 7. Phase D — centered entire Xi

### 7.1 definition

```lean
noncomputable def pascalCenteredRiemannXiKernel (z : ℂ) : ℂ :=
  pascalRiemannXiKernel (criticalLineCenter + z)
```

ここで `z` は zero そのものではなく、critical line center `1/2` からの centered coordinate である。

### 7.2 entire

```lean
theorem differentiable_pascalCenteredRiemannXiKernel :
    Differentiable ℂ pascalCenteredRiemannXiKernel := by
  ...
```

### 7.3 evenness

PPW-018 の中心 theorem:

```lean
@[simp] theorem pascalCenteredRiemannXiKernel_neg
    (z : ℂ) :
    pascalCenteredRiemannXiKernel (-z) =
      pascalCenteredRiemannXiKernel z := by
  ...
```

数学的には

```text
1 - (1/2 + z) = 1/2 - z = 1/2 + (-z)
```

と `pascalRiemannXiKernel_one_sub` だけ。

proof では `criticalLineCenter` を展開し、必要なら `ring` で argument equality を作る。

### 7.4 nontrivial zero → centered Xi zero

```lean
theorem pascalCenteredRiemannXiKernel_sub_center_eq_zero_of_nontrivial
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    pascalCenteredRiemannXiKernel (s - criticalLineCenter) = 0 := by
  ...
```

これは fixed entire Xi が既存 PPW finite zero geometry を受け取る canonical bridge になる。

さらに functional reflection side:

```lean
theorem pascalCenteredRiemannXiKernel_neg_sub_center_eq_zero_of_nontrivial
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    pascalCenteredRiemannXiKernel (-(s - criticalLineCenter)) = 0 := by
  simpa using
    (pascalCenteredRiemannXiKernel_neg (s - criticalLineCenter)).trans ...
```

実際の Lean proof shape は調整してよい。

---

## 8. Phase E — fixed log-derivative observable preparation

outer contour は PPW-019 に送るが、固定 integrand の名前だけ今回用意してよい。

```lean
noncomputable def pascalCenteredXiNegLogDeriv (z : ℂ) : ℂ :=
  -logDeriv pascalCenteredRiemannXiKernel z
```

これは **zero-independent fixed function** である。

PPW-017 の

```text
ρ ↦ h_ρ
```

とは違い、`pascalCenteredXiNegLogDeriv` の定義に zero parameter は一切入らない。

current Mathlib API が素直なら、推奨 theorem:

```lean
theorem meromorphic_pascalCenteredXiNegLogDeriv :
    Meromorphic pascalCenteredXiNegLogDeriv
```

または `MeromorphicOn ... Set.univ`。

ただし exact theorem 名が合わなければ、ここは無理に blocking にしない。PPW-018 必須 checkpoint は entire Xi + zero equivalence + centered evenness まで。

### optional: oddness audit

`Xi_centered` が even なので、その log derivative は形式的には odd:

```text
(-logDeriv Xi_centered)(-z)
  = - [(-logDeriv Xi_centered)(z)]
```

となる。

これを current derivative API で clean に証明できるなら追加してよいが、PPW-018 mandatory ではない。

**注意:** totalized division を使う `logDeriv` でも、even function の derivative oddnessが global exact theorem として本当に通るかは Lean で確認すること。推測で theorem を置かない。

---

## 9. PPW-017 との接続 — 何が解決し、何が残るか

PPW-017:

```text
zero ρ
  ↓
frozen weight h_ρ
  ↓
local radial charge
  ↓
Σ mρ |ρ-1/2|²
  ↓
CF2D q2 radial mass
```

PPW-018:

```text
completedRiemannZeta₀
  ↓
canonical entire Xi_Dk
  ↓
center at 1/2
  ↓
fixed even entire Xi_centered
  ↓
fixed log-derivative candidate
```

したがって PPW-018 は、**zero-independent fixed global analytic object** を供給する。

しかしまだ

```text
frozen radial mass
  = fixed Xi outer contour observable
```

とは証明していない。

この equality を暗黙に仮定してはならない。

---

## 10. 今回やらないこと

PPW-018 では以下を実装しない。

```text
Xi log-derivative の outer contour integral
argument principle
residue sum over a large circle / rectangle
Xi zero multiplicity = zeta zero multiplicity の完全 transport
radial second moment の fixed-weight contour reconstruction
frozen h_ρ の単一 weight への統合
explicit formula
Li / Weil positivity
prime-side boundary identity
SecondMomentDefect = 0
HorizontalEnergy = 0
RiemannHypothesis の導出
```

---

## 11. Stop conditions / audit warnings

1. `completedRiemannZeta₀` の zero set を zeta zero set と同一視しない。
2. `pascalRiemannXiKernel_eq_mul_completedRiemannZeta` を `s = 0,1` へ無条件 extension しない。
3. `Xi_centered(-z) = Xi_centered(z)` から `z = -z` を結論しない。even function は off-center zero pair `±z` を普通に持てる。
4. functional symmetry `s ↦ 1-s` は critical-line reflection `s ↦ 1-conj(s)` と同じ写像ではない。
5. centered evenness は RH ではない。
6. fixed entire Xi が得られたことだけで PPW-017 frozen radial mass が fixed contour observable になったと主張しない。
7. `logDeriv` は zero で pole signature を持つ meromorphic objectであり、entire ではない。
8. zero multiplicity transport を証明していない段階で Xi contour residue を既存 `riemannZetaZeroMultiplicity` と同一視しない。
9. finite PHZ cutoff の critical-strip convergence は依然として未証明。Xi を導入しても PPW-011 の `Re(s) > 1` convergence domain は自動で広がらない。
10. 新しい RH-equivalent provider 名を置いただけで研究前進としない。

---

## 12. Build / acceptance criteria

最低限:

```text
lake build DkMath.RH.CFBRC.PascalCanonicalXiFixedObservableBridge
lake build DkMath.RH
./lean-build.sh DkMath.RH.CFBRC.PascalCanonicalXiFixedObservableBridge
git diff --check
```

新規 module に

```text
sorry
axiom
admit
```

を追加しない。

必須 acceptance theorem 群:

```lean
pascalRiemannXiKernel

differentiable_pascalRiemannXiKernel
pascalRiemannXiKernel_one_sub

pascalRiemannXiKernel_eq_mul_completedRiemannZeta
pascalRiemannXiKernel_eq_zero_iff_completedRiemannZeta_eq_zero_of_openCriticalStrip
pascalRiemannXiKernel_eq_zero_iff_riemannZeta_eq_zero_of_openCriticalStrip
pascalRiemannXiKernel_eq_zero_of_nontrivialRiemannZetaZero

pascalCenteredRiemannXiKernel
differentiable_pascalCenteredRiemannXiKernel
pascalCenteredRiemannXiKernel_neg
pascalCenteredRiemannXiKernel_sub_center_eq_zero_of_nontrivial
```

推奨だが non-blocking:

```lean
pascalRiemannXiKernel_eq_zero_iff_nontrivialRiemannZetaZero_of_openCriticalStrip
pascalCenteredXiNegLogDeriv
meromorphic_pascalCenteredXiNegLogDeriv
centered log-derivative oddness theorem
```

---

## 13. PPW-018 の意味

PPW-017 の問題は、radial mass を読む contour weight が zero-dependent だったことである。

PPW-018 では、その radial weight を魔法のように fixed weight へ変換するのではなく、まず標準 completed-zeta data だけから

```text
zero-independent
entire
functional-equation symmetric
critical-line centered
```

な一つの fixed analytic objectを構築する。

これで PPW-019 の問いを正確に次へ限定できる。

```text
fixed centered Xi log derivative
  ↓
outer contour / argument principle
  ↓
finite centered zero moments
  ↓
既存 zeta multiplicity / PPW window との exact transport
```

その後初めて、fixed holomorphic momentsだけで radial `q2` massを回収できるのか、または追加の non-holomorphic / pair-orbit / boundary provider が本質的に必要なのかを監査する。

PPW-018 はそのための canonical fixed-observable foundation である。
