# PPW-015 — local circle charge / finite contour mass bridge 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-014 complete Green
Lean toolchain: v4.32.2
```

PPW-014 までで、任意の Riemann-zeta zero `ρ` に対し theorem-facing multiplicity

```text
riemannZetaZeroMultiplicity ρ : ℕ
```

が定義され、`m = riemannZetaZeroMultiplicity ρ` とすると punctured neighborhood で

```text
(w - ρ) * pascalZetaNegLogDeriv w  →  -m
```

が Green になった。

また finite critical-mirror window には

```text
pascalCriticalMirrorZeroWindowMultiplicity R
```

として multiplicity の有限和が存在する。

PPW-015 の目的は、この局所極限を **Mathlib の標準 `circleIntegral` 規約に固定し、各 zeta zero の局所 contour charge を exact に `-2πi * multiplicity` とすること**、さらに有限 window 内の各局所 circle charge を有限和として集約することである。

この checkpoint では single outer contour / argument principle / residue theorem の一般形へはまだ進まない。

重要な分離:

```text
PPW-015 local contour mass
  = 各零点の小円を別々に積分して足した量

PPW-016 global contour accounting
  = 一つの外側 contour へ変形・集約する段階
```

したがって PPW-015 では局所円同士の pairwise disjointness も、window 全体を囲む一つの contour も必須ではない。

---

## 2. 新規 module

```text
DkMath.RH.CFBRC.PascalZetaLocalCircleChargeBridge
```

候補 file:

```text
lean/dk_math/DkMath/RH/CFBRC/PascalZetaLocalCircleChargeBridge.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.PascalZetaZeroMultiplicityBridge
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic
```

単体 Green 後に `DkMath/RH.lean` へ公開 import を追加する。

---

## 3. contour convention — 今回ここで固定する

PPW-014 では contour convention を未指定として local circle integral を見送った。

PPW-015 では独自 contour DSL を作らず、**Mathlib `Complex.circleIntegral` の標準向き・標準正規化を PPW の正本 convention とする**。

Mathlib `CauchyIntegral.lean` の仕様では、中心 `c` の円について

```text
∮ (z - c)⁻¹ • f(z) dz = 2π i y
```

が、punctured neighborhood で `f(z) → y` のとき成立する theorem が既に存在する。

利用候補:

```lean
Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable
Complex.circleIntegral.integral_sub_center_inv
Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
```

実装前に必ず `#check` で current toolchain の exact signature を確認すること。

この convention により sign は自動的に固定される。PPW target は `-logDeriv ζ` なので、zeta zero multiplicity `m` の局所 charge は

```text
-2π i m
```

となる。

---

## 4. Phase A — isolating radius predicate

局所 circle theorem を安全に使うため、zero `ρ` の周りで

- radius は正
- `1` を含まない
- `ρ` 以外の zeta zero を含まない

という条件を theorem-facing predicate にする。

候補:

```lean
def IsPascalZetaIsolatingRadius (ρ : ℂ) (r : ℝ) : Prop :=
  0 < r ∧
    Metric.closedBall ρ r ⊆ ({1}ᶜ : Set ℂ) ∧
    ∀ z ∈ Metric.closedBall ρ r,
      z ≠ ρ → riemannZeta z ≠ 0
```

名称はより repository convention に合うものへ変更可。

### existence

必須 theorem:

```lean
theorem exists_isPascalZetaIsolatingRadius
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    ∃ r : ℝ, IsPascalZetaIsolatingRadius ρ r
```

推奨 proof route:

1. `ne_one_of_mem_riemannZetaZeros hρ` から `ρ ≠ 1`。
2. `isDiscrete_riemannZetaZeros` または isolated-zero API から、`ρ` の sufficiently small neighborhood に他の zeta zero が無いことを得る。
3. `ρ ≠ 1` から sufficiently small ball が `{1}ᶜ` に入ることを得る。
4. 二つの neighborhood を intersect し、その内部に positive-radius closed ball を選ぶ。

### fallback route

PPW-014 の local factorization

```lean
ζ(w) = (w - ρ)^m * g(w),   g(ρ) ≠ 0
```

から `g` が近傍で非零となるため、factorization が成立する sufficiently small ball を選び、punctured ball 上で `ζ(w) ≠ 0` を直接示してもよい。

この route なら `isDiscrete_riemannZetaZeros` に依存しなくてよい。

**禁止:** radius を具体的数値で固定しない。zero spacing に uniform lower bound は無い。

---

## 5. Phase B — chosen local radius

finite window 上で各 zero の局所円を有限和に入れるため、existence theorem から noncomputable choice を一度だけ package する。

候補:

```lean
noncomputable def pascalZetaIsolatingRadius (ρ : ℂ) : ℝ :=
  if hρ : ρ ∈ riemannZetaZeros then
    Classical.choose (exists_isPascalZetaIsolatingRadius hρ)
  else 1
```

zero 上の spec:

```lean
 theorem pascalZetaIsolatingRadius_spec
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    IsPascalZetaIsolatingRadius ρ (pascalZetaIsolatingRadius ρ)
```

必要に応じて薄い helper:

```lean
theorem pascalZetaIsolatingRadius_pos ...
theorem pascalZetaIsolatingRadius_closedBall_subset ...
theorem riemannZeta_ne_zero_of_mem_isolating_puncturedBall ...
```

`Classical.choose` を後続 theorem で直接展開し続けないこと。spec theorem を正本 API とする。

---

## 6. Phase C — local residue kernel

PPW-014 theorem を circle-integral API へそのまま渡せる形に名前付けしてよい。

```lean
noncomputable def pascalZetaLocalResidueKernel
    (ρ w : ℂ) : ℂ :=
  (w - ρ) * pascalZetaNegLogDeriv w
```

薄い theorem:

```lean
theorem tendsto_pascalZetaLocalResidueKernel
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    Tendsto (pascalZetaLocalResidueKernel ρ)
      (𝓝[≠] ρ)
      (𝓝 (-(riemannZetaZeroMultiplicity ρ : ℂ)))
```

proof は PPW-014 の

```lean
tendsto_mul_pascalZetaNegLogDeriv_zeroMultiplicity
```

を再利用するだけ。

この kernel は punctured point で

```text
pascalZetaNegLogDeriv w
  = (w - ρ)⁻¹ * pascalZetaLocalResidueKernel ρ w
```

となる。

候補 theorem:

```lean
theorem pascalZetaNegLogDeriv_eq_inv_mul_localResidueKernel
    {ρ w : ℂ} (hw : w ≠ ρ) :
    pascalZetaNegLogDeriv w =
      (w - ρ)⁻¹ * pascalZetaLocalResidueKernel ρ w
```

これは circle 上の integrand normalization に使う。

---

## 7. Phase D — punctured disk での regularity

Mathlib の Cauchy-integral theorem が要求する regularity を、chosen isolating radius 上で package する。

最低限必要になる性質は current theorem signature に合わせること。

概念的には:

```text
on closedBall ρ r \ {ρ}:
  pascalZetaLocalResidueKernel ρ is continuous

on ball ρ r \ {ρ}:
  pascalZetaLocalResidueKernel ρ is complex differentiable

as w → ρ, w ≠ ρ:
  kernel → -m
```

ここで `r` は `IsPascalZetaIsolatingRadius ρ r`。

regularity route は二つある。

### Route 1 — quotient directly

punctured ball では

```text
riemannZeta w ≠ 0
```

かつ `riemannZeta` は analytic なので、

```text
pascalZetaNegLogDeriv = - deriv ζ / ζ
```

は analytic / differentiable。`w - ρ` を掛けても analytic。

### Route 2 — PPW-014 local factorization

局所的に

```text
kernel(w) = -m - (w - ρ) * logDeriv g(w)
```

と書き、`g` が非零の neighborhood で analytic とする。

proof plumbing が短い方を採用する。

新しい Laurent series framework は作らない。

---

## 8. Phase E — local circle charge theorem

PPW-015 の主定理。

Mathlib `circleIntegral` の exact syntax は `#check` 後に合わせる。

概念目標:

```lean
theorem circleIntegral_pascalZetaNegLogDeriv_eq_neg_two_pi_I_mul_multiplicity
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    Complex.circleIntegral pascalZetaNegLogDeriv
      ρ (pascalZetaIsolatingRadius ρ) =
      -(2 * Real.pi * Complex.I) *
        (riemannZetaZeroMultiplicity ρ : ℂ)
```

実際の `circleIntegral` argument order / notation は current Mathlib に合わせること。

### 推奨 route

`f(w) := pascalZetaLocalResidueKernel ρ w` とする。

PPW-014 より

```text
f(w) → -m
```

が punctured center で成立する。

Mathlib theorem

```text
circleIntegral_sub_center_inv_smul_..._of_tendsto
```

へ

```text
c = ρ
R = pascalZetaIsolatingRadius ρ
y = -(m : ℂ)
```

を渡す。

circle 上では radius positivity により `w ≠ ρ` なので

```text
(w - ρ)⁻¹ * f(w) = pascalZetaNegLogDeriv w
```

へ integrand を rewrite する。

結果:

```text
∮ pascalZetaNegLogDeriv(w) dw
  = 2πi * (-m)
```

を normalize して

```text
-2πi * m
```

とする。

### alternative theorem shape

chosen radius を theorem statement に埋め込むことで proof が重くなる場合、まず任意 isolating radius 版を正本としてよい。

```lean
theorem circleIntegral_pascalZetaNegLogDeriv_eq_of_isolatingRadius
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros)
    {r : ℝ} (hr : IsPascalZetaIsolatingRadius ρ r) :
    ... = -(2 * Real.pi * Complex.I) *
      (riemannZetaZeroMultiplicity ρ : ℂ)
```

その後 chosen-radius corollary を付ける。

この形の方が再利用性は高い。

---

## 9. Phase F — normalized local contour charge

`2πi` を除いた zero-counting quantityを作ると PPW-016 で扱いやすい。

候補:

```lean
noncomputable def pascalZetaNormalizedLocalCircleCharge
    (ρ : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    Complex.circleIntegral pascalZetaNegLogDeriv
      ρ (pascalZetaIsolatingRadius ρ)
```

zero 上の theorem:

```lean
@[simp] theorem pascalZetaNormalizedLocalCircleCharge_eq_neg_multiplicity
    {ρ : ℂ} (hρ : ρ ∈ riemannZetaZeros) :
    pascalZetaNormalizedLocalCircleCharge ρ =
      -(riemannZetaZeroMultiplicity ρ : ℂ)
```

`2 * π * I ≠ 0` の処理は `Real.pi_pos` と `Complex.I_ne_zero` 等を使う。

正規化を実装するかどうかは任意だが、PPW-016 では便利。

---

## 10. Phase G — finite window local contour mass

### 10.1 actual local-circle sum

finite window 内の各 zero の chosen circle integral を足す。

候補:

```lean
noncomputable def pascalCriticalMirrorZeroWindowLocalContourMass
    (R : ℝ) : ℂ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    Complex.circleIntegral pascalZetaNegLogDeriv
      ρ (pascalZetaIsolatingRadius ρ)
```

ここで各 circle が mutually disjoint である必要はない。

これは一つの contour ではなく、**独立な局所 contour charge の有限和**である。

### 10.2 exact multiplicity mass theorem

必須 theorem:

```lean
theorem pascalCriticalMirrorZeroWindowLocalContourMass_eq
    (R : ℝ) :
    pascalCriticalMirrorZeroWindowLocalContourMass R =
      -(2 * Real.pi * Complex.I) *
        (pascalCriticalMirrorZeroWindowMultiplicity R : ℂ)
```

proof route:

1. `Finset.sum_congr`。
2. 各 `ρ ∈ windowFinset` から nontrivial zero membership を取り出す。
3. `nontrivialRiemannZetaZero_mem_riemannZetaZeros`。
4. Phase E local circle theorem。
5. finite sum の scalar factor を外へ出す。
6. Nat cast of finite sum を normalize。

### 10.3 normalized version

任意:

```lean
theorem pascalCriticalMirrorZeroWindowNormalizedLocalContourMass_eq
    (R : ℝ) :
    (2 * Real.pi * Complex.I)⁻¹ *
      pascalCriticalMirrorZeroWindowLocalContourMass R =
      -(pascalCriticalMirrorZeroWindowMultiplicity R : ℂ)
```

これが zero-counting charge の最も扱いやすい形。

---

## 11. Phase H — PPW-013 mirror energy との同一 window API

PPW-015 では contour mass と mirror energy の等式を作らない。

ただし同じ `pascalCriticalMirrorZeroWindowFinset R` 上の量であることを明示する convenience theorem / structure は作ってよい。

たとえば定義だけ:

```lean
structure PascalCriticalMirrorWindowObservables (n : ℕ) (R : ℝ) where
  mirrorEnergy : ℝ
  multiplicity : ℕ
  localContourMass : ℂ
```

は **不要**。単なる packaging のために新 structure を増やさない。

既存三量

```text
pascalCriticalMirrorZeroWindowEnergy n R
pascalCriticalMirrorZeroWindowMultiplicity R
pascalCriticalMirrorZeroWindowLocalContourMass R
```

をそのまま正本とする。

必要なら theorem コメントで関係を記述するだけにする。

---

## 12. 今回やらないこと

PPW-015 では以下を実装しない。

```text
一つの outer contour による window 全体の積分
argument principle の一般 theorem
residue theorem の一般 framework
局所小円の pairwise disjoint canonical choice
window boundary に zero が無い radius sequence の構成
critical strip で finite PHZ cutoff の contour convergence
finite PHZ の contour integral = zeta log-derivative contour integral
prime-side sum から mirror energy が 0 になる theorem
∀ R, mirror energy = 0
RiemannHypothesis
```

特に PPW-011 の

```text
finite PHZ → -ζ'/ζ
```

は `re(s) > 1` の pointwise limit である。

そこから critical-strip contour 上で cutoff と integral を交換してはいけない。

---

## 13. Stop conditions / audit warnings

1. `pascalZetaNegLogDeriv` の local circle integral を finite PHZ cutoff の local circle integralと同一視しない。
2. local contour mass が multiplicity を数えることから horizontal mirror energy が 0 と結論しない。
3. multiplicity は zero の「個数」ではなく重複度。window cardinality と混同しない。
4. local circles の有限和を一つの outer contour integral と呼ばない。
5. local circles が重なっていても Phase G の独立有限和自体は定義できるが、contour deformationには使わない。
6. isolating radius に uniform positive lower bound を仮定しない。
7. Mathlib `circleIntegral` の orientation / normalization を独自に反転しない。
8. `2πi` の符号を手計算だけで固定せず、Mathlib theorem の向きに従う。
9. zeta zero の totalized quotient point value を residue として使わない。
10. 新しい RH-equivalent zero-energy theorem を independent progress と呼ばない。

---

## 14. Build / acceptance criteria

最低限:

```text
lake build DkMath.RH.CFBRC.PascalZetaLocalCircleChargeBridge
lake build DkMath.RH
git diff --check
```

可能なら project wrapper build も実行。

新規 module に

```text
sorry
axiom
admit
```

を追加しない。

### 必須 acceptance theorem

名称は多少変更可だが、内容として以下を Green にする。

```lean
exists_isPascalZetaIsolatingRadius
pascalZetaIsolatingRadius_spec

tendsto_pascalZetaLocalResidueKernel

circleIntegral_pascalZetaNegLogDeriv_eq_of_isolatingRadius
-- または chosen radius 専用の同値 theorem

pascalCriticalMirrorZeroWindowLocalContourMass_eq
```

`pascalZetaNormalizedLocalCircleCharge_eq_neg_multiplicity` は推奨。

PPW-015 complete 判定には

```text
任意 multiplicity zero の local circle charge = -2πi * multiplicity
有限 window の local circle charge sum = -2πi * total multiplicity
```

の二段が Green であることを要求する。

---

## 15. PPW-015 の意味

これまでの chain は

```text
Pascal prime-power data
  ↓
von Mangoldt Λ
  ↓
-logDeriv ζ
  ↓
zeta zero local pole
  ↓
analytic multiplicity
```

までだった。

PPW-015 で初めて、この analytic multiplicity を **実際の oriented contour observable** に変換する。

```text
zeta zero ρ
  ↓
local multiplicity mρ
  ↓
local circle integral of -ζ'/ζ
  ↓
-2πi mρ
  ↓
finite window local contour mass
  ↓
-2πi Σ mρ
```

これにより PPW-016 では、局所小円の総和を一つの外側 boundary contour へ変形できる条件を formalize し、finite-window argument-principle 型 accounting を作る準備が整う。

PPW-016 で初めて問うべき本題は、**その outer boundary observable を prime-side / completed-zeta / CFBRC mirror data とどう結びつけるか**である。
