# XDP-002 — Classical Weil / Mathlib adapter audit result

作成日: 2026-08-12
対象 checkout: `/home/deskuma/develop/lean/dkmath/lean/dk_math`
Lean / Mathlib: repository の pinned toolchain / `.lake/packages/mathlib`

## 0. 判定要約

XDP-002 の結論は **Route M — Mellin-first** を primary route とすることである。

理由は次のとおり。

1. pinned Mathlib に Mellin の定義、収束 predicate、`x ↦ x⁻¹`、Mellin/Fourier
   変換、逆変換が揃っている。
2. `SchwartzMap` の Fourier transform と Plancherel も利用できるが、
   centered-Xi の zero-side weight を multiplicative test function から exact に
   取り出すには、まず `h : ℝ → ℂ` on `Ioi 0` とその Mellin transform を固定する
   方が convention を追跡しやすい。
3. Mathlib には von Mangoldt L-series と `-ζ'/ζ` の bridge がある。これは
   Route M の prime-side endpoint として再利用できる。
4. Guinand--Weil explicit formula、classical Weil quadratic functional、Li
   coefficients の zeta-specific theorem は pinned tree の検索結果と compile
   probe の範囲では見つからない。したがって XDP-003 では、まず Mellin-side
   admissible test data と mirror/conjugation lemma を実装し、その後に explicit
   formula adapter を別段階で設計する。

これは provider theorem ではない。`RiemannHypothesis`、
`PascalCenteredXiFixedDefectVanishesOnSafeRadii`、または
`pascalCenteredXiFixedSecondMomentDefectFunctional R = 0` は仮定も証明もしていない。

## 1. XDP-001 Green API の継承

XDP-001 の正本は次の module である。

```text
DkMath/RH/CFBRC/PascalCenteredXiWeilMirrorDefectBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiFixedSecondMomentDefectBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiOuterContourResidueBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiRadialLayerCakeOuterCountBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiGlobalZeroDiskBridge.lean
DkMath/RH/CFBRC/CriticalMirrorGeometry.lean
DkMath/RH/CFBRC/CriticalMirrorZeroBridge.lean
```

固定されている有限構造は次である。

```text
c(s) = centeredComplex s
m(s) = criticalMirror s
c(m(s)) = -conj(c(s))

FiniteWeilStylePair R = - centered second moment
FixedXi defect R = radial mass - Re(FiniteWeilStylePair R)  [safe R]
FixedXi defect R = anti-mirror energy R                         [safe R]
```

ここで `FiniteWeilStylePair` は finite zero-window sum であり、classical Weil
functional の定義ではない。XDP-002 ではこの API を再証明せず、将来の generic
test-function API の specification input として扱う。

## 2. Classical / DkMath / Mathlib convention dictionary

### 2.1 Dictionary

| 項目 | DkMath / pinned Mathlib | classical adapter で固定すべき convention |
|---|---|---|
| critical reflection | `criticalMirror s = (1 - s.re) + s.im I`, すなわち `conj (1-s)` | zero-side の reflection は `s ↦ 1-s` と complex conjugation を別々に記録し、`1 - conj s` と混同しない |
| centered coordinate | `centeredComplex s = s - 1/2` | Weil-side の zero weight に入れる前に `s - 1/2` の shift を明示する |
| centered mirror | `c(m(s)) = -conj(c(s))` | reflection/conjugation による quadratic pairing の符号をこの identity から導出する |
| multiplicative involution | Mathlib の `mellin_comp_inv` は `mellin (fun t => f t⁻¹) s = mellin f (-s)` | 候補は `h∨(x) = x⁻¹ * conj (h x⁻¹)`。この重み・conjugation・measure convention は XDP-003 で theorem にする |
| Mellin kernel | `mellin f s = ∫_{Ioi 0} t^(s-1) • f t` | `t^(s-1)`、`Ioi 0`、complex `cpow` を採用し、文献側の `dx/x` 表記との変換を明示する |
| Fourier kernel | pinned Mathlib の real Fourier は `exp(-2π i ⟪x,ξ⟫)` | `2π` を省略しない。Mellin/Fourier bridge の frequency は `s.im / (2π)` |
| inverse Fourier | `Real.fourierInv_eq_fourier_comp_neg` | inverse は reflection `x ↦ -x` を含む。conjugation symmetry は別 lemma として組む |
| zeta functional equation | `completedRiemannZeta_one_sub`, `completedRiemannZeta₀_one_sub` | completed function の equality と ordinary `riemannZeta_one_sub` の gamma/pole factors を区別する |
| prime side | `ArithmeticFunction.vonMangoldt`、`LSeries ... = -ζ'/ζ` on `1 < s.re` | `Λ(n)` は prime と prime-power の両方を含む。prime-only sum に短絡しない |

### 2.2 Classical source boundary

Lagarias の論文は Li coefficients を Weil quadratic functional の値と関連付け、
その positivity を RH criterion として扱う。しかしこれは XDP-001 の finite
zero-window pairing が classical functional と同一であることを意味しない。
classical source は convention と target specification の資料としてのみ使い、
Lean fact や axiom として輸入しない。

参照した一次資料は次である。

- [Lagarias, *Li Coefficients for Automorphic L-Functions*, Ann. Inst. Fourier 57
  (2007), 1689--1740](https://numdam.org/articles/10.5802/aif.2311/)
- [arXiv:math/0404394](https://arxiv.org/abs/math/0404394)
- 同論文の bibliography にある Weil、Guinand、Bombieri--Lagarias の各 reference

この資料から確定するのは「classical Weil functional / Li coefficient は別の
test-function と global zero-side machinery を持つ」という研究上の位置付けであり、
XDP-001 の名称を classical theorem の名称へ昇格させる根拠ではない。

## 3. Audit B — pinned Mathlib Mellin surface

### 3.1 Compile-confirmed present API

次の scratch file を `/tmp/xdp002_api_probe.lean` に作成し、

```bash
cd /home/deskuma/develop/lean/dkmath/lean/dk_math
lake env lean /tmp/xdp002_api_probe.lean
```

で compile 確認した。

```lean
MellinConvergent
HasMellin
mellin
mellinInv
mellin_cpow_smul
mellin_comp_inv
mellin_differentiableAt_of_isBigO_rpow
mellin_eq_fourier
mellinInv_mellin_eq
mellin_inversion              -- deprecated alias, present
```

### 3.2 Exact shapes relevant to XDP-003

`MellinConvergent` は、型 `E` に `[NormedAddCommGroup E] [NormedSpace ℂ E]` を
要求し、次を表す。

```lean
IntegrableOn
  (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t)
  (Set.Ioi 0)
```

`mellin` の kernel は `t ^ (s - 1)` であり、`mellinInv` は

```lean
(1 / (2 * π)) • ∫ y,
  (x : ℂ) ^ (-(σ + y * I)) • f (σ + y * I)
```

である。したがって `2π` と exponent の符号は XDP-003 の theorem statement に
残す必要がある。

`mellin_comp_inv` は次だけを与える。

```lean
mellin (fun t => f t⁻¹) s = mellin f (-s)
```

これは `x⁻¹ * conj (h x⁻¹)` の Mellin transform、complex conjugation、
critical-line shift までを一度に与える theorem ではない。そこには少なくとも
以下の追加 lemma が必要である。

```text
1. x⁻¹ の実数 scalar と complex scalar multiplication の整理
2. `star` と set integral / Bochner integral の交換
3. `s ↦ 1 - s` または centered coordinate への shift
4. Ioi 0 上の inverse substitution と integrability transport
```

`mellin_differentiableAt_of_isBigO_rpow` は `Ioi 0` 上の local integrability と、
zero / infinity での二つの `IsBigO` 条件を要求する。単に `SchwartzMap` である
ことから自動的に XDP の desired holomorphicity theorem が得られる、とは判定
しない。

`mellin_eq_fourier` は

```text
u ↦ exp(-s.re * u) • f (exp(-u))
```

の Fourier transform を `s.im / (2π)` で評価する。これは Route M と Route S の
接続に十分な primitive だが、zeta explicit formula 自体ではない。

`mellinInv_mellin_eq` / `mellin_inversion` の仮定は、`x > 0`、Mellin convergence、
vertical integrability of `mellin f`、`ContinuousAt f x` である。XDP-003 はこの
theorem の hypotheses を満たす test family を明示的に持つ必要がある。

## 4. Audit C — Fourier / Schwartz surface

### 4.1 Compile-confirmed present API

次の名前は compile probe で確認した。

```lean
SchwartzMap.fourierTransformCLM
SchwartzMap.fourierTransformCLE
SchwartzMap.integral_bilin_fourier_eq
SchwartzMap.integral_inner_fourier_fourier
FourierPair.fourierInv_fourier_eq
FourierInvPair.fourier_fourierInv_eq
Real.fourierInv_eq_fourier_comp_neg
```

`SchwartzMap` の Fourier surface は、実有限次元 inner-product space、measurable /
Borel structure、必要な complete normed structures を要求する。従って
`SchwartzMap ℝ ℂ` は候補 test class にできるが、それだけで classical Weil
admissibility が得られるわけではない。

### 4.2 Normalization and available identities

pinned Mathlib の real Fourier convention は次である。

```text
𝓕 f ξ = ∫ x, exp(-2π i ⟪x, ξ⟫) • f x
```

`Real.fourierInv_eq_fourier_comp_neg` は inverse transform を `x ↦ -x` での
Fourier transform として表す。`SchwartzMap.integral_inner_fourier_fourier` は
sesquilinear inner product の Plancherel identity を与える。

このため Fourier 側は以下を提供する。

```text
present: transform, inverse, reflection, self-adjoint bilinear identity,
         sesquilinear Plancherel
missing: zeta zero evaluation, Weil test-function class, explicit-formula
         decomposition, centered-Xi defect evaluation
```

### 4.3 Compact support bridge

Mathlib Basic には次の general constructor がある。

```lean
HasCompactSupport.toSchwartzMap
```

これは `HasCompactSupport f` と `ContDiff ℝ ∞ f` から Schwartz map を作る。
ただし、XDP-003 に必要な「positive multiplicative variable 上の smooth radial
cutoff」「support が `R - ε` と `R + ε` の間にあること」「Mellin-side reflection
compatibility」を一つにまとめた constructor は確認できなかった。したがって
compact support から classical admissibility へ直接ジャンプする API は未提供と
分類する。

## 5. Audit D — arithmetic / zeta surface

### 5.1 Mathlib の present surface

次の theorem は compile probe で確認した。

```lean
ArithmeticFunction.LSeriesSummable_vonMangoldt
ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
```

正確な bridge は `1 < s.re` のもとで

```lean
LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s
  = - deriv riemannZeta s / riemannZeta s
```

である。

von Mangoldt 側には次も存在する。

```lean
ArithmeticFunction.vonMangoldt_apply
ArithmeticFunction.vonMangoldt_apply_pow
ArithmeticFunction.vonMangoldt_apply_prime
ArithmeticFunction.vonMangoldt_eq_zero_iff
ArithmeticFunction.vonMangoldt_ne_zero_iff
ArithmeticFunction.vonMangoldt_sum
```

### 5.2 DkMath の existing bridge

次の DkMath module は既に上記 API を利用しているため再実装しない。

```text
DkMath/RH/CFBRC/PascalVonMangoldtLSeriesBridge.lean
DkMath/RH/CFBRC/PascalPrimePowerCanonicalFold.lean
DkMath/RH/CFBRC/PascalPrimePowerModeBridge.lean
```

特に `PascalVonMangoldtLSeriesBridge` には、finite PPW cutoff から von Mangoldt
L-series への partial-sum convergence と、safe half-plane での `-ζ'/ζ` limit が
既にある。XDP-003 以降ではこの module を prime-side entry point にする。

### 5.3 Functional equation / gamma boundary

Mathlib には次の zeta API がある。

```lean
completedRiemannZeta_one_sub
completedRiemannZeta₀_one_sub
riemannZeta_one_sub
```

後者は gamma / cosine / power factors を含む ordinary zeta relation であり、
completed zeta の reflection equality と同じ theorem ではない。explicit-formula
adapter では pole term、gamma/archimedean term、zero term を分ける必要がある。
XDP-002 ではその分解を新規に formalize していない。

## 6. Audit E — explicit-formula availability

### 6.1 Search procedure

最低限、次の検索を pinned tree に対して実行した。

```bash
rg -n "MellinConvergent|HasMellin|mellin_inversion|mellin_eq_fourier" .lake/packages/mathlib/Mathlib
rg -n "fourierTransformCLM|fourierTransformCLE|integral_inner_fourier_fourier|integral_bilin_fourier" .lake/packages/mathlib/Mathlib
rg -n "LSeries_vonMangoldt_eq_deriv_riemannZeta_div|vonMangoldt|riemannZeta.*deriv|logDeriv" .lake/packages/mathlib/Mathlib
rg -n -i "\\b(Weil|Guinand|Li coefficient|LiCoefficient|explicit formula|zero sum)\\b" .lake/packages/mathlib/Mathlib
```

同義語として `functional equation`、`zero-side`、`prime explicit`、
`RiemannHypothesis` も確認した。

### 6.2 Classification

判定は **C: 必要な Mellin/Fourier/LSeries 部品はあるが、Guinand--Weil
explicit formula theorem 自体はない** である。

Mathlib に generic Fourier inversion / Plancherel や Dirichlet L-series machinery
が存在することは確認できる。しかし次の zeta-specific theorem は確認できない。

```text
- Guinand--Weil explicit formula
- Weil quadratic functional for ζ
- Li coefficient / Li criterion theorem
- theorem joining a zero sum, prime-power sum, pole term, and archimedean term
```

これは「Mathlib 全体に数学的に絶対存在しない」という主張ではない。今回の
pinned tree に、上記の theorem surface として利用できる declaration が見つから
なかった、という repository-scoped audit result である。

従って XDP-003 で必要な explicit-formula theorem は新規 research formalization
となり、既存 API の単純な adapter だけでは閉じない。

## 7. Hard-cutoff obstruction

### H1 — hard radial zero-window localization

XDP-001 の zero-side quantity は概念的に

```text
1_{|ρ - 1/2| ≤ R}
```

を含む有限 window である。classical explicit formula が要求するのは通常、
admissible test function の Mellin/Fourier transform を zero で評価した重みであり、
この hard indicator がその transform の像であることは現在の API からは得られない。

従って H1 は

```text
finite hard zero-window localization → smooth/admissible transform
```

という adapter obstruction である。RH の obstruction でも、hard cutoff が不可能
だという定理でもない。

### H2 — unbounded centered coordinate

`c(s) = s - 1/2` は zero-side で無限遠に減衰しない。したがってこれをそのまま
classical admissible transform と宣言することはできない。`c(s)` を zero-side の
factor として使うには、例えば Mellin transform の微分、compactly supported
test-function の moment、または regularized transform を設計する必要がある。

H2 も RH の obstruction ではない。admissible test class への factorization が
未設計であるという adapter obstruction である。

H1 と H2 は別問題である。smooth cutoff を作っても centered factor の growth は
残り、centered factor を regularize しても hard cutoff の近似問題は残る。

## 8. Boundary-safe radius and annulus stabilization

既存 API には次がある。

```lean
IsPascalCenteredXiBoundarySafeRadius
pascalCenteredXiForbiddenRadii
isBoundarySafe_of_pos_le_not_mem_forbiddenRadii
finite_boundaryUnsafeRadii_in_Icc
mem_centeredXiZeroDiskFinset_iff_mem_ball_of_boundarySafe
finite_pascalCenteredXiZeros_in_compact
```

既存 theorem は、bounded interval 上の boundary-unsafe radii が finite exceptional
set に含まれることを Green にしている。従って固定 safe radius `R` に対して、
`R` を含む十分小さい annulus に zero radius が無い、という candidate lemma は
有限集合の距離から構成できる見込みがある。

ただし次の reusable theorem は現在の codebase に存在しない。

```lean
exists_safe_annulus_around_boundarySafeRadius
```

よって Gate H の判定は次である。

```text
viable in principle, but not yet Green as a named reusable theorem
```

XDP-003 では次の candidate lemma を最初に検討する。

```text
safe radius R
  → ∃ δ > 0,
      ∀ r, |r - R| < δ → no centered zero has radius r
```

その後、support transition をこの annulus に閉じ込めた smooth cutoff を作れば、
finite zero set 上では sufficiently small `ε` に対する eventual equality を、
global dominated convergence より先に試せる。

これは「smooth cutoff の Mellin transform が既に explicit formula admissible」と
いう意味ではない。H1 の finite stabilization を扱いやすくする local route に
限られる。

## 9. Generic finite pairing abstraction

XDP-001 の

```lean
pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair
```

は centered coordinate 専用であり、現在の XDP-002 では generic definition を
追加しない。

Gate I の決定は次である。

```text
XDP-002: defer
XDP-003: introduce a generic finite zero-window Weil-style pairing after the
          test-function type is fixed
```

理由は二つある。

1. 今ここで `finiteWeilMirrorPair R F G` を導入すると、classical infinite Weil
   functional と誤認される API surface だけが増える。
2. XDP-003 の primary route は Mellin transform `H` と its mirror/conjugate
   transformを必要とするため、pairing の引数型は `ℂ → ℂ` と単純に決めず、
   support / convergence / mirror compatibility を含む test data structure の
   後に決めるべきである。

XDP-001 pairing はそのまま保持し、XDP-003 で specialization theorem が短くなる
ことを確認できた場合だけ generic abstraction を追加する。

## 10. XDP-003 primary target — Route M

XDP-003 の最小 target を次の順番に固定する。

### M1. Positive multiplicative test data

まず `Ioi 0` 上の compactly supported smooth test functionを表す data を作る。
候補の内容は次である。

```text
h : ℝ → ℂ
0 < a < b
support h ⊆ Icc a b
ContDiff ℝ ∞ h
```

Mathlib の `HasCompactSupport.toSchwartzMap` は利用候補だが、positive-support と
Mellin convergence の bridge は XDP-003 の責務とする。

### M2. Mellin transform and mirror companion

次の名前を XDP-003 の候補 public surface とする。

```lean
pascalWeilMellinTest
pascalWeilMellinMirrorTest
pascalWeilMellinMirror_eq
pascalWeilMellin_transform_eq_fourier_logCoordinate
```

この段階で証明すべきことは、classical theorem の全 explicit formula ではなく、

```text
Mellin convergence
inverse/conjugation convention
critical-line shift convention
local holomorphicity or differentiability on the required strip
```

である。

### M3. Centered zero-side factor

`c(s) = s - 1/2` をそのまま admissible transform と宣言しない。まず次のどちらを
採るかを theorem assumptions とともに決める。

```text
moment / Mellin derivative producing a controlled centered factor
regularized centered factor with an explicit remainder
```

M3 の target theorem は、chosen factor が `centeredComplex` を zero-side で読む
ことを示す有限/局所 statement に限る。global zero sum や RH equivalence はまだ
含めない。

### M4. Safe-radius finite stabilization

M1 の cutoff transition を boundary-safe annulus に置き、XDP-001 の finite
window values に対して sufficiently small `ε` の eventual equality を狙う。

候補 theorem 名:

```lean
pascalCenteredXiBoundarySafeRadius_exists_zeroFreeAnnulus
pascalCriticalMirrorZeroWindow_smoothCutoff_eventually_eq
```

これらは候補名であり、XDP-002 で未実装・未証明である。

### M5. Prime-side entry point

prime-side は新しい `Λ` theorem から始めず、既存の

```lean
pascalVonMangoldtLSeriesBridge
ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
```

を入口にする。explicit formula の missing theorem は、Mellin test data、contour /
residue、zero-side、archimedean term、prime-power termを別々に formalize する
次段階である。

## 11. Fallback routes

### Route S — Schwartz/Fourier-first

Mathlib の Fourier / Schwartz surface は十分強いが、`SchwartzMap ℝ ℂ` から
positive multiplicative Mellin test functionへの support-preserving transportと、
zeta zero evaluationが未接続である。したがって fallback とする。

### Route P — existing PPW prime/zeta bridge first

PPW-011 の von Mangoldt bridge は既に Green なので、prime-side theoremを先に
整理する場合の fallback とする。ただしそれだけでは zero-side admissibilityや
Guinand--Weil explicit formulaを提供しない。

## 12. Blocker / Risk / Non-goal

### Blocker

```text
B1. pinned Mathlib に Guinand--Weil explicit formula theorem surface がない
B2. classical Weil test-function class と Mathlib Mellin/Schwartz structure の
    definition-level adapter がない
B3. centered unbounded factor と admissible transform の factorization が未決定
```

### Risk

```text
R1. `x ↦ x⁻¹`、complex conjugation、`s ↦ 1-s` の順序で符号が変わる
R2. Fourier の `2π` normalization と literature の convention を混同しやすい
R3. safe-radius stabilization は finite zero set では軽いが、global transformの
    convergenceとは別問題
R4. smooth cutoff の zero-side approximation は possibleでも、prime-sideの
    explicit formula contributionを自動的には与えない
```

### Non-goal

```text
N1. RH の証明または RH-equivalent provider
N2. classical Weil criterion / Li criterion の formalization完了
N3. global infinite zero sumの convergence
N4. Guinand--Weil explicit formulaの一括実装
N5. hard cutoffをclassical admissibleと宣言すること
```

## 13. Gate status

```text
[Green] Gate A  XDP-001 finite defectのdictionary
[Green] Gate B  Mellin API present / missingのcompile audit
[Green] Gate C  Fourier / Schwartz API present / missingのcompile audit
[Green] Gate D  von Mangoldt / ζ'/ζ bridgeのcompile audit
[Green] Gate E  explicit-formula availability = C
[Green] Gate F  hard-cutoff obstruction H1
[Green] Gate G  centered-growth obstruction H2
[Classified] Gate H safe-radius annulus = viable candidate, named theorem未実装
[Deferred] Gate I generic finite pairing = XDP-003で型確定後
[Green] Gate J XDP-003 primary target = Route M / M1--M5
```

## 14. Validation record

XDP-002 は report-only change とし、Lean public root import は変更していない。

```bash
lake env lean /tmp/xdp002_api_probe.lean
git diff --check
```

API probe は成功した。probe の一時ファイルは commit 対象ではない。今回の report
には Lean code、`sorry`、`admit`、`axiom`、`native_decide` を追加していない。

以上により、XDP-003 は「classical Weil theorem を既に呼べる」と仮定せず、
Route M の M1 positive compactly-supported smooth test data、M2 Mellin mirror
convention、M4 safe-radius annulus candidateを最初の実装単位とする。
