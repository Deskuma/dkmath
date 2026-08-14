# XDP-017 — Finite right-edge prime-cutoff integral transport 実装指示書

作成日: 2026-08-13

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-side-explicit-formula-260813-v0
workdir: lean/dk_math
Lean / Mathlib: repository pinned toolchain
```

XDP-012〜016 の finite contour / residue transport block は `develop` に merge 済みであり、この branch はその Green surface から開始する。

現在の finite explicit-formula endpoint は次である。

```lean
pascalCenteredXiFiniteExplicitFormulaSkeleton
```

概念的には

```text
-2πi × finite Xi weighted zero moment
=
2 × finite right-edge decomposed integral
+ 2 × finite top-horizontal correction
```

right edge は ordinary coordinate

```text
s(t) = σ + i t
```

にあり、rectangle contract から `1 < σ` が既に保証される。

ordinary-zeta component については既に pointwise endpoint

```lean
tendsto_pascalPrimePowerPHZFiniteUpTo_pascalXiOrdinaryZetaNegLogDeriv_rightEdge
```

が Green である。

また finite cutoff は既に

```lean
pascalPrimePowerPHZFiniteUpTo_eq_vonMangoldt_sum
pascalPrimePowerPHZFiniteUpTo_eq_LSeries_partialSum
```

により von Mangoldt Dirichlet polynomial / L-series partial sum と exact に一致する。

XDP-017 の目的は、**この pointwise arithmetic endpoint を有限 vertical interval integral の endpoint へ昇格すること**である。

principal target:

```text
pointwise Pascal/von Mangoldt cutoff convergence
→ vertical-line absolute majorant independent of t and X
→ finite interval dominated / uniform convergence
→ cutoff integral convergence
→ ordinary-zeta right-edge integral transport
```

本 phase では `T → ∞`、horizontal decay、top-horizontal correction の消去、Mellin `τ → 0` / `ε → 0+`、defect sign / defect vanishing、RH は扱わない。

---

# Gate 0 — Pinned API audit

実装前に pinned Mathlib の exact API を確認すること。

最低限 audit する対象:

```text
MeasureTheory dominated-convergence theorem family
intervalIntegral と set/measure integral の変換 API
IntervalIntegrable / Integrable の変換 API
finite interval 上の ContinuousOn.intervalIntegrable
Finset norm-sum inequality
Summable / HasSum / tsum の nonnegative upper bound API
LSeries term の norm / real-part dependence に関する API
Complex.cpow の norm / real-part formula
```

候補名を memory だけで決めず、repository pinned source / `#check` で exact signature を確認すること。

特に次を確認する。

```lean
#check ArithmeticFunction.LSeriesSummable_vonMangoldt
#check LSeries.term
#check LSeries.term_def₀
#check intervalIntegral.integral_eq_integral_uIoc
```

上記最後の名前が pinned revision に存在しない場合は equivalent API を探す。

### 禁止

pointwise `Tendsto` だけから integral `Tendsto` を直接結論してはならない。

```text
pointwise convergence
≠
integral convergence
```

である。

必ず uniform bound / dominated convergence / summable tail estimate のいずれかを theorem として供給すること。

---

# Gate A — Canonical finite right-edge arithmetic observables

新 module を推奨する。

```text
DkMath/RH/CFBRC/PascalCenteredXiPrimeRightEdgeTransport.lean
```

right-edge arithmetic observable を明示的に定義する。

推奨 shape:

```lean
noncomputable def pascalPrimePowerRightEdgeCutoffIntegrand
    (h : ℂ → ℂ) (σ : ℝ) (X : ℕ) (t : ℝ) : ℂ :=
  (h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t)) *
    pascalPrimePowerPHZFiniteUpTo X
      (pascalSymmetricRectangleRightEdge σ t)) * Complex.I

noncomputable def pascalPrimePowerRightEdgeCutoffIntegral
    (h : ℂ → ℂ) (σ T : ℝ) (X : ℕ) : ℂ :=
  ∫ t in (-T)..T,
    pascalPrimePowerRightEdgeCutoffIntegrand h σ X t
```

ordinary-zeta limit observable も parallel に定義する。

```lean
noncomputable def pascalXiOrdinaryZetaRightEdgeIntegrand ...
noncomputable def pascalXiOrdinaryZetaRightEdgeIntegral ...
```

### Coordinate discipline

`h` は centered coordinate function なので必ず

```lean
h (pascalOrdinaryToCentered
  (pascalSymmetricRectangleRightEdge σ t))
```

と評価する。

`pascalPrimePowerPHZFiniteUpTo` と `pascalXiOrdinaryZetaNegLogDeriv` は ordinary coordinate `s` で評価する。

Acceptance:

```text
Gate A Green:
finite cutoff integral と ordinary-zeta limit integral が canonical named object になっている。
```

---

# Gate B — Weighted pointwise right-edge convergence

既存 theorem

```lean
tendsto_pascalPrimePowerPHZFiniteUpTo_pascalXiOrdinaryZetaNegLogDeriv_rightEdge
```

から、固定 `t` に対して weighted integrand が収束する theorem を作る。

概念的 target:

```text
h(z(t)) × PHZ_X(s(t)) × I
→
h(z(t)) × Lζ(s(t)) × I
```

ここで

```text
z(t) = pascalOrdinaryToCentered (rightEdge σ t)
s(t) = rightEdge σ t
```

である。

推奨 theorem:

```lean
tendsto_pascalPrimePowerRightEdgeCutoffIntegrand
```

仮定は最低限 `1 < σ` でよい。`h` の differentiability は pointwise convergence 自体には不要。

Acceptance:

```text
Gate B Green:
各 t で weighted arithmetic integrand の pointwise Tendsto が actual theorem。
```

---

# Gate C — Vertical-line absolute majorant

ここが XDP-017 の load-bearing gate である。

## C1. L-series term norm を vertical line 上で固定する

coeff を

```lean
fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)
```

とする。

`1 < σ` のもとで、理想的には

```text
‖LSeries.term coeff (σ + i t) n‖
=
‖LSeries.term coeff (σ : ℂ) n‖
```

またはそれ以下の upper bound を示す。

Mathlib に direct lemma があれば必ずそれを優先する。

direct lemma がない場合は `vonMangoldt_LSeries_term_eq` と complex `cpow` の norm formula から局所 helper を証明してよい。

`n = 0` は coefficient zero convention があるため、totalized `0 ^ (-s)` を無理に解析しないこと。

## C2. Real-axis absolute series is summable

既存

```lean
ArithmeticFunction.LSeriesSummable_vonMangoldt
```

を `s = (σ : ℂ)` に適用し、vertical majorant series の summability を得る。

可能なら named constant を定義する。

```lean
noncomputable def pascalVonMangoldtVerticalMajorant (σ : ℝ) : ℝ :=
  ∑' n : ℕ,
    ‖LSeries.term
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
      (σ : ℂ) n‖
```

命名は実装上自然なものへ変更してよい。

## C3. Every finite cutoff is bounded uniformly in `X,t`

principal target:

```text
‖pascalPrimePowerPHZFiniteUpTo X (rightEdge σ t)‖
≤
pascalVonMangoldtVerticalMajorant σ
```

を `X` と `t` に依存しない bound として theorem 化する。

証明は

```text
PHZ finite
= LSeries finite partial sum
→ norm_sum_le
→ sum of term norms
→ finite partial norm sum ≤ total tsum
```

を第一候補とする。

### 注意

von Mangoldt の非負性を一から展開して手作業で majorant を作る必要はない。既存 L-series absolute summability surface を最大限再利用すること。

Acceptance:

```text
Gate C Green:
1 < σ の vertical line 上で PHZ_X の norm に X,t-independent finite majorant がある。
```

Gate C が未閉鎖なら integral transport を Green と判定しない。

---

# Gate D — Weight-side finite-interval integrability

`h : ℂ → ℂ` に `Differentiable ℂ h` を仮定する。

right-edge centered path

```lean
fun t : ℝ =>
  h (pascalOrdinaryToCentered
    (pascalSymmetricRectangleRightEdge σ t))
```

は continuous である。

有限 interval `[-T,T]` 上で、Gate C の scalar majorant `Bσ` を使い

```text
g(t) = ‖h(z(t))‖ * Bσ
```

を dominating real function として構成するのを第一候補とする。

`g` は finite interval 上 continuous なので integrable である。

この設計なら `sup ‖h‖` を別途構成しなくてもよい。

もし pinned dominated-convergence API が constant bound を要求する方が簡単なら、compact interval 上の continuity から

```text
∃ C ≥ 0, ∀ t ∈ [-T,T], ‖h(z(t))‖ ≤ C
```

を作り `C * Bσ` を constant majorant としてもよい。

Acceptance:

```text
Gate D Green:
weighted cutoff integrand を all X で支配する finite-interval integrable majorant が actual theorem / proof-local theorem として存在する。
```

---

# Gate E — Finite interval dominated-convergence transport

Gate B pointwise convergence、Gate C/D majorant を用いて、principal theorem を閉じる。

推奨 target:

```lean
theorem tendsto_pascalPrimePowerRightEdgeCutoffIntegral
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {σ T : ℝ} (hσ : 1 < σ) :
    Tendsto
      (fun X => pascalPrimePowerRightEdgeCutoffIntegral h σ T X)
      atTop
      (nhds (pascalXiOrdinaryZetaRightEdgeIntegral h σ T))
```

`0 < T` を pinned interval-integral → measure-integral conversion が要求する場合は仮定してよい。rectangle adapter では `W.rectangle.hT` が利用できる。

## Preferred route

1. interval integral を finite set / measure integral に rewrite。
2. Gate B の pointwise convergence を measure-a.e. convergenceへ持ち上げる。
3. Gate D の integrable dominationを供給。
4. pinned dominated-convergence theoremを適用。
5. interval integralへ戻す。

## Alternative route

pinned DCT interface が非常に扱いにくい場合は、absolute summability から uniform tail estimate を作り、finite interval integral の norm estimateで Cauchy / uniform convergenceを閉じてもよい。

ただし alternative routeでも

```text
uniform tail bound independent of t
```

を actual theorem として示すこと。

### 禁止

```text
pointwise Tendsto を rw して integral の外へ出す
```

ような非合法 shortcut を行わないこと。

Acceptance:

```text
Gate E Green:
finite right-edge PHZ cutoff integral が ordinary-zeta right-edge integralへ Tendsto する actual theorem。
```

XDP-017 の minimum successful close は Gate E Green である。

---

# Gate F — Finite cutoff arithmetic expansion

将来の prime-side explicit formula の可読性のため、有限 `X` では right-edge cutoff integral を von Mangoldt finite sumへ展開する。

既存

```lean
pascalPrimePowerPHZFiniteUpTo_eq_vonMangoldt_sum
```

を integrand に入れ、有限 `Finset` sum と interval integral を交換する。

概念的 target:

```text
I_X(h,σ,T)
=
Σ_{q≤X} Λ(q)
  ∫_{-T}^{T}
    h(σ - 1/2 + i t)
    q^{-(σ+i t)}
    i dt
```

Lean では既存 complex `cpow` 表現をそのまま保持してよい。

`exp(-i t log q)`、三角関数、`Complex.arg` へ展開する必要はない。

`q = 0` / `q = 1` は von Mangoldt zero convention を利用し、特別な branch analysis を増やさない。

推奨 theorem:

```lean
pascalPrimePowerRightEdgeCutoffIntegral_eq_vonMangoldt_sum
```

または canonical PHZ version を先に作ってもよい。

Acceptance:

```text
Gate F Green:
finite cutoff integral が finite arithmetic sum of weighted oscillatory kernels として actual theorem に展開される。
```

---

# Gate G — Residue-window adapter

XDP-016 の downstream callers がそのまま使える adapter を作る。

`W : PascalCenteredXiResidueTransportWindow` に対して

```text
σ := W.rectangle.σ
T := W.rectangle.T
```

とし、`W.rectangle.hσ`、`W.rectangle.hT` を利用する。

推奨 theorem:

```lean
tendsto_pascalPrimePowerRightEdgeCutoffIntegral_of_residueTransportWindow
```

または命名上自然な equivalent theorem。

この adapter の limit target は XDP-016 skeleton の decomposed right-edge integralの **ordinary-zeta component** と syntactically compatible な shape にすること。

具体的には `* Complex.I` の位置と centered `h` の評価点を skeleton と一致させる。

Acceptance:

```text
Gate G Green:
XDP-016 skeleton の right-edge ordinary-zeta componentを prime cutoff limitで置換できる API がある。
```

---

# Gate H — Optional right-edge decomposition split

余力があれば、XDP-016 の right-edge decomposed integral

```text
h × (ordinary-zeta + archimedean + elementary) × I
```

を finite interval 上で

```text
ordinary-zeta right-edge integral
+ archimedean right-edge integral
+ elementary right-edge integral
```

へ actual に分離する。

必要な `IntervalIntegrable` は個別に供給すること。

right edge は `σ > 1` なので ordinary zeta / elementary factor は singularity-free。Gammaℝ termもこの half-planeで必要な regularityを pinned APIから供給する。

ただし Gate H が unexpectedly heavy なら **XDP-018 へ明示的に残してよい**。XDP-017 の principal close は Gate E/G である。

---

# Acceptance levels

## Minimum Green

```text
Gate A–E Green
```

すなわち finite right-edge Pascal/von Mangoldt cutoff integral の limit exchange が actual theorem。

## Strong Green

```text
Minimum Green
+ Gate F finite arithmetic expansion
+ Gate G residue-window adapter
```

## Ideal Green

```text
Strong Green
+ Gate H right-edge decomposed integral split
```

Ideal Green まで到達した場合、次 phase は XDP-016 skeleton へ prime cutoff limitを代入した finite arithmetic explicit-formula assemblyへ進める。

---

# No-circularity / phase boundary

本 phase では以下を仮定・結論に含めない。

```text
RiemannHypothesis
PascalCenteredXiFixedDefectVanishesOnSafeRadii
defect = 0
defect ≤ 0
critical-line concentration
horizontal term = 0
T → ∞
ε → 0+
τ → 0
prime-side sign theorem
```

また新規

```text
axiom
sorry
admit
native_decide
```

で解析 gap を埋めない。

既存 unrelated `sorry` warning は別 ledger として扱う。

---

# Build / validation

最低限:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiPrimeRightEdgeTransport.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiPrimeRightEdgeTransport
lake build DkMath.RH
./lb DkMath.RH
git diff --check
```

主要 theorem について

```text
#print axioms
```

を確認する。

結果報告には必ず以下を記録する。

```text
Gate A–H の Green / Blocked status
採用した pinned DCT / interval-integral API
vertical majorant の exact theorem 名
finite PHZ norm bound の exact theorem 名
integral Tendsto の exact theorem 名
finite arithmetic expansion の exact theorem 名
残った analytic blocker がある場合は最小の theorem shape
axiom / sorry / admit / native_decide audit
```

---

# XDP-017 completion criterion

最重要 endpoint は次である。

```text
finite Pascal/von Mangoldt cutoff on Re(s)=σ>1
→ weighted finite right-edge interval integral
→ X→∞
→ ordinary-zeta negative-log-derivative right-edge integral
```

この endpoint が Green になれば、XDP-016 で得た spectral finite explicit-formula skeleton に対して、ordinary-zeta right edgeを arithmetic prime-power limitへ置換する数学的 license が初めて得られる。

XDP-017 は residue transport の続編ではなく、**spectral side から arithmetic sideへ渡る最初の actual integral-level bridge** と位置づける。