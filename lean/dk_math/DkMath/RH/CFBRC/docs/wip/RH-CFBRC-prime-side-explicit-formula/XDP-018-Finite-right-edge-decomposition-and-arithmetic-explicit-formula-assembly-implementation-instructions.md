# XDP-018 — Finite right-edge decomposition / arithmetic explicit-formula assembly 実装指示書

作成日: 2026-08-13

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-side-explicit-formula-260813-v0
workdir: lean/dk_math
Lean / Mathlib: repository pinned toolchain
```

XDP-017 は `Strong Green through Gate G` で閉じた。

現在 Green の prime-side endpoint は次である。

```lean
pascalPrimePowerRightEdgeCutoffIntegrand
pascalPrimePowerRightEdgeCutoffIntegral
pascalXiOrdinaryZetaRightEdgeIntegrand
pascalXiOrdinaryZetaRightEdgeIntegral

tendsto_pascalPrimePowerRightEdgeCutoffIntegral
pascalPrimePowerRightEdgeCutoffIntegral_eq_vonMangoldt_sum
tendsto_pascalPrimePowerRightEdgeCutoffIntegral_of_residueTransportWindow
```

XDP-016 の finite spectral endpoint は次である。

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

right-edge decomposed observable は

```lean
pascalXiDecomposedNegLogDeriv s
```

であり、定義上

```text
ordinary-zeta
+ archimedean Gammaℝ correction
+ elementary correction
```

の和である。

XDP-018 の目的は、**有限 right edge 上でこの三項分解を interval-integral theorem に昇格し、XDP-017 の Pascal/von Mangoldt cutoff limit を XDP-016 の finite skeleton に actual に差し込んで finite arithmetic explicit formula を構成すること**である。

本 phase では以下を扱わない。

```text
T → ∞
horizontal decay / top-horizontal correction = 0
Mellin τ → 0 / ε → 0+
defect sign / defect vanishing
RH / critical-line concentration
prime-side infinite-height integral
```

---

# Gate 0 — Pinned API / coordinate audit

実装前に pinned Mathlib の exact API を `#check` / source で確認すること。

最低限 audit する対象:

```text
IntervalIntegrable.add / sub / mul_const / const_mul
intervalIntegral.integral_add
intervalIntegral.integral_sub
Continuous.intervalIntegrable
ContinuousOn.intervalIntegrable
AEStronglyMeasurable / Integrable / IntervalIntegrable の limit-side helper
interval dominated-convergence theoremから limit integrabilityを得る companion API
LSeries の absolute convergence / continuity API
```

候補 theorem 名を memory だけで固定しない。

### 座標規律

right edge の ordinary point は

```text
s(t) = pascalSymmetricRectangleRightEdge σ t
```

centered weight は必ず

```lean
h (pascalOrdinaryToCentered s(t))
```

で評価する。

ordinary-zeta / Gammaℝ / elementary correction は ordinary point `s(t)` で評価する。

vertical differential `Complex.I` は既存 XDP-017 observable と同じ位置に保持すること。

---

# Gate A — Named right-edge correction observables

新 module を推奨する。

```text
DkMath/RH/CFBRC/PascalCenteredXiFiniteArithmeticExplicitFormula.lean
```

既存 XDP-017 definitions と shape を揃えて、少なくとも次を named API にする。

```lean
pascalXiArchimedeanRightEdgeIntegrand
pascalXiArchimedeanRightEdgeIntegral

pascalXiElementaryRightEdgeIntegrand
pascalXiElementaryRightEdgeIntegral

pascalXiNonPrimeRightEdgeIntegrand
pascalXiNonPrimeRightEdgeIntegral

pascalXiDecomposedRightEdgeIntegrand
pascalXiDecomposedRightEdgeIntegral
```

推奨定義:

```lean
pascalXiArchimedeanRightEdgeIntegrand h σ t :=
  (h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t)) *
    pascalXiArchimedeanLogDeriv
      (pascalSymmetricRectangleRightEdge σ t)) * Complex.I

pascalXiElementaryRightEdgeIntegrand h σ t :=
  (h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t)) *
    pascalXiElementaryLogDerivCorrection
      (pascalSymmetricRectangleRightEdge σ t)) * Complex.I

pascalXiNonPrimeRightEdgeIntegrand h σ t :=
  pascalXiArchimedeanRightEdgeIntegrand h σ t +
    pascalXiElementaryRightEdgeIntegrand h σ t

pascalXiDecomposedRightEdgeIntegrand h σ t :=
  (h (pascalOrdinaryToCentered
      (pascalSymmetricRectangleRightEdge σ t)) *
    pascalXiDecomposedNegLogDeriv
      (pascalSymmetricRectangleRightEdge σ t)) * Complex.I
```

実際の naming / factoring は repository convention に合わせてよい。

### Required pointwise algebra

```lean
pascalXiDecomposedRightEdgeIntegrand_eq_zeta_add_nonPrime

pascalXiNonPrimeRightEdgeIntegrand_eq_archimedean_add_elementary
```

は定義展開と ring で閉じる。

Acceptance:

```text
Gate A Green:
right-edge zeta / archimedean / elementary / non-prime / decomposed observablesの型と座標が一意に揃う。
```

---

# Gate B — Full decomposed right-edge integrability from the fixed-Xi Green surface

Gamma の `deriv` continuity を最初から直接攻めないこと。

XDP-016 では既に

```lean
pascalCenteredXiRectangleBoundaryIntegrable_diskWeightedRawRegularizer
pascalCenteredXiRectangleBoundaryIntegrable_diskWeightedPrincipalPartSum
pascalSymmetricRectangleBoundaryIntegrable_add
pascalCenteredXiWeightedNegLogDeriv_comp_toCentered_eq_raw_add_principalPartSum
```

が Green である。

これらからまず coordinate-safe full fixed-Xi boundary integrability を actual theorem にすること。

推奨 theorem:

```lean
pascalCenteredXiRectangleBoundaryIntegrable_weightedNegLogDeriv
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    PascalSymmetricRectangleBoundaryIntegrable
      (fun s => pascalCenteredXiWeightedNegLogDeriv h
        (pascalOrdinaryToCentered s))
      W.rectangle.σ W.rectangle.T
```

証明は raw + principal-part sum の integrability と pointwise decomposition の congruence でよい。

次に right edge だけを取り出し、

```lean
pascalCenteredXiNegLogDeriv_rightEdge_eq_decomposed
```

を使って weighted decomposed right-edge integrability へ transport する。

推奨 theorem:

```lean
intervalIntegrable_pascalXiDecomposedRightEdgeIntegrand
```

### 注意

`pascalXiDecomposedNegLogDeriv` の三 summands が個別に integrable だから full が integrable、という順にしなくてよい。

本 Gate では逆に、**already-Green fixed-Xi combined observable の regularity を right-edge decomposed observableへ移す**。

Acceptance:

```text
Gate B Green:
finite right edge の complete decomposed weighted integrand が actual IntervalIntegrable。
```

---

# Gate C — Ordinary-zeta right-edge limit integrability

XDP-017 は integral Tendsto を既に閉じているが、XDP-018 で `integral_add` を使うには target ordinary-zeta integrand の `IntervalIntegrable` theorem が別途必要である。

principal target:

```lean
intervalIntegrable_pascalXiOrdinaryZetaRightEdgeIntegrand
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {σ T : ℝ} (hσ : 1 < σ) :
    IntervalIntegrable
      (pascalXiOrdinaryZetaRightEdgeIntegrand h σ)
      volume (-T) T
```

### 第一候補 — XDP-017 majorant の再利用

XDP-017 で既に

```lean
pascalVonMangoldtVerticalMajorant
summable_pascalVonMangoldtVerticalMajorant
norm_pascalPrimePowerPHZFiniteUpTo_rightEdge_le_verticalMajorant
pascalRightEdgeCutoff_norm_le_majorant
```

相当の domination machinery がある。

同じ bound と pointwise limit から target integrand の norm bound / measurability / integrabilityを証明する。

pinned API に、dominated convergence の結論と一緒に limit integrability を直接供給する theorem があれば使う。

無ければ、次のいずれかで明示的に閉じる。

```text
A. pointwise limit と uniform norm bound から limit norm boundを得て integrable_of_dominated を使う
B. von Mangoldt L-series の absolute convergence / continuity theorem を使う
C. right-edge ordinary-zeta = von Mangoldt LSeries を使い compact interval continuity を得る
```

### 禁止

`intervalIntegral` が totalized だから integrability を省略してよい、とはしない。

Gate D/E の add/sub split に必要な `IntervalIntegrable` を actual theorem として供給すること。

Acceptance:

```text
Gate C Green:
ordinary-zeta right-edge integrand の finite interval integrability が無仮定 providerなしで閉じる。
```

---

# Gate D — Non-prime correction integrability by subtraction

ここが XDP-018 の推奨 route の中心である。

Gate B で

```text
decomposed integrand : IntervalIntegrable
```

Gate C で

```text
ordinary-zeta integrand : IntervalIntegrable
```

を得たら、pointwise algebra

```text
non-prime = decomposed - ordinary-zeta
```

を使い、

```lean
intervalIntegrable_pascalXiNonPrimeRightEdgeIntegrand
```

を `.sub` + congruence で閉じる。

ここでは Gamma derivative の continuity を必要としない。

そして

```lean
pascalXiDecomposedRightEdgeIntegral_eq_zeta_add_nonPrime
```

を `intervalIntegral.integral_add` で actual に証明する。

概念式:

```text
I_dec = I_zeta + I_nonprime
```

Acceptance:

```text
Gate D Green:
combined non-prime correction が finite interval 上で actual integrable かつ integral split が Green。
```

---

# Gate E — Elementary correction direct integrability

`pascalXiElementaryLogDerivCorrection` は

```lean
-1 / s + 1 / (1 - s)
```

である。

right edge では `1 < σ` から

```text
s ≠ 0
s ≠ 1
```

が `rightEdge_factor_nonzero_of_one_lt` で自動供給される。

したがって elementary right-edge integrand は finite interval 上で直接 continuous / interval-integrable にできるはずである。

推奨 theorem:

```lean
intervalIntegrable_pascalXiElementaryRightEdgeIntegrand
```

proof route:

```text
right-edge path continuous
centered weight continuous from Differentiable h
s ↦ -1/s + 1/(1-s) continuous along right edge because denominators nonzero
product × Complex.I continuous
Continuous.intervalIntegrable
```

既存

```lean
rightEdge_factor_nonzero_of_one_lt
```

を denominator safety に使う。

Acceptance:

```text
Gate E Green:
elementary correction integrability が direct analytic theorem として閉じる。
```

---

# Gate F — Archimedean integrability without a Gamma-derivative continuity detour

Gate D の combined non-prime integrability と Gate E の elementary integrability から

```text
archimedean = non-prime - elementary
```

を使って

```lean
intervalIntegrable_pascalXiArchimedeanRightEdgeIntegrand
```

を閉じる。

その後

```lean
pascalXiNonPrimeRightEdgeIntegral_eq_archimedean_add_elementary
```

を actual theorem にする。

最終的に

```lean
pascalXiDecomposedRightEdgeIntegral_eq_zeta_add_archimedean_add_elementary
```

を得る。

概念式:

```text
I_dec = I_zeta + I_arch + I_elem
```

### なぜこの route を優先するか

`pascalXiArchimedeanLogDeriv` は `-logDeriv Gammaℝ` であり、`Gammaℝ ≠ 0` だけでは `deriv Gammaℝ` の continuity theorem名まで自明ではない。

right edge の combined fixed-Xi regularity は既に XDP-016 で確立しているため、Gamma term の integrability を差として得る方が小さく、既存 Green surface を再利用できる。

### 代替 route

pinned Mathlib に `logDeriv Gammaℝ` の right-half-plane continuity / holomorphicityを直接簡潔に与える API がある場合、直接 proof を追加してもよい。

ただしその場合も result report に使用 theorem と domain 条件を明記する。

Acceptance:

```text
Gate F Green:
archimedean / elementary を含む三項 right-edge integral split が actual theorem。
```

---

# Gate G — Finite spectral/arithmetic endpoint equality

XDP-016 の

```lean
pascalCenteredXiFiniteExplicitFormulaSkeleton
```

と Gate F の right-edge split を合成する。

推奨 endpoint theorem:

```lean
pascalCenteredXiFiniteExplicitFormula_eq_zeta_archimedean_elementary_top
```

概念式:

```text
-2πi × M_W(h)
=
2 I_zeta
+ 2 I_arch
+ 2 I_elem
+ 2 I_top
```

ここでは `I_top` を絶対に消さない。

`W.rectangle.T` は finite のまま保持する。

Acceptance:

```text
Gate G Green:
finite Xi zero moment と zeta/Gamma/elementary/top の4-term right side が exact equalityで接続される。
```

---

# Gate H — Finite arithmetic explicit-formula Tendsto

XDP-017 の

```lean
tendsto_pascalPrimePowerRightEdgeCutoffIntegral_of_residueTransportWindow
```

を Gate G へ差し込む。

principal theorem を次の shape で作ることを推奨する。

```lean
tendsto_pascalCenteredXiFiniteArithmeticExplicitFormula
    {h : ℂ → ℂ}
    (hdiff : Differentiable ℂ h)
    (heven : PascalCenteredEvenWeight h)
    (W : PascalCenteredXiResidueTransportWindow) :
    Tendsto
      (fun X =>
        2 * pascalPrimePowerRightEdgeCutoffIntegral h
          W.rectangle.σ W.rectangle.T X +
        2 * pascalXiArchimedeanRightEdgeIntegral h
          W.rectangle.σ W.rectangle.T +
        2 * pascalXiElementaryRightEdgeIntegral h
          W.rectangle.σ W.rectangle.T +
        2 * pascalCenteredXiTopHorizontalContribution h
          W.toContourTransportWindow)
      atTop
      (nhds
        (-(2 * Real.pi * Complex.I) *
          pascalCenteredXiZeroDiskWeightedMoment h W.R))
```

exact syntax は actual definitions に合わせてよい。

重要なのは、**prime cutoff を含む finite arithmetic approximant が spectral zero-moment endpoint へ収束する actual theorem**にすること。

これは

```text
I_X^prime → I_zeta
```

と fixed correction terms の constant Tendsto、Gate G equality の合成で閉じる。

### 注意

この theorem は

```text
for each finite T / fixed residue window W
```

の theorem である。

`T → ∞` と混同しない。

Acceptance:

```text
Gate H Green:
finite Pascal/von Mangoldt cutoff approximants が finite Xi weighted zero moment endpointへ actual Tendsto。
```

---

# Gate I — Explicit finite von Mangoldt approximant expansion

XDP-017 の

```lean
pascalPrimePowerRightEdgeCutoffIntegral_eq_vonMangoldt_sum
```

を使い、Gate H の approximant を finite von Mangoldt weighted kernel sum へ rewrite する named theorem を追加する。

推奨 definition:

```lean
pascalCenteredXiFiniteArithmeticApproximant
    (h : ℂ → ℂ)
    (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℂ :=
  2 * pascalPrimePowerRightEdgeCutoffIntegral h
      W.rectangle.σ W.rectangle.T X +
    2 * pascalXiArchimedeanRightEdgeIntegral h
      W.rectangle.σ W.rectangle.T +
    2 * pascalXiElementaryRightEdgeIntegral h
      W.rectangle.σ W.rectangle.T +
    2 * pascalCenteredXiTopHorizontalContribution h
      W.toContourTransportWindow
```

then theorem:

```text
pascalCenteredXiFiniteArithmeticApproximant_eq_vonMangoldt_sum
```

概念的には

```text
A_X(h,W)
=
2 Σ_{n≤X} Λ(n) ∫_{-T}^{T}
    h(σ-1/2+it) n^{-(σ+it)} i dt
+ 2 I_arch
+ 2 I_elem
+ 2 I_top
```

`Complex.cpow` のまま保持する。

`Complex.arg`、三角関数、偏角展開は不要。

Acceptance:

```text
Gate I Green:
finite arithmetic approximant が明示的な von Mangoldt finite sum surfaceを持つ。
```

---

# Result classification

## Minimum Green

次がすべて actual theorem:

```text
Gate B complete decomposed integrability
Gate C ordinary-zeta integrability
Gate D combined non-prime integrability and split
Gate H arithmetic approximant Tendsto
```

この場合、correction は combined `I_nonprime` のままでもよい。

ただし result report では archimedean / elementary individual splitが未閉鎖と明記する。

## Strong Green

Minimum Green に加えて:

```text
Gate E elementary direct integrability
Gate F archimedean integrability by subtraction
Gate G exact zeta + archimedean + elementary + top identity
```

## Ideal Green

Strong Green に加えて:

```text
Gate I finite von Mangoldt approximant expansion
public RH import surfaceへの接続
主要 theorem #print axioms audit
```

XDP-018 の狙いは `Strong Green` 以上である。

---

# Forbidden shortcuts / phase boundary

次を禁止する。

```text
T → ∞
horizontal term disappearance
fixed same-zero-set window のまま T∞ を取ること
prime cutoff limit と T-limit の交換
Mellin τ → 0 / ε → 0+ の混入
defect = 0 の仮定
RH / critical-line concentration の仮定
Weil/Li positivity の持ち込み
provider-only archimedean integrability を Green 扱い
circle theorem を right-edge interval theorem として読み替える
new axiom / sorry / admit / native_decide
```

`Gammaℝ` の個別 continuity proof が難しい場合、Gate F の subtraction route を使う。

**難しいから provider を置く、は不可。**

---

# No-circularity audit

本 phase の assumptions / conclusions に以下を含めないこと。

```text
RiemannHypothesis
PascalCenteredXiFixedDefectVanishesOnSafeRadii
critical-line concentration
zero horizontal energy = 0
defect ≤ 0 / defect = 0
```

XDP-018 は既存 finite spectral identity と prime-side right-edge convergenceを assembly する phase であり、RH provider ではない。

---

# Expected result report

作成:

```text
lean/dk_math/DkMath/RH/CFBRC/docs/wip/RH-CFBRC-prime-side-explicit-formula/
XDP-018-Finite-right-edge-decomposition-and-arithmetic-explicit-formula-assembly-result.md
```

最低限記録する。

```text
1. phase classification
2. pinned API audit
3. named observable inventory
4. full decomposed integrability proof route
5. ordinary-zeta limit integrability proof route
6. non-prime subtraction route
7. elementary direct integrability
8. archimedean integrability route
9. exact 4-term finite identity
10. arithmetic approximant Tendsto
11. finite von Mangoldt expansion status
12. coordinate audit
13. no-circularity audit
14. #print axioms
15. build commands
16. forbidden declaration search
17. next exact blocker
```

---

# Validation

最低限:

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiFiniteArithmeticExplicitFormula.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiFiniteArithmeticExplicitFormula
lake build DkMath.RH
./lb DkMath.RH
git diff --check
```

主要 theorem:

```text
right-edge integrability theorems
3-term split theorem
finite 4-term spectral/arithmetic equality
arithmetic approximant Tendsto
finite von Mangoldt expansion
```

について `#print axioms` を確認する。

新規 source / result report について

```text
sorry
admit
axiom
native_decide
```

を検索し、意図しない追加がないことを確認する。

---

# After XDP-018

XDP-018 が Strong Green / Ideal Green になった場合、次の frontier は初めて weight specialization へ進める。

候補:

```text
XDP-019 — Mellin second-difference finite arithmetic specialization
```

既存

```lean
centeredMellinSecondDifferenceWeight
  (centeredMellinBoxApprox ε) τ
```

を generic arithmetic explicit formula へ代入し、fixed `ε > 0`, fixed `τ` の段階で prime-side observableを記録する。

その時点でもまだ

```text
τ → 0
ε → 0+
T → ∞
```

を同時に動かさない。

まず finite parameter identity を Green にすること。