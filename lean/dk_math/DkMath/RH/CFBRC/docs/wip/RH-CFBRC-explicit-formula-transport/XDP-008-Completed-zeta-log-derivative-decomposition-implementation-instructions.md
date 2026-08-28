# XDP-008 — Completed-zeta logarithmic-derivative decomposition / explicit-formula transport preflight 実装指示書

作成日: 2026-08-12

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-explicit-formula-transport-260812-v0
Lean: repository toolchain
mathlib: repository pinned revision
```

作業 directory:

```text
lean/dk_math
```

本 branch は、merge 済みの `wip/RH-CFBRC-fixed-Xi-defect-provider-260812-v0` に続く **explicit-formula transport phase** の正本である。

XDP-001〜XDP-007 で zero / Mellin side は次まで Green になっている。

```text
finite centered-Xi defect
→ finite critical-mirror pairing / anti-mirror energy
→ Mellin critical mirror
→ safe-radius local zero-window stability
→ positive compact-support Mellin admissibility
→ globally differentiable centered Mellin spectral weight
→ fixed centered-Xi weighted outer contour
→ centered dilation / symmetric second difference
→ multiplicative approximate identity
→ quadratic weight z² realization
→ fixed centered-Xi second contour target
```

一方、既存 prime side はすでに

```text
Pascal prime-power finite shadow
→ von Mangoldt finite sum
→ von Mangoldt L-series
→ -deriv riemannZeta s / riemannZeta s    (1 < s.re)
```

まで Green である。

XDP-008 の目的は、この二つの endpoint の間に必要な **completed-zeta / ordinary-zeta logarithmic-derivative decomposition** を repository 固有 normalization に即して形式化し、XDP-009 の contour transport に必要な singularity / safety contract を固定することである。

**XDP-008 では full explicit formula、contour shift、prime sum、defect sign、defect vanishing、RH を証明しない。**

---

## 1. Repository 正本 normalization

最初に、以下の既存定義・定理を正本として使うこと。標準的な教科書の Xi normalization を記憶から置き換えてはならない。

既存 module:

```text
DkMath/RH/CFBRC/CompletedZetaBridge.lean
DkMath/RH/CFBRC/PascalCanonicalXiFixedObservableBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiOuterContourResidueBridge.lean
DkMath/RH/CFBRC/PascalVonMangoldtLSeriesBridge.lean
```

現在の fixed observable は repository 上で

```lean
noncomputable def pascalRiemannXiKernel (s : ℂ) : ℂ :=
  s * (1 - s) * completedRiemannZeta₀ s - 1
```

と定義されている。

また、既存 theorem

```lean
theorem pascalRiemannXiKernel_eq_mul_completedRiemannZeta
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    pascalRiemannXiKernel s =
      s * (1 - s) * completedRiemannZeta s
```

がある。

centered coordinate は

```lean
noncomputable def pascalCenteredRiemannXiKernel (z : ℂ) : ℂ :=
  pascalRiemannXiKernel (criticalLineCenter + z)
```

であり、fixed negative logarithmic derivative は

```lean
noncomputable def pascalCenteredXiNegLogDeriv (z : ℂ) : ℂ :=
  -logDeriv pascalCenteredRiemannXiKernel z
```

である。

したがって XDP-008 は常に

```text
z : centered coordinate
s := criticalLineCenter + z = 1/2 + z : ordinary zeta coordinate
```

を明示的に区別すること。

### 禁止

次のような shortcut は禁止する。

```text
pascalRiemannXiKernel = textbook ξ
completedRiemannZeta = remembered normalization
completedRiemannZeta₀ = completedRiemannZeta
```

既存 theorem で証明された domain の外へ、これらの equality を延長してはならない。

---

## 2. Gate A — pinned Mathlib completed-zeta API audit

実装前に pinned Mathlib の exact API を小さな probe file または `#check` / `#print` で確認すること。

最低限確認する候補:

```lean
#check completedRiemannZeta
#check completedRiemannZeta₀
#check completedRiemannZeta_eq
#check completedRiemannZeta_one_sub
#check completedRiemannZeta₀_one_sub
#check riemannZeta_def_of_ne_zero
#check Complex.Gammaℝ
#check Complex.Gammaℝ_eq_zero_iff
#check logDeriv
#check logDeriv_mul
```

必要なら `deriv` / `DifferentiableAt` / `AnalyticAt` の Gamma factor API も確認する。

### Audit report に必ず記録するもの

1. `completedRiemannZeta` と `riemannZeta` / `Complex.Gammaℝ` の exact relation。
2. その relation が成立するための exact hypotheses。
3. `completedRiemannZeta₀` と `completedRiemannZeta` の relation。
4. Mathlib の totalization によって pole point でどの値になるかを、証明に利用してよいか否か。
5. Gamma factor の zero / pole representation が Lean 上でどう表現されているか。

**数式の係数や符号を推測して実装しない。probe で確認した pinned API を source of truth にすること。**

---

## 3. Gate B — local factorized-kernel bridge

`pascalRiemannXiKernel_eq_mul_completedRiemannZeta` は pointwise theorem である。しかし `logDeriv` は値だけでなく derivative を読むので、単一点の equality をそのまま derivative equality に使ってはならない。

### 必須方針

`s ≠ 0`、`s ≠ 1` なら、`s` の十分小さい neighborhood で `0` と `1` を避けられることを使い、factorized kernel との **eventual equality / local equality** を作ること。

必要なら thin helper を定義してよい。

```lean
noncomputable def pascalRiemannXiFactorizedKernel (s : ℂ) : ℂ :=
  s * (1 - s) * completedRiemannZeta s
```

期待する helper shape の一例:

```lean
theorem pascalRiemannXiKernel_eventuallyEq_factorized
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    pascalRiemannXiKernel =ᶠ[𝓝 s]
      pascalRiemannXiFactorizedKernel
```

その上で derivative / logDeriv を合法的に transport する。

### Acceptance

少なくとも、適切な nonzero hypotheses のもとで

```text
logDeriv pascalRiemannXiKernel s
=
logDeriv pascalRiemannXiFactorizedKernel s
```

を得る reusable theorem を Green にする。

### 禁止

```text
have h : pascalRiemannXiKernel s = factorized s := ...
rw [h]  -- derivative/logDeriv の中をこれだけで書き換える
```

のような不正な derivative transport を行わない。

---

## 4. Gate C — uncentered negative log-derivative decomposition

次に、factorized kernel

```text
s * (1 - s) * completedRiemannZeta s
```

の negative logarithmic derivativeを product rule で分解する。

### 4.1 Elementary factor

`s ≠ 0`、`s ≠ 1` のもとで、`s * (1 - s)` の contribution を exact に分離する。

期待する数学的形は

$$
-\frac{d}{ds}\log(s(1-s))
=
-\frac1s+\frac1{1-s}.
$$

ただし Lean theorem の最終 normal form は `field_simp` / `ring` が安定する形を採用してよい。

この部分を named function にしてよい。

```lean
noncomputable def pascalXiElementaryLogDerivCorrection (s : ℂ) : ℂ := ...
```

### 4.2 Completed-zeta factor

pinned Mathlib の exact definition / theorem に従い、completed-zeta contribution を

```text
ordinary zeta negative log derivative
+
archimedean Gamma contribution
```

へ分解する。

ordinary zeta term の canonical target は既存 prime bridge と一致する

```lean
- deriv riemannZeta s / riemannZeta s
```

とする。

archimedean term は、pinned API が安定するなら例えば

```text
-logDeriv Complex.Gammaℝ s
```

のような named correction として残してよい。digamma / `log π` まで無理に展開することは XDP-008 の必須条件ではない。

### 4.3 Required theorem

適切な hypotheses のもとで概念的に

```text
-pascal Xi log derivative
=
ordinary zeta negative log derivative
+
archimedean correction
+
elementary correction
```

という **uncentered pointwise decomposition** を Green にする。

実際の theorem name は repository naming に合わせてよいが、例:

```lean
theorem pascalRiemannXiNegLogDeriv_eq_zeta_add_archimedean_add_elementary
    {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0)
    (hGamma : Complex.Gammaℝ s ≠ 0) :
    ...
```

### 重要

`logDeriv_mul` の hypotheses を満たすために必要な differentiability / nonzero hypotheses は明示する。

**Mathlib の totalized quotient が zero/pole point で数値を返すことを、meromorphic cancellation の代用にしてはならない。**

---

## 5. Gate D — centered coordinate decomposition

Gate C の theorem を

```text
s = criticalLineCenter + z
```

へ transport する。

中心 target は

```lean
pascalCenteredXiNegLogDeriv z
```

である。

必要なら coordinate helper を作る。

```lean
noncomputable def pascalCenteredXiOrdinaryCoordinate (z : ℂ) : ℂ :=
  criticalLineCenter + z
```

ただし既存表現が十分なら新定義を増やさない。

### Required endpoint

適切な pointwise safety hypotheses のもとで

```text
pascalCenteredXiNegLogDeriv z
=
zetaLogDerivTerm (1/2 + z)
 + archimedeanCorrection (1/2 + z)
 + elementaryCorrection (1/2 + z)
```

を Green にする。

符号は Gate C の proved theorem から transport し、手計算で再入力しない。

---

## 6. Gate E — decomposition boundary safety contract

既存の

```lean
def IsPascalCenteredXiBoundarySafeRadius (R : ℝ) : Prop :=
  0 < R ∧ ∀ z ∈ Metric.sphere (0 : ℂ) R,
    pascalCenteredRiemannXiKernel z ≠ 0
```

は **Xi contour 自体**を安全にする。しかし分解後の各 factor

```text
s
1 - s
riemannZeta s
Complex.Gammaℝ s
```

が boundary 上で nonzero であることまでは自動的に保証しない。

特に trivial-zero / Gamma singularity / `s = 0, 1` の bookkeeping を Xi-safe だけで消してはならない。

### 必須

XDP-008 用の追加 safety predicate を定義するか、同等の explicit hypotheses を theorem に持たせること。

候補 shape:

```lean
def IsPascalCenteredXiLogDerivDecompositionSafeRadius (R : ℝ) : Prop :=
  IsPascalCenteredXiBoundarySafeRadius R ∧
  ∀ z ∈ Metric.sphere (0 : ℂ) R,
    let s := criticalLineCenter + z
    s ≠ 0 ∧
    s ≠ 1 ∧
    riemannZeta s ≠ 0 ∧
    Complex.Gammaℝ s ≠ 0
```

名称・形は実装に合わせて改善してよい。

### Optional strengthening

既存 zero classification から、critical strip 内の nontrivial zeta zero について Xi-safe がどこまで `riemannZeta s ≠ 0` を供給できるかを補題化してよい。

しかし trivial zeros / Gamma factor singularitiesまで同じ theorem で消えると仮定しない。

---

## 7. Gate F — weighted integrand decomposition on the outer circle

既存 generic weighted contour integrand は

```lean
fun z => h z * pascalCenteredXiNegLogDeriv z
```

である。

Gate D/E を使い、decomposition-safe boundary 上でこの integrand を

```text
weighted ordinary-zeta term
+
weighted archimedean correction
+
weighted elementary correction
```

へ pointwise に分解する。

### Required theorem shape

```lean
theorem pascalCenteredXiWeightedNegLogDeriv_eq_decomposed_on_sphere
    {h : ℂ → ℂ} {R : ℝ}
    (hSafe : IsPascalCenteredXiLogDerivDecompositionSafeRadius R) :
    Set.EqOn
      (fun z => h z * pascalCenteredXiNegLogDeriv z)
      (fun z =>
        h z * zetaTerm (criticalLineCenter + z) +
        h z * archimedeanTerm (criticalLineCenter + z) +
        h z * elementaryTerm (criticalLineCenter + z))
      (Metric.sphere 0 R)
```

実際の associativity / parenthesization は Lean の簡潔な normal form を採用してよい。

---

## 8. Gate G — outer contour decomposition

各 term の `CircleIntegrable` を確保できるなら、既存 outer contour を三成分へ分解する。

概念 endpoint:

$$
C_{\Xi,h}(R)
=
C_{\zeta,h}(R)
+
C_{\infty,h}(R)
+
C_{\mathrm{elem},h}(R).
$$

### 方針

1. `Set.EqOn` で integrand を boundary 上だけ書き換える。
2. `circleIntegral.integral_add` 等の pinned API を再利用する。
3. singularity の cancellation を circle integral の totalization に押し込まない。
4. Xi residue theoremを再実装しない。

### If blocked

Gamma / ordinary-zeta termの boundary regularityを individually 証明するための pinned API が不足する場合、無理に contour equality を通さず、

```text
Gate F pointwise decomposition = Green
Gate G = named obstruction
```

として result report に exact missing theorem / hypothesis を残す。

XDP-008 の最低 acceptance は Gate A〜F であり、Gate G は pinned API の状態に応じて Green または明示 Blocked としてよい。

---

## 9. Gate H — prime-side hook

既存 module

```text
DkMath/RH/CFBRC/PascalVonMangoldtLSeriesBridge.lean
```

を import / reuse する。

既存 endpoint:

```lean
theorem tendsto_pascalPrimePowerPHZFiniteUpTo_neg_deriv_riemannZeta_div
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun X => pascalPrimePowerPHZFiniteUpTo X s) atTop
      (nhds (- deriv riemannZeta s / riemannZeta s))
```

XDP-008 で ordinary-zeta term を新しく定義する場合、その term が `1 < s.re` でこの既存 endpoint と definitionally / theorem-wise 一致する thin adapter を追加する。

### 禁止

von Mangoldt L-series convergenceを再証明しない。

Pascal prime-power canonical fold を再実装しない。

XDP-008 では contour をまだ `1 < s.re` へ移動しない。

---

## 10. Gate I — XDP-009 contour-shift preflight audit

実装後、次の phase に必要な contour geometry / singularities を report に列挙する。

centered circle

```text
|z| = R
```

は ordinary coordinate で

```text
|s - 1/2| = R
```

である。

これを `1 < s.re` の Dirichlet-series domain と接続するには、単なる theorem rewrite ではなく contour transport が必要である。

### 必ず監査する項目

1. ordinary-zeta termを右半平面へ移す際に crossing し得る singularities。
2. `s = 1` の pole bookkeeping。
3. trivial zeros / negative-even pointsの扱い。
4. Gamma factor側の singularity / totalization representation。
5. centered Xi contourでは cancellation 済みだが、分解後 individually singular になる点。
6. pinned Mathlib に rectangle / contour deformation / meromorphic residue theorem のどこまでがあるか。
7. XDP-009 で必要になる exact missing lemmas。

### 重要

XDP-008 report で

```text
"safe Xi contour だから decomposition contours も安全"
```

と書いてはならない。

---

## 11. 推奨 module

第一候補:

```text
DkMath/RH/CFBRC/PascalCenteredXiCompletedZetaLogDerivBridge.lean
```

必要なら generic helper を別 module にしてよいが、Gamma / Riemann-zeta 固有 algebra を `DkMath.Analysis` に押し上げないこと。

public endpoint が安定した場合のみ

```text
DkMath/RH.lean
```

へ import を追加する。

---

## 12. 推奨 declaration surface

名称は実装時に改善してよい。最低限、次の役割を持つ declaration を用意する。

```text
A. uncentered factorized kernel
B. local/eventual factorized-kernel equality
C. elementary log-derivative correction
D. archimedean log-derivative correction
E. ordinary zeta negative log-derivative term
F. uncentered decomposition theorem
G. centered decomposition theorem
H. decomposition boundary-safety predicate
I. weighted boundary EqOn decomposition
J. optional circle-integral decomposition
K. prime-side thin hook
```

既存 declaration で足りる項目は新規定義しない。

---

## 13. Circularity / safety gate

XDP-008 は representation / analytic transport phase であり、provider phase ではない。

### 使用禁止

次を仮定・import して decomposition を閉じてはならない。

```text
RiemannHypothesis
PascalCenteredXiFixedDefectVanishesOnSafeRadii
pascalCenteredXiFixedSecondMomentDefectFunctional R = 0
all nontrivial zeros lie on re = 1/2
horizontal energy vanishes
Weil positivity / Li positivity equivalent to RH
```

### 主張禁止

```text
explicit formula completed
prime side proves sign
fixed defect ≤ 0
fixed defect = 0
RH
```

XDP-008 が閉じても、得られるのは **Xi log derivative の exact decomposition と contour-shift preflight** だけである。

---

## 14. Validation gate

最低限実行する。

```text
lake env lean DkMath/RH/CFBRC/PascalCenteredXiCompletedZetaLogDerivBridge.lean
lake build DkMath.RH.CFBRC.PascalCenteredXiCompletedZetaLogDerivBridge
./lean-build.sh
./lean-test.sh
git diff --check
```

新規 code について以下を監査する。

```text
sorry
admit
axiom
native_decide
```

必要に応じ principal declaration を `#print axioms` で確認する。

既存 unrelated module の warning は result report で区別する。

---

## 15. Result report

次を作成する。

```text
DkMath/RH/CFBRC/docs/wip/RH-CFBRC-explicit-formula-transport/
  XDP-008-Completed-zeta-log-derivative-decomposition-result.md
```

report には必ず以下を書く。

1. actual pinned completed-zeta normalization。
2. actual theorem names / signatures。
3. local derivative transport route。
4. elementary correction の exact sign / formula。
5. archimedean correction の exact representation。
6. ordinary zeta term の exact representation。
7. centered decomposition theorem。
8. decomposition safety predicate / hypotheses。
9. weighted boundary decomposition の成否。
10. contour decomposition Gate G の成否。
11. prime-side existing bridgeへの hook。
12. XDP-009 contour shiftで crossing する singularity list。
13. pinned Mathlib contour / meromorphic API の named obstruction。
14. build / test / shortcut audit。

---

## 16. XDP-008 完了条件

最低完了条件:

```text
[Green] repository normalization audit
[Green] local factorized-kernel derivative transport
[Green] uncentered Xi negative-log-derivative decomposition
[Green] centered Xi negative-log-derivative decomposition
[Green] decomposition boundary safety contract
[Green] weighted boundary EqOn decomposition
[Green] existing -ζ'/ζ / von Mangoldt endpoint hook
[Recorded] XDP-009 contour-shift singularity / API audit
```

Gate G の full circle-integral split は、pinned API が不足する場合のみ explicit Blocked を許容する。

---

## 17. XDP-009 handoff

XDP-008 後の想定 chain は

```text
fixed centered-Xi weighted contour
→ XDP-008 log-derivative decomposition
→ ordinary-zeta weighted contour + archimedean + elementary corrections
→ XDP-009 contour deformation / residue bookkeeping
→ Re(s) > 1 ordinary-zeta boundary
→ existing PascalVonMangoldtLSeriesBridge
→ weighted prime-power / von Mangoldt representation
```

である。

XDP-009 の開始条件は、**ordinary-zeta term と correction terms が exact に分離され、その singularity contract が Lean declaration と report の双方で固定されていること**。

ここまでは representation bridge であり、defect の independent sign provider ではない。
