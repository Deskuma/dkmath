# XDP-012 — Fixed-Xi circle-to-rectangle residue transport 実装指示書

作成日: 2026-08-12

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-explicit-formula-transport-260812-v0
workdir: lean/dk_math
Lean / Mathlib: repository pinned toolchain
```

XDP-011 までで、finite symmetric rectangle の幾何と functional-equation pairing は次まで Green になっている。

```text
fixed centered-Xi rectangle
→ left/right vertical pairing
→ top/bottom horizontal pairing
→ 2 × right-edge decomposed contribution
 + 2 × finite top-horizontal contribution
```

principal theorem:

```lean
pascalCenteredXiRectangleContribution_eq_two_right_decomposed_add_two_top
```

一方、zero side では既存 `PascalCenteredXiOuterContourResidueBridge.lean` により、boundary-safe centered circle について任意の entire weight `h` に対し

```text
fixed centered-Xi circle
→ finite principal-part subtraction
→ removable patch
→ circle Cauchy-Goursat
→ finite Xi zero weighted moment
```

が既に Green である。

主要 endpoint:

```lean
theorem pascalCenteredXiWeightedOuterContourMass_eq
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiWeightedOuterContourMass h R =
      -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment h R
```

XDP-012 の目的は、**decomposed zeta / Gamma / elementary の三項ではなく、cancellation 済み fixed centered-Xi combined observable のまま finite rectangle residue formula を構成し、circle と rectangle を同じ finite zero moment に接続すること**である。

最終 target は概念的に

```text
fixed Xi circle
   = -2πi × finite zero weighted moment

fixed Xi rectangle
   = -2πi × same finite zero weighted moment

therefore
fixed Xi rectangle = fixed Xi circle
```

である。

さらに XDP-011 と合成して、finite explicit-formula skeleton

```text
-2πi × finite Xi zero weighted moment
=
2 × right-edge decomposed contribution
+ 2 × finite top-horizontal contribution
```

までを狙う。

**XDP-012 では `T → ∞`、horizontal decay、prime cutoff と interval integral の極限交換、crossed charge の asymptotic、defect sign、defect vanishing、RH を証明しない。**

---

# 1. Primary strategy — direct homotopy を避ける

circle を rectangle へ直接 deformation / homotopy する theorem を最初から作らないこと。

優先 route は、既存 circle proof と同じ finite principal-part subtraction を rectangle に独立に適用することである。

```text
circle
→ regularizer boundary integral = 0
→ principal parts only
→ finite residue sum

rectangle
→ same regularizer boundary integral = 0
→ same principal parts only
→ same finite residue sum
```

両 contour の equality は最後に同じ finite moment endpoint を介して得る。

この route は、circle と rectangle の間の複雑な homotopy region を直接形式化する必要を減らす。

---

# 2. Pinned Mathlib audit — 最初に必ず実施

以下を local pinned toolchain で `#check` / source search すること。

第一候補:

```lean
#check Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
```

必要に応じて:

```lean
#check Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
#check Complex.integral_boundary_rect_eq_zero_of_differentiableOn
```

current Mathlib documentation では rectangle Cauchy-Goursat API が存在するが、**theorem 名・argument order・set notation は repository pinned revision を正本とすること**。

また、rectangle 上の one-pole Cauchy integral / winding / residue theorem が既に存在するかを必ず追加 audit する。

検索語例:

```text
integral_boundary_rect
sub_inv
one_div
residue
winding
index
Cauchy rectangle
```

既存 API があれば再利用する。無ければ Gate D の最小導出を検討する。

---

# 3. Gate A — Mathlib rectangle boundary expression adapter

XDP-009/010 の geometry は

```lean
pascalSymmetricRectangleBoundaryIntegral
```

として4辺を orientation 付きで定義している。

Mathlib の rectangle Cauchy-Goursat theorem が返す boundary expression とこの定義を exact に接続する adapter theorem を作ること。

推奨 opposite corners は ordinary coordinate で

```text
lower-left  = (1 - σ) - T i
upper-right = σ + T i
```

である。

XDP の orientation:

```text
right:  bottom → top
top:    right → left
left:   top → bottom
bottom: left → right
```

Mathlib の boundary expression と符号・`Complex.I` の placement を Lean の algebra で照合する。

**手計算した orientation を theorem target に盲目的に埋め込まないこと。**

推奨 theorem shape:

```lean
theorem pascalSymmetricRectangleBoundaryIntegral_eq_mathlibBoundary ...
```

または Mathlib theorem を直接 `simpa` できる wrapper を用意する。

Gate A acceptance:

```text
our 4-edge boundary integral
↔ pinned Mathlib rectangle boundary expression
```

が exact Green。

---

# 4. Gate B — residue-transport safety contract

既存

```lean
PascalCenteredXiContourTransportWindow
```

は circle interior と rectangle interior の same-zero-set contract を持つが、rectangle boundary 上の zero-freeness は保証しない。

したがって XDP-012 用に stronger contract を追加する。

推奨形:

```lean
structure PascalCenteredXiResidueTransportWindow
    extends PascalCenteredXiContourTransportWindow where
  circle_safe : IsPascalCenteredXiBoundarySafeRadius R
  rectangle_boundary_safe : ...
```

`rectangle_boundary_safe` は4辺すべてについて

```text
pascalCenteredRiemannXiKernel (...) ≠ 0
```

を要求する明示的 predicate とする。

または equivalent な named predicate

```lean
IsPascalCenteredXiRectangleBoundarySafe W
```

を先に定義して field として持たせてもよい。

### 必須 lemma

この stronger window から、closed rectangle 内の centered-Xi zero は exactly circle/disk finset の zero であることを導く。

概念的に

```text
zero in open rectangle
↔ W.zero_mem_iff
↔ zero in centered ball
↔ member of pascalCenteredXiZeroDiskFinset W.R
```

boundary zero は `rectangle_boundary_safe` で排除する。

可能なら closed rectangle set を Mathlib Cauchy-Goursat theorem と同じ形で定義する。

例:

```text
uIcc (1 - σ) σ ×ℂ uIcc (-T) T
```

既存 `pascalSymmetricRectangleInterior` との equivalence lemma も作る。

---

# 5. Gate C — disk regularizer machinery の rectangle reuse

**新しい rectangle-specific principal-part regularizer を最初から複製しないこと。**

既存を再利用する。

```lean
pascalCenteredXiWeightedPrincipalPart
pascalCenteredXiDiskWeightedPrincipalPartSum
pascalCenteredXiDiskWeightedRawRegularizer
pascalCenteredXiDiskWeightedRegularizer
pascalCenteredXiDiskWeightedRawRegularizerLimit
```

ここで使う finite pole set は rectangle 独自 Finset ではなく、same-zero-set contract により既存

```lean
pascalCenteredXiZeroDiskFinset W.R
```

を正本にする。

必要なのは既存 disk-restricted helper の一般化である。

現在の一部 lemma は

```text
w ∈ Metric.closedBall 0 R
```

を仮定して Xi nonzero を得ている。

XDP-012 では、より一般的な reusable helper を追加する。

推奨 shape:

```lean
theorem differentiableAt_pascalCenteredXiDiskWeightedRawRegularizer_of_kernel_ne_zero
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} {w : ℂ}
    (hXi : pascalCenteredRiemannXiKernel w ≠ 0) :
    DifferentiableAt ℂ
      (pascalCenteredXiDiskWeightedRawRegularizer h R) w
```

必要なら `w ∉ pascalCenteredXiZeroDiskFinset R` も explicit に要求する。

同様に patched regularizer について rectangle interior / closed rectangle 用の

```text
ContinuousOn
DifferentiableAt off finite zero set
```

を構築する。

### 重要

zero point では既存 removable patch を使う。

非zero pointでは Xi kernel nonzero を stronger window から供給する。

**totalized `logDeriv` の zero point valueを removable limit と同一視しないこと。**

---

# 6. Gate D — rectangle Cauchy-Goursat for the patched regularizer

Gate A–C を使って、patched regularizer の rectangle boundary integral が zero であることを証明する。

principal target:

```lean
theorem pascalCenteredXiRectangleIntegral_diskWeightedRegularizer_eq_zero
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalSymmetricRectangleBoundaryIntegral
      (pascalCenteredXiDiskWeightedRegularizer h W.R)
      W.rectangle.σ W.rectangle.T = 0
```

pinned Mathlib の

```lean
Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
```

が利用可能なら、exceptional set は

```lean
(pascalCenteredXiZeroDiskFinset W.R : Set ℂ)
```

を使う。

既存 circle proof と同じ思想で

```text
continuous on closed rectangle
complex differentiable in open rectangle off finite set
```

を供給する。

その後、rectangle boundary safety によって patched regularizer と raw regularizer が boundary 上で一致する theorem を作り、

```lean
pascalSymmetricRectangleBoundaryIntegral
  (pascalCenteredXiDiskWeightedRawRegularizer h W.R)
  ... = 0
```

まで移す。

Gate D は Green expected。

---

# 7. Gate E — one-pole rectangle charge: XDP-012 の荷重部

次に各

```lean
pascalCenteredXiWeightedPrincipalPart h a
```

の rectangle boundary integral を評価する。

目標は、`a` が rectangle interior にあるとき

```text
rectangleIntegral(principalPart h a)
=
-(2πi) * multiplicity(a) * h(a)
```

である。

## Route E1 — existing pinned API

rectangle Cauchy integral / winding / residue theorem が pinned Mathlib に存在するなら最優先で使用する。

## Route E2 — minimal derivation

直接 API が無い場合のみ、one-pole case に限定した最小 proof を作る。

候補:

```text
small circle around a
+ rectangle Cauchy-Goursat on pole-free pieces
→ rectangle integral = small circle integral
→ existing circle principal-part theorem
```

または rectangle subdivision による内部辺 cancellation。

**一般 residue framework、一般 winding-number library、一般 polygon homologyを XDP-012 のためだけに新設しないこと。**

## Route E3 — exact Blocked boundary

E1/E2 が pinned API 上で不合理に大きい場合、次の theorem shape を named provider として固定し、Gate E を Blocked と記録してよい。

```lean
structure PascalCenteredXiRectanglePrincipalPartChargeProvider ... where
  principalPart_boundary_eq : ...
```

ただし provider の存在を `axiom` / `sorry` で偽装しない。

### Acceptance priority

```text
E1 > E2 > E3
```

Gate E が Green なら XDP-012 principal endpoint まで進む。

---

# 8. Gate F — finite principal-part sum on rectangle

Gate E が Green の場合、Finset sum と boundary integral の線形性から

```lean
theorem pascalCenteredXiRectangleIntegral_diskWeightedPrincipalPartSum_eq ...
```

を証明する。

目標:

```text
rectangle boundary integral of principal-part sum
=
-(2πi) × pascalCenteredXiZeroDiskWeightedMoment h W.R
```

各 disk zero が rectangle interior にあることは stronger transport window から供給する。

zero が rectangle boundary に無いことも safety contract から供給する。

---

# 9. Gate G — fixed-Xi rectangle residue formula

raw regularizer identity

```text
h(z) * pascalCenteredXiNegLogDeriv(z)
=
rawRegularizer(z) + principalPartSum(z)
```

を rectangle boundary integral に上げる。

Gate D の regularizer zero と Gate F を使い、

```lean
theorem pascalCenteredXiWeightedRectangleMass_eq
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiRectangleContribution h W.toContourTransportWindow =
      -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment h W.R
```

に相当する theorem を principal endpoint とする。

既存 naming に合わせて名称調整可。

### normalized companion

可能なら

```text
(2πi)⁻¹ × rectangleMass
=
-zeroDiskWeightedMoment
```

も追加する。

---

# 10. Gate H — circle = rectangle

既存 Green theorem

```lean
pascalCenteredXiWeightedOuterContourMass_eq
```

と Gate G を同じ finite weighted moment を介して接続する。

principal bridge:

```lean
theorem pascalCenteredXiWeightedRectangleMass_eq_outerContourMass ...
```

概念的に

```text
rectangle
= -2πi × finite weighted zero moment
= circle
```

である。

これは direct homotopy theorem ではなく、**共通 residue endpoint を介した equality** として証明する。

---

# 11. Gate I — XDP-011 finite explicit-formula skeleton

weight が even なら XDP-011 principal theorem と Gate G/H を合成する。

一般 even entire weightで theorem を置けるなら置く。

特に XDP-006/007 weight

```lean
centeredMellinSecondDifferenceWeight
  (centeredMellinBoxApprox ε) τ
```

については XDP-011 で evenness が Green なので、positive `ε` の specialization を追加してよい。

principal conceptual identity:

```text
-(2πi) × finite Xi zero weighted moment
=
2 × right-edge decomposed contribution
+ 2 × finite top-horizontal contribution
```

normalized version:

```text
-finite Xi zero weighted moment
=
(2πi)⁻¹ ×
  [2 × right-edge decomposed + 2 × top-horizontal]
```

### 禁止

この finite identity から horizontal term を消さない。

right-edge ordinary-zeta termを prime sum integralへまだ交換しない。

---

# 12. Existing XDP-009 conditional provider migration

XDP-009 では

```lean
PascalExplicitFormulaContourTransportProvider
```

が conditional crossed-local-charge provider として存在する。

XDP-012 Gate G/H が Green になった場合、**combined fixed-Xi observableについては、より強い実 theorem が得られたことを result report に明記する**。

ただし XDP-009 の decomposed individual-term providersを削除しない。

理由:

```text
combined fixed-Xi transport
```

と

```text
ordinary-zeta / Gamma / elementary individual transport
```

は別の責務である。

XDP-012 は前者だけを actual analytic theorem に昇格する。

---

# 13. No-circularity / safety gate

以下を仮定・import・結論に使わない。

```text
RiemannHypothesis
all nontrivial zeros on critical line
defect vanishing
horizontal energy vanishing
Weil positivity
Li positivity
prime-side sign theorem
```

same-zero-set は XDP-009 以来の explicit geometry contract として使用可。

これは RH 相当条件ではなく、選んだ finite circle / rectangle が同じ有限 zero set を囲むという localization input である。

ただし **その window の存在を無条件に主張しないこと**。XDP-012 は supplied stronger window に対する analytic theorem でよい。

---

# 14. Validation

最低限:

```text
lake env lean <new module>
lake build <new module>
./lb DkMath.RH
git diff --check
```

principal declarations:

```text
#print axioms ...
```

新規 source について:

```text
sorry
admit
axiom
native_decide
```

を禁止する。

existing unrelated warning は result report で区別する。

---

# 15. 推奨 module

第一候補:

```text
DkMath/RH/CFBRC/PascalCenteredXiExplicitFormulaRectangleResidueTransport.lean
```

必要なら geometry helper を既存

```text
PascalCenteredXiExplicitFormulaContourGeometry.lean
```

へ最小追加してよい。

既存 `OuterContourResidueBridge` の generic helper を一般化する変更も可。ただし circle theorem の既存 API / proof を壊さないこと。

公開 surface が安定したら `DkMath/RH.lean` へ import を追加する。

---

# 16. Result report 必須項目

```text
XDP-012-Fixed-Xi-circle-to-rectangle-residue-transport-result.md
```

に以下を記録する。

1. pinned rectangle Cauchy-Goursat API audit
2. stronger residue transport window の exact contract
3. rectangle regularizer continuity / differentiability status
4. patched/raw regularizer rectangle boundary integral status
5. one-pole rectangle charge Gate E の route 判定 E1/E2/E3
6. finite principal-part sum status
7. rectangle weighted Xi residue formula status
8. circle = rectangle bridge status
9. XDP-011 finite explicit-formula skeleton status
10. XDP-009 conditional provider の migration note
11. no-circularity audit
12. build / test / axioms audit

---

# 17. Phase close 判定

## Full Green

次が theorem として成立した場合:

```text
fixed Xi rectangle
= fixed Xi circle
= -2πi × same finite Xi weighted zero moment
```

かつ XDP-011 と合成して

```text
finite zero weighted moment
↔ right-edge decomposed contribution
 + finite horizontal correction
```

まで到達。

この場合、XDP-013 は

```text
right-edge ordinary-zeta interval integral
↔ Pascal / von Mangoldt cutoff integral
```

の uniform/dominated transport を primary frontier にできる。

## Partial Green / Gate E Blocked

rectangle regularizer Cauchy-Goursat まで Green だが one-pole rectangle chargeが pinned API 上で閉じない場合:

```text
regularizer transport: GREEN
one-pole residue charge: BLOCKED
```

と明記する。

この場合、次 phase は一般 explicit formula へ進まず、**one-pole rectangle charge の最小 analytic lemma**を独立 checkpoint に切る。

---

## 18. 最重要原則

XDP-012 の目的は新しい RH criterion を作ることではない。

目的は、既に Green の

```text
finite Xi zero moment ↔ fixed Xi circle
```

と

```text
fixed Xi finite rectangle ↔ right arithmetic edge + horizontal correction
```

の間にある唯一の analytic transport gap を、**combined fixed-Xi observable の residue theoryとして実際の theorem にすること**である。

Lean が閉じた範囲だけを Green とし、one-pole rectangle charge が残るならその一点を次 frontier として正確に露出させること。