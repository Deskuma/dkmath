# XDP-013 — Rectangle one-pole Cauchy charge realization 実装指示書

作成日: 2026-08-12

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-explicit-formula-transport-260812-v0
workdir: lean/dk_math
Lean / Mathlib: repository pinned toolchain
```

XDP-012 は `Partial Green / Gate E Blocked` で閉じた。

Green surface は次である。

```text
fixed centered-Xi weighted integrand
→ finite principal-part subtraction
→ removable patch
→ rectangle closed-set continuity
→ rectangle open-set differentiability off finite zero set
→ pinned rectangle Cauchy–Goursat
→ patched regularizer boundary integral = 0
→ raw regularizer boundary integral = 0
```

残った本質的 blocker は一極の矩形 charge だけである。

概念的 target:

```text
a is strictly inside rectangle
→ ∮∂Rect (s - a)⁻¹ ds = 2πi
→ weighted principal-part charge
→ finite principal-part sum
→ fixed-Xi rectangle residue formula
→ circle = rectangle
→ XDP-011 finite explicit-formula skeleton
```

本 phase はこの Gate E を閉じるための **micro-checkpoint** とする。

一般 residue framework、一般 winding theory、一般 homotopy library は作らない。必要な rectangle Cauchy kernel theorem と、その XDP-012 への specialization だけを実装する。

---

# Gate 0 — Mandatory coordinate-contract repair

## 0.1 XDP-012 provider に残る型上の mismatch

XDP-012 の current provider は次の shape を持つ。

```lean
structure PascalCenteredXiRectanglePrincipalPartChargeProvider
    (h : ℂ → ℂ) (W : PascalCenteredXiResidueTransportWindow) where
  principalPart_boundary_eq : ∀ {a : ℂ},
    a ∈ pascalCenteredXiZeroDiskFinset W.R →
    pascalSymmetricRectangleBoundaryIntegral
      (pascalCenteredXiWeightedPrincipalPart h a)
      W.rectangle.σ W.rectangle.T =
      -(2 * Real.pi * Complex.I) *
        (pascalCenteredXiZeroMultiplicity a : ℂ) * h a
```

しかし `pascalSymmetricRectangleBoundaryIntegral` の入力点は ordinary coordinate `s` であり、`pascalCenteredXiWeightedPrincipalPart h a w` の `w` は centered coordinate である。

XDP-012 の regularizer 側は既に

```lean
fun s =>
  pascalCenteredXiDiskWeightedRegularizer h W.R
    (pascalOrdinaryToCentered s)
```

として正しく translation しているため、Gate E provider だけが coordinate-safe surface から外れている。

### 必須修正

principal part も rectangle 上では必ず ordinary-to-centered translation を通すこと。

推奨 shape:

```lean
pascalSymmetricRectangleBoundaryIntegral
  (fun s =>
    pascalCenteredXiWeightedPrincipalPart h a
      (pascalOrdinaryToCentered s))
  W.rectangle.σ W.rectangle.T
```

あるいは既存 canonical wrapper

```lean
pascalExplicitFormulaCenteredRectangleContribution
  (pascalCenteredXiWeightedPrincipalPart h a)
  W.toContourTransportWindow
```

を使ってよい。

**raw ordinary rectangle に centered function を直接渡す旧 contract を principal API として残さないこと。**

必要なら旧 declaration を削除・置換し、XDP-012 result report に migration addendum を追記する。

---

# Gate A — Ordinary pole coordinate bridge

centered zero `a` に対応する ordinary pole location を明示する。

```lean
noncomputable def pascalCenteredXiOrdinaryPole (a : ℂ) : ℂ :=
  pascalCenteredToOrdinary a
```

最低限、次の exact coordinate identity を証明する。

```lean
pascalOrdinaryToCentered s - a =
  s - pascalCenteredToOrdinary a
```

これにより rectangle 上の pulled-back principal part を ordinary Cauchy kernel へ変形できる。

目標形:

```lean
pascalCenteredXiWeightedPrincipalPart h a
    (pascalOrdinaryToCentered s) =
  (-(pascalCenteredXiZeroMultiplicity a : ℂ) * h a) *
    (s - pascalCenteredToOrdinary a)⁻¹
```

ここは純代数で Green にすること。

---

# Gate B — Generic ordinary rectangle boundary integral

XDP-009 の symmetric rectangle は一種類しかなく、one-pole proof の局所 subdivision には任意の axis-aligned subrectangle が必要になる。

一般 residue framework ではなく、**4辺積分だけの small generic helper** を導入してよい。

推奨:

```lean
noncomputable def pascalRectangleBoundaryIntegral
    (F : ℂ → ℂ)
    (xL xR yB yT : ℝ) : ℂ :=
  ...
```

orientation は XDP-009 と一致させる。

```text
bottom: xL → xR
right : yB → yT
 top  : xR → xL
 left  : yT → yB
```

vertical side には `Complex.I` factor を含める。

そして symmetric specialization を Green にする。

```lean
pascalRectangleBoundaryIntegral F
    (1 - σ) σ (-T) T =
  pascalSymmetricRectangleBoundaryIntegral F σ T
```

既存 definition を壊さず adapter として置くこと。

---

# Gate C — Rectangle subdivision algebra

one-pole theorem のために、boundary integral の **有限 subdivision additivity** だけを実装する。

少なくとも次の二種を用意する。

```text
vertical split:
Rect[xL,xR] = Rect[xL,c] + Rect[c,xR]

horizontal split:
Rect[yB,yT] = Rect[yB,d] + Rect[d,yT]
```

境界の内部辺が orientation 反転で相殺される形を interval integral の additivity / symmetry で証明する。

必要ならこの二つを組み合わせて 3×3 grid の theorem を作る。

重要:

- 一般 chain complex を作らない。
- polygon library を作らない。
- homology / winding abstraction を作らない。
- current rectangle integral に必要な有限代数だけに留める。

---

# Gate D — Interior pole around a small centered square

ordinary pole

```lean
p := pascalCenteredToOrdinary a
```

が open rectangle に入るとき、`p` を中心とする正方形が rectangle 内に strict に収まることを示す。

実装は二段階を推奨する。

## D1. Explicit square hypothesis theorem

まず `δ` を受け取る theorem を作る。

```text
0 < δ
xL < p.re - δ
p.re + δ < xR
yB < p.im - δ
p.im + δ < yT
```

のもとで small square を扱う。

## D2. Existence from open-rectangle membership

その後、

```lean
p ∈ Set.Ioo xL xR ×ℂ Set.Ioo yB yT
```

からそのような `δ > 0` の存在を構成する。

例えば四つの side distance の正の minimum の半分を使ってよい。

`Classical.choose` は不要なはずだが、proof convenience のために使う場合でも通常 axioms surface を越えないことを確認する。

---

# Gate E1 — Cauchy kernel vanishes on pole-free subrectangles

ordinary Cauchy kernel

```lean
fun s : ℂ => (s - p)⁻¹
```

について、closed subrectangle が `p` を含まない場合、その boundary integral が `0` である theorem を作る。

ここでは pinned

```lean
Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
```

またはより単純な rectangle Cauchy–Goursat API を再利用する。

pole-free closed rectangle では kernel は continuous / differentiable なので、exceptional set を空にできるなら空を使う。

この theorem は specialized helper で十分。

---

# Gate E2 — Big rectangle charge reduces to small square charge

D の small square を中心に 3×3 grid で big rectangle を分割する。

概念的には

```text
+---------+---------+---------+
|    0    |    0    |    0    |
+---------+---------+---------+
|    0    |  pole   |    0    |
+---------+---------+---------+
|    0    |    0    |    0    |
+---------+---------+---------+
```

center square 以外の8個の subrectangle は pole-free なので Gate E1 で boundary integral `0`。

Gate C の subdivision algebra により、big rectangle boundary integral は center square boundary integral と一致する。

ここが XDP-012 の E2 に相当するが、一般 residue theory ではなく **one-pole specialized finite subdivision proof** として閉じる。

---

# Gate E3 — Compute the centered square Cauchy charge

ここが principal analytic micro-lemma である。

`δ > 0` に対して、原点中心 square

```text
[-δ,δ] × [-δ,δ]
```

の positively oriented boundary で

```text
∮ dz / z = 2πi
```

を interval integrals だけで直接計算する。

translation により pole `p` 中心 square も同じ charge を持つ。

## 推奨計算

vertical pair は奇関数成分が消え、概念的に

```text
2 i δ ∫_{-δ}^{δ} dt / (δ² + t²)
```

へ落ちる。

horizontal pair も同じ値になる。

実数積分 helper として

```text
δ ∫_{-δ}^{δ} dt / (δ² + t²) = π / 2
```

を `Real.arctan` の微分から証明するのが第一候補。

必要な pinned API は実装前に `#check` / grep で確認すること。候補名を記憶で決め打ちしない。

もし interval substitution の方が簡単なら

```text
t = δ u
```

で `[-1,1]` へ rescale してから `arctan` を使ってよい。

### principal generic theorem

最終的に次に相当する theorem を Green にする。

```lean
p ∈ Set.Ioo xL xR ×ℂ Set.Ioo yB yT →
  pascalRectangleBoundaryIntegral
      (fun s : ℂ => (s - p)⁻¹)
      xL xR yB yT =
    2 * Real.pi * Complex.I
```

orientation sign は XDP-009 / XDP-012 の convention と照合すること。

**符号を textbook memory から決め打ちしない。small-square explicit computation を正本とする。**

---

# Gate F — XDP-012 principal-part provider realization

Gate 0 で修正した coordinate-safe provider に actual constructor / existence theorem を与える。

例えば:

```lean
noncomputable def pascalCenteredXiRectanglePrincipalPartChargeProvider
    ...
```

を structure のまま使うなら、次の constructor theorem を作る。

```lean
pascalCenteredXiRectanglePrincipalPartChargeProvider_of_differentiable
```

ただし principal-part charge 自体には `Differentiable h` は本質的に不要であるため、不要なら仮定しない。

`a ∈ pascalCenteredXiZeroDiskFinset W.R` から

```text
a ∈ centered Xi zeros
→ a ∈ ball R
→ same-zero-set
→ pascalCenteredToOrdinary a ∈ open rectangle
```

を得て Gate E3 を適用する。

constant scalar

```text
-(multiplicity a) * h a
```

を Cauchy kernel charge に掛けて

```text
rectangle principal-part charge
= -2πi * multiplicity(a) * h(a)
```

を得る。

---

# Gate G — Finite principal-part sum charge

provider が actual theorem になった後、finite sum を閉じる。

目標:

```text
rectangle boundary integral of
  pascalCenteredXiDiskWeightedPrincipalPartSum h W.R
=
-2πi * pascalCenteredXiZeroDiskWeightedMoment h W.R
```

注意:

- boundary 上に pole がないことは `rectangle_boundary_safe` と same-zero-set から供給する。
- finite sum と interval integral の交換は有限和なので、通常の linearity だけでよい。
- infinite convergence theorem は不要。

---

# Gate H — Actual fixed-Xi rectangle residue formula

XDP-012 Green theorem

```lean
pascalCenteredXiRectangleIntegral_diskWeightedRawRegularizer_eq_zero
```

と Gate G を合成する。

raw decomposition は centered coordinate で

```text
weighted Xi integrand
= raw regularizer + principal-part sum
```

である。

rectangle では ordinary-to-centered translation を必ず保持する。

principal target:

```lean
pascalCenteredXiWeightedRectangleMass_eq
    {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (W : PascalCenteredXiResidueTransportWindow) :
  pascalCenteredXiRectangleContribution h W.toContourTransportWindow =
    -(2 * Real.pi * Complex.I) *
      pascalCenteredXiZeroDiskWeightedMoment h W.R
```

実際の declaration 名は current API と衝突しないよう調整してよい。

---

# Gate I — Circle = rectangle bridge

既存 circle theorem

```lean
pascalCenteredXiWeightedOuterContourMass_eq
```

と Gate H は同じ finite weighted zero moment に等しい。

従って actual theorem として

```text
fixed Xi rectangle contribution
= fixed Xi circle contribution
```

を出す。

仮定は少なくとも

```text
Differentiable ℂ h
PascalCenteredXiResidueTransportWindow W
```

で十分なはずである。

ここでは homotopy theorem を使う必要はない。

---

# Gate J — XDP-011 finite explicit-formula skeleton

`h` が even centered weight でもある場合、XDP-011 の

```lean
pascalCenteredXiRectangleContribution_eq_two_right_decomposed_add_two_top
```

と Gate H を合成する。

principal finite skeleton:

```text
-2πi × finite Xi weighted zero moment
=
2 × right-edge decomposed contribution
+ 2 × finite top-horizontal contribution
```

これを actual theorem として公開する。

推奨 theorem shape:

```lean
pascalCenteredXiFiniteExplicitFormulaSkeleton
    {h : ℂ → ℂ}
    (hhDiff : Differentiable ℂ h)
    (hhEven : PascalCenteredEvenWeight h)
    (W : PascalCenteredXiResidueTransportWindow) :
  -(2 * Real.pi * Complex.I) *
      pascalCenteredXiZeroDiskWeightedMoment h W.R =
    2 * (...) +
    2 * pascalCenteredXiTopHorizontalContribution h
      W.toContourTransportWindow
```

exact right-edge expression は XDP-011 theorem の既存 RHS を再利用すること。

---

# Gate K — Quadratic / Mellin specialization

principal generic skeleton が Green になった後、低コストなら次を追加してよい。

1. `h z := z ^ 2` specialization
2. fixed `ε > 0, τ` の
   `centeredMellinSecondDifferenceWeight (centeredMellinBoxApprox ε) τ`
   specialization

ただし XDP-013 で

```text
τ → 0
ε → 0⁺
prime cutoff X → ∞
T → ∞
```

の極限交換を行わない。

XDP-013 の目的は one-pole rectangle charge と finite skeleton の実体化までである。

---

# Gate L — Migration / audit

XDP-012 result report に migration addendum を追記する。

最低限、次を記録する。

```text
Gate E provider coordinate mismatch repaired
one-pole rectangle charge: Green / Blocked
provider existence: Green / Blocked
finite principal-part sum: Green / Blocked
rectangle residue formula: Green / Blocked
circle = rectangle: Green / Blocked
finite explicit-formula skeleton: Green / Blocked
```

もし one-pole charge が閉じられなかった場合でも、blocker は必ず以下の粒度まで絞る。

```text
small-square explicit integral
subdivision algebra
arctan integral normalization
```

「Mathlib に residue theorem がない」で止めないこと。今回は E2 specialized derivation を明示的に許可している。

---

# 実装優先順位

```text
1. Gate 0 coordinate repair
2. Gate A ordinary pole identity
3. Gate B/C generic rectangle + subdivision
4. Gate D small square existence
5. Gate E1 pole-free rectangles
6. Gate E2 big rectangle → center square
7. Gate E3 explicit square charge = 2πi
8. Gate F provider realization
9. Gate G finite principal-part sum
10. Gate H rectangle residue formula
11. Gate I circle = rectangle
12. Gate J finite explicit-formula skeleton
13. optional Gate K specializations
```

Gate 0 を飛ばして Gate E を証明してはならない。

---

# 禁止事項 / circularity gate

XDP-013 では以下を禁止する。

```text
RH
critical-line concentration
fixed defect vanishing
horizontal energy vanishing
Weil/Li positivity criterion
unproved residue provider
axiom / sorry / admit / native_decide
```

また、次も禁止する。

```text
provider field を theorem と呼ぶ
circle charge を rectangle charge と同一視する
centered principal part を ordinary rectangle に直接渡す
one-pole theorem を general residue framework の axiomatizationで代用する
```

---

# 検証

最低限:

```text
lake env lean <new module>
lake build <new module>
./lb DkMath.RH
git diff --check
```

principal declarations について `#print axioms` を確認する。

新規 source に

```text
sorry
admit
axiom
native_decide
```

を追加しない。

既存 unrelated warning は result report で分離記録する。

---

# 完了判定

## Full Green

次が actual theorem として成立する場合。

```text
one-pole rectangle Cauchy charge
→ coordinate-safe principal-part provider realization
→ finite principal-part sum charge
→ fixed-Xi rectangle residue formula
→ circle = rectangle
→ finite explicit-formula skeleton
```

## Partial Green

small-square / subdivision の一部まで Green だが、one-pole charge の exact `2πi` normalization が閉じない場合。

この場合は blocker を具体的な interval-integral lemma まで特定すること。

---

# XDP-014 handoff 候補

XDP-013 が Full Green なら、次は finite skeleton の **right-edge prime transport** を principal frontier とする。

候補:

```text
XDP-014 — Right-edge prime-cutoff interval transport
```

狙い:

```text
right-edge ordinary-zeta integral
→ finite Pascal prime-power cutoff integral
→ uniform / dominated convergence audit
```

horizontal term は finite correction として保持し、`T → ∞` はまだ自動的に導入しない。
