# XDP-010 — Coordinate-safe functional-equation edge reflection 実装指示書

作成日: 2026-08-12

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-explicit-formula-transport-260812-v0
workdir: lean/dk_math
Lean / Mathlib: repository pinned toolchain
```

XDP-009 までで次が Green / contract 化されている。

```text
fixed centered-Xi circle
→ completed-zeta log-derivative decomposition
→ symmetric ordinary-coordinate rectangle geometry
→ singularity risk ledger
→ conditional crossed-local-charge providers
→ right edge Re(s) > 1
→ existing Pascal / von Mangoldt pointwise endpoint
```

XDP-010 の principal goal は、critical functional equation により **left vertical edge を right vertical edgeへ exact に反射し、偶 centered weight に対する vertical pair を right-edge observable へ畳むこと**である。

ただし、その前に XDP-009 で露出した centered / ordinary coordinate の型上の同一視を監査・修復する。

**XDP-010 では horizontal-edge decay、`T → ∞`、rectangle deformation/residue provider の存在、crossed charge の closed form、prime cutoff と積分の極限交換、defect sign、defect vanishing、RH を証明しない。**

---

# Gate 0 — Mandatory coordinate audit / repair

## 0.1 現在の監査対象

XDP-009 では rectangle edge は ordinary coordinate として定義されている。

```lean
pascalSymmetricRectangleRightEdge σ t
pascalSymmetricRectangleLeftEdge σ t
pascalSymmetricRectangleTopEdge u T
pascalSymmetricRectangleBottomEdge u T
```

一方、現在の named decomposed term は centered coordinate を引数に取る形である。

```lean
def pascalExplicitFormulaOrdinaryZetaTerm
    (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  h z * pascalXiOrdinaryZetaNegLogDeriv (criticalLineCenter + z)
```

同様に archimedean / elementary term も centered `z` を入力としている。

しかし現在の

```lean
pascalExplicitFormulaRectangleContribution F W
```

は ordinary rectangle edge `s` をそのまま `F` に渡す。

したがって、

```lean
pascalExplicitFormulaRectangleContribution
  (pascalExplicitFormulaOrdinaryZetaTerm h) W
```

を文字通り評価すると、rectangle の ordinary point `s` が centered `z` として扱われ、ordinary-zeta の評価点が `criticalLineCenter + s` になる。

これは型 `ℂ` が同じため Lean の type checker が検出できない coordinate-space mismatch である。

## 0.2 修復方針

以下のどちらかを採用すること。**A を第一候補**とする。

### Route A — rectangle contribution 内で ordinary → centered translation

```lean
noncomputable def pascalOrdinaryToCentered (s : ℂ) : ℂ :=
  s - criticalLineCenter
```

を導入し、centered integrand `F : ℂ → ℂ` に対して rectangle contribution を

```text
ordinary edge s
→ centered coordinate (s - 1/2)
→ F
```

として評価する canonical wrapper を作る。

例:

```lean
pascalExplicitFormulaCenteredRectangleContribution
    (F : ℂ → ℂ)
    (W : PascalCenteredXiContourTransportWindow) : ℂ
```

既存 `pascalExplicitFormulaRectangleContribution` を破壊的に変更する場合は、影響範囲を audit して全 caller を修正すること。互換 wrapper を残す方が安全ならそうしてよい。

### Route B — centered / ordinary integrand を別々に持つ provider

```text
Fcentered : ℂ → ℂ
Fordinary : ℂ → ℂ
translation_compatibility :
  Fordinary (criticalLineCenter + z) = Fcentered z
```

を provider に明示する。

ただし API が過剰に重くなる場合は Route A を優先する。

## 0.3 必須 inverse / compatibility lemmas

少なくとも次の shape を Green にする。

```text
pascalOrdinaryToCentered (pascalCenteredToOrdinary z) = z
pascalCenteredToOrdinary (pascalOrdinaryToCentered s) = s
```

さらに rectangle edge について、right / left reflection が centered coordinate で exact negation になる theorem を置く。

概念形:

```text
centered(leftEdge σ (-t)) = - centered(rightEdge σ t)
```

既存

```lean
pascalSymmetricRectangleLeftEdge_eq_one_sub_rightEdge
```

を再利用すること。

## Gate 0 acceptance

- centered circle と ordinary rectangle で同じ raw `ℂ → ℂ` を無翻訳で共有しない。
- XDP-009 transport ledger の theorem statement が coordinate-correct になる。
- 修正した API の caller を build で確認する。
- result report に mismatch と修復方法を明記する。

---

# Gate A — Fixed centered-Xi negative-log-derivative reflection

既存 theorem:

```lean
@[simp] theorem pascalCenteredRiemannXiKernel_neg
    (z : ℂ) :
    pascalCenteredRiemannXiKernel (-z) =
      pascalCenteredRiemannXiKernel z
```

を正本として使う。

目標は centered fixed kernel の negative logarithmic derivativeが odd であること。

概念 theorem:

```lean
theorem pascalCenteredXiNegLogDeriv_neg (z : ℂ) :
    pascalCenteredXiNegLogDeriv (-z) =
      -pascalCenteredXiNegLogDeriv z
```

可能なら global theorem とする。`logDeriv` の totalized division のため unnecessary な nonzero hypothesis を追加しないこと。

証明は kernel evenness と derivative transportから行う。単に completed-zeta の functional equation を手計算で展開して符号を target に埋め込まない。

必要なら以下を compile-probe すること。

```text
deriv_neg
HasDerivAt.neg
HasDerivAt.comp
Filter.EventuallyEq.deriv_eq
```

pinned API の exact theorem name を確認してから実装する。

---

# Gate B — Combined decomposed term reflection

XDP-008 の三項をまとめた named observable を追加してよい。

概念定義:

```lean
noncomputable def pascalXiDecomposedNegLogDeriv (s : ℂ) : ℂ :=
  pascalXiOrdinaryZetaNegLogDeriv s +
    pascalXiArchimedeanLogDeriv s +
    pascalXiElementaryLogDerivCorrection s
```

重要:

**ordinary-zeta / Gammaℝ / elementary の各項が個別に reflection law を持つとは主張しない。**

functional equation が保証するのは completed object / fixed Xi の合計である。

右辺・左辺の decomposition hypotheses が満たされる点では、XDP-008 theorem を使って

```text
D(1 - s) = -D(s)
```

を導いてよい。

ただし left side が trivial-zero / Gamma exceptional location に当たる場合、三項個別 decomposition を強制しない。そこでは fixed Xi combined observable を正本として残す。

---

# Gate C — Even centered weights

最終 quadratic weight `z ↦ z^2` を principal application とするため、centered evenness を named predicate / theorem shape にする。

候補:

```lean
def PascalCenteredEvenWeight (h : ℂ → ℂ) : Prop :=
  ∀ z, h (-z) = h z
```

あるいは既存の標準 predicate が適切なら再利用する。

必須 specialization:

```text
z ↦ z^2 is even
```

XDP-007 の approximate-identity family 自体の mirror self-duality I/J は今回要求しない。

XDP-010 の principal exact theorem は **exact quadratic weight または任意の even centered weight** に対して成立すればよい。

---

# Gate D — Weighted centered-Xi integrand is odd

centered weight `h` に対し

```text
F_h(z) := h(z) * pascalCenteredXiNegLogDeriv(z)
```

を named observable としてよい。

`h` が even なら Gate A より

```text
F_h(-z) = -F_h(z)
```

を Green にする。

この theorem は vertical-edge pairing の pointwise kernel となる。

---

# Gate E — Right-edge automatic decomposition safety

right edge は

```text
s = σ + i t
1 < σ
```

である。

したがって既存 API を再利用して、right edge 上で XDP-008 decomposition に必要な条件を自動的に供給する。

少なくとも:

```text
s ≠ 0
s ≠ 1
riemannZeta s ≠ 0
Complex.Gammaℝ s ≠ 0
```

を `1 < s.re` から導く。

候補 existing API:

```text
riemannZeta_ne_zero_of_one_le_re
gammaR_ne_zero_of_pos_re
one_lt_re_pascalSymmetricRectangleRightEdge
```

これにより right edge では

```text
pascalCenteredXiNegLogDeriv(centered s)
```

またはその ordinary-coordinate translation が

```text
ordinary-zeta + archimedean + elementary
```

へ **無条件に pointwise decomposition** できる theorem を作る。

ここでいう「無条件」は rectangle parameter `hσ : 1 < σ` の内部で、追加の zeta/Gamma nonzero hypothesis を caller に要求しないという意味である。

---

# Gate F — Vertical-edge reflection with orientation

XDP-009 geometry:

```lean
pascalSymmetricRectangleLeftEdge σ (-t) =
  1 - pascalSymmetricRectangleRightEdge σ t
```

および Gate 0 の coordinate translation を使う。

centered even weight `h` に対して、left edge の fixed-Xi weighted integrand を right edgeへ pointwise に反射する。

orientation を必ず含めること。

XDP-009 boundary convention は:

```text
right edge : t = -T → T
left edge  : t =  T → -T
```

である。

したがって integrand の odd reflection と path reversal が二重に符号を反転し、vertical pair は概念的に

```text
left vertical contribution + right vertical contribution
→ 2 * right vertical contribution
```

となる。

ここは手計算の符号を theorem target に直接押し込まず、interval integral の substitution / reversal API で証明する。

pinned Mathlib で以下周辺を audit / compile-probe すること。

```text
intervalIntegral.integral_symm
intervalIntegral.integral_comp_sub_left
intervalIntegral.integral_comp_sub_right
intervalIntegral.integral_comp_mul_deriv
```

exact API が無い場合は、必要最小限の affine substitution lemma を generic Analysis/Core 側に作ってよい。

---

# Gate G — Principal paired vertical-edge theorem

最終 principal endpoint は、even centered weight `h` と symmetric rectangle `W` に対し、fixed-Xi vertical pair を **right-edge decomposed observable の2倍**として表す theorem。

概念形:

```text
Xi-left-edge(h, W) + Xi-right-edge(h, W)
  = 2 * right-edge-integral(
      h × (ordinary-zeta + archimedean + elementary))
```

ただし数式の具体的 orientation / coordinate wrapper は実装後の canonical definition に合わせる。

重要:

- left edge で ordinary-zeta / Gamma / elementary を個別分解しなくてよい。
- left side は fixed Xi combined observable のまま reflection する。
- right edge だけを `Re(s) > 1` で三項分解する。
- これにより trivial-zero / Gamma cancellation を left edge で個別に展開する必要を避ける。

これは XDP-009 の singularity ledger を無視するのではない。**cancellation 済み fixed Xi を left edge の正本にすることで、個別 singularity を不正に分離しない**という設計である。

---

# Gate H — Right-edge prime endpoint preservation

XDP-009 の

```lean
tendsto_pascalPrimePowerPHZFiniteUpTo_pascalXiOrdinaryZetaNegLogDeriv_rightEdge
```

を再利用する。

XDP-010 では pointwise adapter より先へ進まない。

特に禁止:

```text
Tendsto pointwise
→ intervalIntegral Tendsto
```

という無条件交換。

uniform / dominated convergence が必要なら XDP-011 以降の named gap とする。

---

# Gate I — Horizontal edges remain explicit

XDP-010 の rectangle identity では top / bottom edge を消さない。

functional reflection により top/bottom の pointwise pairing theorem を追加するのは可。ただし

```text
horizontal pair = 0
horizontal pair → 0 as T → ∞
```

を証明してはならない。後者には growth / decay estimate が必要であり、XDP-011 の principal task とする。

可能なら horizontal reflection geometry の exact identityだけを Green にする。

---

# Gate J — XDP-009 coordinate repair migration

Gate 0 で XDP-009 public API を修正した場合、以下を必ず実施する。

```text
DkMath/RH.lean public import remains Green
XDP-009 modules rebuild
XDP-009 result report addendum or XDP-010 result report records migration
```

既存 theorem の意味が変わる場合は docstring を更新する。

単に build が通るだけでなく、circle contribution が centered coordinate、rectangle contribution が ordinary coordinateから正しく centered translation されることを theorem で監査する。

---

# Proposed modules

第一候補:

```text
DkMath/RH/CFBRC/PascalCenteredXiExplicitFormulaFunctionalEquationReflection.lean
```

Gate 0 の修復は必要に応じて既存

```text
PascalCenteredXiExplicitFormulaContourGeometry.lean
PascalCenteredXiExplicitFormulaContourTransport.lean
```

へ加える。

公開 endpoint が安定したら `DkMath/RH.lean` に import を追加する。

result report:

```text
DkMath/RH/CFBRC/docs/wip/RH-CFBRC-explicit-formula-transport/
XDP-010-Coordinate-safe-functional-equation-edge-reflection-result.md
```

---

# Acceptance checklist

## Principal Green requirements

- [ ] Gate 0: centered / ordinary coordinate mismatch を監査・修復
- [ ] ordinary ↔ centered inverse lemmas
- [ ] left/right edge centered reflection theorem
- [ ] fixed centered-Xi negative log derivative oddness
- [ ] even centered-weight predicate / quadratic specialization
- [ ] weighted fixed-Xi integrand oddness
- [ ] right edgeの decomposition hypotheses を `1 < σ` から自動供給
- [ ] right edge fixed-Xi → zeta + Gamma + elementary pointwise decomposition
- [ ] interval-integral orientation を含む left/right vertical pairing
- [ ] vertical pair = 2 × right-edge decomposed contribution
- [ ] existing pointwise prime endpoint hook を保持
- [ ] horizontal edgesを未処理の named contribution として残す
- [ ] public import / build Green
- [ ] no new `sorry`, `admit`, `axiom`, `native_decide`
- [ ] principal declarations の `#print axioms` audit

## Explicitly out of scope

- rectangle deformation / residue theorem provider の存在証明
- crossed local charge closed form
- trivial-zero / Gamma residue coefficient の個別評価
- horizontal edge decay
- `T → ∞`
- prime cutoff と vertical integral の limit exchange
- full Guinand–Weil explicit formula
- fixed defect sign / vanishing
- RH

---

# Failure / Blocked policy

principal theorem が pinned Mathlib の interval-integral substitution API 不足で閉じない場合、provider を新しい axiom/structure field で偽装しない。

その場合は次を result report に記録する。

1. pointwise reflection まで Green か。
2. coordinate repair は完了したか。
3. exact missing affine-substitution theorem shape。
4. generic interval-integral lemma を DkMath Analysis に追加すれば閉じるか。
5. horizontal decay / residue / limit exchangeとは独立の純粋 geometry obstruction であること。

---

# XDP-010 完了後の想定 frontier

XDP-010 が principal endpoint まで Green なら、rectangle の vertical pair は right-half-plane observable に圧縮される。

次 phase の第一候補は:

```text
XDP-011 — Horizontal-edge growth/decay audit and T → ∞ transport
```

概念 chain:

```text
fixed Xi rectangle
→ vertical pair = 2 × right edge
→ top/bottom horizontal remainder
→ horizontal decay as T → ∞
→ right-edge integral only
→ prime-side limit transport
```

ただし XDP-011 でも prime cutoff / integral limit exchange と horizontal decay は別 gate として扱うこと。
