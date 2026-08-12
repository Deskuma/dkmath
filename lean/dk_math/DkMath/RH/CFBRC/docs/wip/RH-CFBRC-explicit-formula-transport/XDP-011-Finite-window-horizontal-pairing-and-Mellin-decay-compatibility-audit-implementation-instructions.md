# XDP-011 — Finite-window horizontal pairing / Mellin-decay compatibility audit 実装指示書

作成日: 2026-08-12

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-explicit-formula-transport-260812-v0
workdir: lean/dk_math
Lean / Mathlib: repository pinned toolchain
```

XDP-010 までで、fixed centered-Xi observable と symmetric rectangle の vertical pair は、even centered weight のもとで exact に right edge へ畳まれている。

principal endpoint:

```lean
pascalCenteredXiVerticalPair_eq_two_right_decomposed
```

概念的には

```text
left vertical + right vertical
→ 2 × right vertical
→ 2 × decomposed right-edge observable
→ Re(s) > 1
→ existing Pascal / von Mangoldt pointwise endpoint
```

まで Green である。

XDP-011 の目的は、残る top / bottom horizontal contributions を finite-window geometry のまま exact に整理し、同時に XDP-006/007 由来の Mellin-admissible weight が imaginary direction で持つ decay を **fixed-window transport と混同せず** 監査することである。

本 phase の principal endpoint は

```text
four-edge fixed-Xi rectangle
→ 2 × right-edge decomposed contribution
 + 2 × one horizontal contribution
```

という finite-height identity である。

**XDP-011 では fixed contour transport window のまま `T → ∞` を取らない。**

また、rectangle deformation / residue provider の存在、crossed charge の closed form、prime cutoff と積分の極限交換、defect sign、defect vanishing、RH は証明しない。

---

# 1. 重要な設計修正 — fixed window と `T → ∞` は両立しない

XDP-009 の

```lean
structure PascalCenteredXiContourTransportWindow where
  R : ℝ
  rectangle : PascalCenteredXiSymmetricRectangle
  hR : 0 < R
  zero_mem_iff : ∀ z ∈ pascalCenteredXiZeros,
    z ∈ Metric.ball (0 : ℂ) R ↔
      pascalCenteredToOrdinary z ∈
        pascalSymmetricRectangleInterior rectangle.σ rectangle.T
```

は、fixed centered circle と finite rectangle が **同じ centered-Xi zero set を囲む**契約である。

したがって `R` と `σ` を固定したまま `T → ∞` とすると、rectangle が circle 外の高い零点を新たに含む可能性があり、この `zero_mem_iff` を自動的に保持できない。

よって、次の shortcut を禁止する。

```text
fixed W
→ let W.rectangle.T → ∞
→ horizontal edges vanish
→ same-zero-set remains valid
```

これは証明されていないだけではなく、一般には localization contract と衝突する。

XDP-011 ではこの点を docstring / result report に明示し、必要なら小さな obstruction API として形式化する。

---

# Gate A — Horizontal reflection geometry

既存:

```lean
pascalSymmetricRectangleBottomEdge_eq_one_sub_topEdge
pascalOrdinaryToCentered
criticalLineCenter
```

を使い、ordinary coordinate の top / bottom reflection を centered coordinate の negation に輸送する。

主 target shape:

```lean
theorem pascalOrdinaryToCentered_bottomEdge_reflected_eq_neg_topEdge ... :
  pascalOrdinaryToCentered
      (pascalSymmetricRectangleBottomEdge (1 - u) T) =
    -pascalOrdinaryToCentered
      (pascalSymmetricRectangleTopEdge u T)
```

既存 theorem で直接済むなら新しい theorem を増やさず adapter のみにする。

重要:

- top edge orientation は `σ → 1 - σ`
- bottom edge orientation は `1 - σ → σ`
- reflection `u ↦ 1 - u` による interval orientation を Lean theorem で処理する
- 手計算だけで符号を決めない

---

# Gate B — Horizontal weighted-integrand reflection

XDP-010 の

```lean
PascalCenteredEvenWeight
pascalCenteredXiWeightedNegLogDeriv
pascalCenteredXiWeightedNegLogDeriv_neg
```

を再利用する。

`hh : PascalCenteredEvenWeight h` のもとで、top / bottom edge integrands が reflection と orientation により pairing 可能であることを Green にする。

主 target:

```text
bottom reflected integrand
→ negative of top integrand before path reversal
→ orientation reversal cancels the sign
```

vertical edge と同じく、pointwise reflection と interval orientation を別段階で証明すること。

---

# Gate C — Horizontal pair identity

既存:

```lean
pascalCenteredXiTopHorizontalContribution
pascalCenteredXiBottomHorizontalContribution
```

について、even centered weight のもとで

```lean
theorem pascalCenteredXiBottomHorizontalContribution_eq_top ... :
  pascalCenteredXiBottomHorizontalContribution h W =
    pascalCenteredXiTopHorizontalContribution h W
```

を目標とする。

続いて

```lean
theorem pascalCenteredXiHorizontalPair_eq_two_top ... :
  pascalCenteredXiTopHorizontalContribution h W +
      pascalCenteredXiBottomHorizontalContribution h W =
    2 * pascalCenteredXiTopHorizontalContribution h W
```

を Green にする。

もし orientation convention により principal representative が bottom の方が自然なら、top / bottom を逆にしてよい。ただし result report に実際の符号と orientation を明記すること。

---

# Gate D — Full finite rectangle reduction

centered-coordinate fixed-Xi weighted integrandの canonical rectangle contributionを一つ定義するか、既存

```lean
pascalExplicitFormulaCenteredRectangleContribution
```

を再利用する。

weight:

```lean
fun z => h z * pascalCenteredXiNegLogDeriv z
```

に対し、4 edge の定義展開から

```text
rectangle boundary
→ right + top + left + bottom
→ vertical pair + horizontal pair
```

を exact に整理する。

XDP-010 の

```lean
pascalCenteredXiVerticalPair_eq_two_right_decomposed
```

と Gate C を組み合わせ、principal theorem として

```text
full centered-Xi rectangle contribution
=
2 × right-edge decomposed contribution
+ 2 × top-horizontal fixed-Xi contribution
```

を Green にする。

目標概念式:

\[
I_{\partial\mathcal R}(h)
=
2I_{\mathrm R}^{\mathrm{dec}}(h)
+
2I_{\mathrm H}(h).
\]

ここで `I_H` は有限 `T` の named horizontal contribution のままでよい。

**`I_H = 0` を主張してはならない。**

---

# Gate E — XDP-006/007 Mellin weight の evenness

XDP-006/007 の正本 API:

```lean
DkMath.Analysis.centeredMellinSecondDifferenceWeight
DkMath.Analysis.centeredMellinSecondDifferenceWeight_eq_kernel_mul
DkMath.Analysis.centeredMellinSpectralWeight
DkMath.Analysis.centeredMellinBoxApprox
DkMath.Analysis.centeredMellinSpectralWeight_centeredMellinBoxApprox_eq_logAverage
DkMath.Analysis.tendsto_centeredMellinSecondDifferenceWeight_zero
DkMath.Analysis.tendsto_centeredMellinSpectralWeight_centeredMellinBoxApprox_one
```

finite explicit-formula phase で使う principal weight candidate は

```lean
fun z =>
  centeredMellinSecondDifferenceWeight
    (centeredMellinBoxApprox ε) τ z
```

である。

まず box spectral weight の centered evenness を証明できるか監査する。

数学的には

\[
H_\varepsilon(z)
=
\frac{1}{2\varepsilon}
\int_{-\varepsilon}^{\varepsilon}e^{tz}\,dt
\]

なので、`t ↦ -t` 置換により

\[
H_\varepsilon(-z)=H_\varepsilon(z)
\]

が期待される。

次に symmetric second-difference kernel 自体も `z ↦ -z` で不変なので、可能なら

```lean
theorem centeredMellinSecondDifferenceWeight_centeredMellinBoxApprox_even
    {ε τ : ℝ} (hε : 0 < ε) :
    PascalCenteredEvenWeight
      (centeredMellinSecondDifferenceWeight
        (centeredMellinBoxApprox ε) τ)
```

または generic Analysis theorem + CFBRC thin adapter を Green にする。

実装方針:

1. まず generic `DkMath.Analysis` に置くべき theorem か監査する。
2. log-average の interval substitutionで box spectral evenness を得る。
3. `τ = 0` / `τ ≠ 0` を分け、patched definition を正しく扱う。
4. `centeredMellinSecondDifferenceWeight_eq_kernel_mul` を使う場合は `τ ≠ 0` branch のみ。

mirror self-duality `h^∨ = h` は不要。XDP-007 I/J の blocked API を再開しない。

---

# Gate F — Mellin weight-only imaginary-direction decay audit

ここは **full horizontal integrand decay ではない**。

固定

```text
ε > 0
τ ≠ 0  （必要なら τ arbitrary を分岐）
u ∈ [1 - σ, σ]
```

について

```lean
centeredMellinSecondDifferenceWeight
  (centeredMellinBoxApprox ε) τ
  (pascalOrdinaryToCentered
    (pascalSymmetricRectangleTopEdge u T))
```

が `T → +∞` で `0` へ行くことを証明できるか監査する。

数学的背景:

box Mellin weight は

\[
H_\varepsilon(z)
=
\frac{1}{2\varepsilon}
\int_{-\varepsilon}^{\varepsilon}e^{tz}\,dt
\]

で、固定 `Re z` 上では Fourier-type oscillatory average となる。

`z ≠ 0` で explicit primitive を使えば

\[
H_\varepsilon(z)
=
\frac{e^{\varepsilon z}-e^{-\varepsilon z}}
{2\varepsilon z}
\]

が候補となるため、bounded real strip 上で概ね `O(1 / |Im z|)` が期待される。

一方、fixed `τ` の symmetric exponential second-difference kernel は bounded real strip 上で imaginary part に指数増大しない。

よって weight-only では decay が期待される。

ただし pinned Mathlib で explicit complex exponential interval integral / norm estimate が高コストなら、以下の優先順位でよい。

```text
F1. exact closed form + explicit bound + Tendsto 0
F2. direct Fourier/Riemann-Lebesgue theorem が pinned Mathlib にあれば再利用
F3. named decay provider contract + exact obstruction audit
```

**F3 でも XDP-011 principal Gate A–E/D は失敗扱いにしない。**

---

# Gate G — Xi log-derivative growth を weight decay と混同しない

horizontal fixed-Xi integrand は

\[
h_{\varepsilon,\tau}(z)
\,\operatorname{pascalCenteredXiNegLogDeriv}(z)
\]

である。

weight-only decay

\[
h_{\varepsilon,\tau}(u+iT)\to0
\]

だけから horizontal integral の消滅を結論してはならない。

必要なのは別途、少なくとも

```text
Xi negative-log-derivative の horizontal growth bound
zero / near-zero avoidance height
uniformity in u over the finite horizontal segment
```

である。

古典的には suitable height sequence を選ぶ方法があり得るが、XDP-011 では未証明 theorem を導入しない。

必要なら次のような **明示的 provider shape のみ**定義してよい。

```lean
structure PascalCenteredXiHorizontalAnalyticProvider (...) where
  heights : ℕ → ℝ
  heights_tendsto_atTop : Tendsto heights atTop atTop
  boundary_nonzero : ...
  uniform_logDeriv_bound : ...
  horizontal_weighted_tendsto_zero : ...
```

ただし provider の存在を証明しない限り、full horizontal decay Green とは記録しない。

---

# Gate H — Fixed-window localization obstruction API

可能なら、`T` を大きくする際の same-zero-set contract の破綻条件を小さな theorem として形式化する。

例えば、固定 `R, σ` と `T < T'` に対し、ある centered-Xi zero `z` が

```text
z ∉ Metric.ball 0 R
```

だが

```text
pascalCenteredToOrdinary z ∈
pascalSymmetricRectangleInterior σ T'
```

なら、`R, σ, T'` を用いた same-zero-set window は存在できない、という shape でよい。

目的は「零点が必ずその strip に存在する」と証明することではない。

目的は

> fixed `R` の same-zero-set contract と arbitrary `T → ∞` は自動両立しない

ことを型・theorem level に固定することである。

もし theorem 化が不自然なら、module docstring と result report の explicit obstruction でもよい。

---

# Gate I — Limit order ledger

XDP-006/007 と explicit-formula phase には複数の limit parameter がある。

```text
T       rectangle height
X       prime-power cutoff
τ       centered second-difference scale
ε       multiplicative approximate-identity width
```

現時点で Green なのは

```text
fixed ε > 0:
  τ → 0

then:
  ε → 0⁺
```

という XDP-006/007 の iterated limit だけである。

XDP-011 result report では、以下を明記すること。

```text
T → ∞ under fixed same-zero-set window: NOT LICENSED
X → ∞ under right-edge pointwise evaluation: GREEN pointwise only
X-limit ↔ interval integral exchange: OPEN
T-limit ↔ rectangle transport: OPEN / localization conflict
τ → 0 then ε → 0⁺: existing Green chain
```

joint limit や limit permutation を勝手に導入しない。

---

# 2. 推奨 module 構成

principal CFBRC module:

```text
DkMath/RH/CFBRC/PascalCenteredXiExplicitFormulaHorizontalPairing.lean
```

Gate E/F が generic に切れる場合のみ追加候補:

```text
DkMath/Analysis/MellinBoxSpectralSymmetry.lean
DkMath/Analysis/MellinBoxVerticalDecay.lean
```

ただし file proliferation を避け、既存

```text
MellinMultiplicativeApproxIdentity.lean
MellinCenteredDilation.lean
```

への自然な追加で済むなら既存 file を拡張してよい。

CFBRC theorem を `DkMath.Analysis` に逆 import してはならない。

public surface が有用なら

```text
DkMath/Analysis.lean
DkMath/RH.lean
```

へ import を追加する。

---

# 3. Principal acceptance set

最低 acceptance は次。

```text
A. top/bottom centered reflection geometry
B. even-weight horizontal integrand reflection
C. bottom = top and horizontal pair = 2 × top
D. full finite rectangle = 2 × right decomposed + 2 × top
E. XDP-006/007 principal Mellin second-difference box weight の evenness
H/I. fixed-window vs T∞ obstruction / limit-order audit を明記
```

Gate F は possible Green / Blocked のどちらでもよいが、実際の pinned API と証明可能範囲を result report に具体的に残す。

Gate G の full horizontal decay は XDP-011 の acceptance 条件ではない。

---

# 4. 禁止事項

次を行わないこと。

```text
- fixed same-zero-set window のまま T → ∞ を仮定
- weight decay だけから Xi-weighted horizontal integral decay を結論
- pointwise prime cutoff convergence と interval integral の極限交換
- z² weight に先に潰してから decay を主張
- rectangle deformation / residue provider の存在を sorry / axiom で埋める
- crossed local charge を未証明 residue sum と同一視
- RH / critical-line zero classification / defect vanishing を import または仮定
- Weil/Li positivity と同値な条件を independent provider と呼ぶ
```

新規 code に

```text
sorry
admit
axiom
native_decide
```

を追加しない。

---

# 5. Validation

最低限:

```text
lake env lean <new/changed module>
lake build DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaHorizontalPairing
./lb DkMath.RH
./lean-test.sh       # repository workflow に適合する場合
git diff --check
```

principal declarations は `#print axioms` を監査する。

既存 unrelated `sorry` warning と新規 warning を区別する。

---

# 6. Result report

作成:

```text
DkMath/RH/CFBRC/docs/wip/RH-CFBRC-explicit-formula-transport/
XDP-011-Finite-window-horizontal-pairing-and-Mellin-decay-compatibility-audit-result.md
```

必須記載:

1. 実際の declaration 名。
2. top/bottom orientation の exact sign。
3. full finite rectangle reduction の exact theorem。
4. Mellin second-difference box weight の evenness が Green か Blocked か。
5. weight-only imaginary decay が Green / conditional / Blocked のどれか。
6. full Xi-weighted horizontal decay を証明していない場合、その missing hypotheses。
7. fixed-window `T → ∞` がなぜ licensed でないか。
8. `T, X, τ, ε` の limit-order ledger。
9. no-circularity audit。
10. build/test/axiom audit。

---

# 7. XDP-011 終了後の判断

XDP-011 の principal endpoint が Green なら、fixed finite rectangle は

```text
2 × right-edge decomposed contribution
+ 2 × finite horizontal contribution
```

まで圧縮される。

そこから先は結果に応じて分岐する。

```text
Route H:
  suitable finite-height / height-sequence analytic provider を構成し
  horizontal contribution を制御する

Route R:
  actual rectangle deformation / residue provider を先に構成し
  fixed circle ↔ finite rectangle の charge を実現する

Route P:
  finite right-edge interval 上で prime cutoff convergence の
  uniform / dominated transport を構成する
```

XDP-012 は XDP-011 result を見て、最も load-bearing な未閉鎖 provider を選ぶ。

現時点では **`T → ∞` を自動的な次手として固定しない**。
