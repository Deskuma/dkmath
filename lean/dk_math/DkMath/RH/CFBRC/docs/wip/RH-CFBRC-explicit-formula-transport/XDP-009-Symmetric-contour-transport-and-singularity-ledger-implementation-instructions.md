# XDP-009 — Symmetric contour transport / singularity-residue ledger 実装指示書

作成日: 2026-08-12

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-explicit-formula-transport-260812-v0
Lean: repository toolchain
mathlib: repository pinned revision
workdir: lean/dk_math
```

本 phase は XDP-008 の completed-zeta logarithmic-derivative decomposition を受け、fixed centered-Xi contour と既存 prime-side `-ζ'/ζ` endpoint の間に必要な **contour geometry / singularity bookkeeping** を形式化する。

XDP-008 で Green になった principal endpoint は次である。

```text
pascalCenteredXiNegLogDeriv
→ ordinary-zeta negative log derivative
 + archimedean Gammaℝ correction
 + elementary s(1-s) correction
```

centered coordinate は

```text
s = criticalLineCenter + z
```

である。

また、既存 prime-side hook

```lean
tendsto_pascalPrimePowerPHZFiniteUpTo_pascalXiOrdinaryZetaNegLogDeriv
```

により、`1 < s.re` では ordinary-zeta term は Pascal prime-power / von Mangoldt endpoint に既に接続されている。

XDP-009 の目的は、**closed contour 全体を右半平面へ押し込むことではない**。非自明零点を囲んだ closed contour を `1 < re` に完全移送することは、その零点を同時に囲み続ける geometry と両立しない。

したがって primary geometry は、critical line を中心とする **左右対称 rectangle / box contour** とする。

概念図:

```text
left edge               critical line               right edge
Re(s) = 1-σ                  1/2                    Re(s) = σ
   |                           |                          |
   |                           |                          |
   +---------------------------+--------------------------+
   |                                                      |
   |          zeros / singularity ledger                  |
   |                                                      |
   +---------------------------+--------------------------+

                                            σ > 1
```

右 edge を `1 < re` に置き、ordinary-zeta term を既存 prime-side endpoint に接続する。左 edge は将来の functional-equation reflection target とする。

**XDP-009 では full explicit formula、left-edge functional-equation cancellation、prime sum evaluation、defect sign、defect vanishing、RH を証明しない。**

---

## 1. XDP-008 正本 API

必ず以下を再利用すること。

```text
DkMath/RH/CFBRC/PascalCenteredXiCompletedZetaLogDerivBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiOuterContourResidueBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinWeightedOuterContourBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiMellinQuadraticRealizationBridge.lean
DkMath/RH/CFBRC/PascalVonMangoldtLSeriesBridge.lean
```

主要 declarations:

```lean
pascalXiOrdinaryZetaNegLogDeriv
pascalXiArchimedeanLogDeriv
pascalXiElementaryLogDerivCorrection

pascalCenteredXiNegLogDeriv_eq_zeta_add_archimedean_add_elementary

IsPascalCenteredXiLogDerivDecompositionSafeRadius

pascalCenteredXiWeightedNegLogDeriv_eq_decomposed_on_sphere

pascalCenteredXiWeightedOuterContourMass_eq_decomposed

tendsto_pascalPrimePowerPHZFiniteUpTo_pascalXiOrdinaryZetaNegLogDeriv
```

XDP-008 の Gate G は、Xi-safe だけから decomposition 後の三項それぞれの `CircleIntegrable` を無条件に供給できないため conditional のままである。

XDP-009 ではこの blocked 境界を隠さない。

---

## 2. 最初に行う pinned Mathlib contour API audit

コードを書く前に compile probe を行い、repository pinned Mathlib に存在する rectangle / path / contour deformation API を確認すること。

候補領域:

```text
Mathlib.Analysis.Complex.CauchyIntegral
Mathlib.Analysis.Complex.Residue
Mathlib.MeasureTheory.Integral.CircleIntegral
Mathlib.MeasureTheory.Integral.IntervalIntegral
Mathlib.Analysis.Complex.UpperHalfPlane.Basic
```

ただし import path / declaration 名は推測しない。`#check` / grep / compile probe で実在を確認する。

最低限、次を audit する。

1. rectangle boundary integral の既存 primitive があるか。
2. four-segment path を連結する API があるか。
3. holomorphic function に対する rectangle boundary integral zero theorem があるか。
4. finite isolated singularities を穴あき domain として除外する reusable theorem があるか。
5. residue theorem / argument principle 相当の API が pinned Mathlib にあるか。
6. contour homotopy / path integral congruence が実用可能か。
7. orientation reversal / translated segment / vertical line segment の integral API があるか。
8. existing DkMath `PascalCenteredXiOuterContourResidueBridge` の local-circle constructionを rectangle transport に再利用できるか。

### 重要

一般 residue theorem が無い場合、独自の巨大 residue framework を XDP-009 で新造しない。

優先順位は次とする。

```text
existing Mathlib theorem
→ existing DkMath local-circle/Cauchy machinery の再利用
→ 最小 rectangle boundary helper
→ named obstruction と conditional transport theorem
```

---

# Gate A — ordinary-coordinate contour geometry

## A1. centered circle の ordinary-coordinate image

centered circle

```text
|z| = R
```

は ordinary coordinate では

```text
|s - 1/2| = R
```

であることを theorem 化する。

既存 `criticalLineCenter` を使い、新しい `1/2` 定数を乱立させない。

候補 theorem shape:

```lean
theorem mem_centeredSphere_iff_mem_ordinaryCriticalCircle ...
```

名称は repository style に合わせて調整可。

## A2. symmetric rectangle parameters

少なくとも parameter として

```text
σ : ℝ
T : ℝ
```

を持ち、

```text
1 < σ
0 < T
```

を基本 contract とする。

左右 edge は

```text
Re(s) = σ
Re(s) = 1 - σ
```

とし、critical line `1/2` に関して対称であることを Green にする。

上下 edge は

```text
Im(s) = T
Im(s) = -T
```

とする。

rectangle 自体の membership predicate / boundary predicate は、既存 Mathlib rectangle type が十分ならそれを使う。無ければ DkMath 側で必要最小限だけ定義する。

### 禁止

単なる図示を theorem の代用にしない。

---

# Gate B — same-zero-set / transport contract

fixed centered circle と symmetric rectangle が自動的に同じ零点集合を囲むとは仮定しない。

rectangle を circle の外側に置けば追加零点を拾う可能性があり、内側に置けば零点を落とす可能性がある。

したがって次のどちらかを採用する。

## Route B1 — exact same-zero-set contract

有限 centered-Xi zero setについて、circle interior と rectangle interior の membership が一致することを明示する predicate / structure を定義する。

例:

```lean
structure PascalCenteredXiContourTransportWindow ... where
  ...
  zero_mem_iff : ∀ z ∈ pascalCenteredXiZeros,
    z ∈ circleInterior R ↔ centeredToOrdinary z ∈ rectangleInterior σ T
```

実際の名称・field は repository style に合わせる。

## Route B2 — difference ledger

同一集合を要求せず、rectangle と circle の差領域にある有限零点を ledger として明示する。

この場合、transport identity は

```text
rectangle contribution
circle contribution
additional enclosed zero contribution
removed zero contribution
```

を別項として保持する。

### 推奨

まず B1 の conditional contract を最小 Green API として作り、B2 は必要なら後段に回す。

### 絶対禁止

safe radius だけから arbitrary rectangle と zero-set equality を推論しない。

XDP-004 の safe-annulus theorem は radius の局所変化に対する安定性であり、circle と rectangle の global geometry equality ではない。

---

# Gate C — singularity ledger

XDP-008 で分解した三項ごとに singularity source を名前付きで記録する。

対象:

```text
ordinary zeta term:
  pascalXiOrdinaryZetaNegLogDeriv

archimedean term:
  pascalXiArchimedeanLogDeriv

elementary term:
  pascalXiElementaryLogDerivCorrection
```

最低限 ledger に含める location class:

```text
s = 1
s = 0
nontrivial zeta zeros
trivial zeta zeros / negative-even locations
Gammaℝ exceptional locations
```

## C1. classification only first

最初の Green endpoint は、各 point class がどの decomposed term の regularity hypothesis を壊し得るかを theorem / predicate で分類するところまででよい。

## C2. residue sign を記憶から hard-code しない

特に `Complex.Gammaℝ` は Mathlib の totalized meromorphic representationを使っており、exceptional point の point value を古典的 Laurent pole と同一視してはならない。

同様に `riemannZeta` の `s = 1` totalized behavior を classical pole residue の代用に使わない。

residue coefficient を実装するなら、以下のいずれかで Lean 上の局所 analytic / meromorphic theorem から導くこと。

```text
analyticOrder / meromorphic order
local factorization
existing residue theorem
punctured-neighborhood equality
```

証明できない residue coefficient は `Blocked` として ledger に残す。

---

# Gate D — rectangle boundary integrability / regularity contract

XDP-008 の `CircleIntegrable` contract に対応する rectangle/path 版を定義する。

理想的には、各 boundary component ごとに regularity を分離する。

```text
right edge
left edge
top edge
bottom edge
```

そして各 decomposed term ごとに、boundary 上 singularity が無いことと integrability を明示する。

一つの巨大 predicate に全部を埋め込んでもよいが、debug 可能性のため projection theorem を用意する。

候補概念:

```lean
IsPascalExplicitFormulaRectangleSafe σ T

PascalExplicitFormulaRectangleIntegrable h σ T
```

ただし実在 API に合わせて名称・型を調整する。

### 必須 theorem

`1 < σ` から right edge の全 point について

```text
1 < s.re
```

を導く lemma を Green にする。

これが既存 von Mangoldt endpoint への formal hook になる。

---

# Gate E — right-edge ordinary-zeta / prime hook

right edge parameterizationを `s(t)` としたとき、`1 < σ` から

```lean
tendsto_pascalPrimePowerPHZFiniteUpTo_pascalXiOrdinaryZetaNegLogDeriv
```

を各 boundary point に適用できることを adapter theorem として固定する。

XDP-009 では integral と limit の交換まで要求しない。

Green endpoint は例えば次で十分である。

```text
for every point s on right edge,
Pascal prime-power finite cutoff converges to
pascalXiOrdinaryZetaNegLogDeriv s
```

必要なら parameterized form を追加する。

### 禁止

pointwise `Tendsto` だけから contour integral limit を自動的に交換しない。

その交換には dominated convergence / uniform bound / finite interval integrability 等の別 theorem が必要であり、XDP-010 candidate として残す。

---

# Gate F — contour transport theorem

ここは pinned API に応じて三段階の acceptance を許す。

## F1 — preferred Green

既存 Mathlib / DkMath machinery で可能なら、holomorphic-away-from-finite-singularities な weighted decomposed observableについて、circle と symmetric rectangle の boundary integral differenceを finite local-circle / residue contribution として exact に表す。

概念形:

```text
rectangle boundary integral
-
circle integral

is finite sum of crossed local charges
```

式の符号・orientation は Lean の path orientation から導出する。

## F2 — conditional Green

一般 deformation theorem が pinned API に無い場合、transport provider を named hypothesis として切り、そこから XDP-008 decomposition / right-edge hookまでを exact に接続する theorem を作る。

ただし provider は曖昧な `assume explicit formula` ではなく、具体的な contour identity のみを field とする。

例:

```text
CircleToSymmetricRectangleTransport
```

のような structure/predicate を作り、

```text
same zero set
boundary regularity
orientation
integral identity
```

を明示する。

## F3 — audit-only Blocked

rectangle / residue API が不足し、F2 すら有益でない場合は、compile probe と exact missing declarations を result report に残す。

### 重要

F2/F3 でも Gate A–E が Green なら XDP-009 は有効な進展として扱う。

---

# Gate G — elementary / archimedean bookkeeping separation

transport 後も三項を早期に一つへ再結合しない。

```text
ordinary-zeta transport contribution
archimedean transport contribution
elementary transport contribution
crossed singularity/local-charge contribution
```

を named observable として保持する。

理由は、次 phase 以降で functional equation により left edge を right edgeへ反射するとき、Gamma / elementary correction が ordinary-zeta term と交換される可能性があるためである。

### 今回まだ証明しないもの

```text
left edge = reflected right edge + explicit correction
Gamma contribution closed form
elementary contribution closed form
trivial-zero cancellation closed form
```

これらは XDP-010 以降の candidate とする。

---

# Gate H — no-circularity / no-shortcut audit

XDP-009 の source / theorem / hypothesis に次を入れない。

```text
RiemannHypothesis
all nontrivial zeros have real part 1/2
PascalCenteredXiFixedDefectVanishesOnSafeRadii
defect = 0
horizontal energy = 0
Weil positivity
Li positivity
full Guinand-Weil explicit formula as an axiom
```

また、以下を禁止する。

```text
native_decide
axiom
admit
new sorry
```

既存 unrelated `sorry` warning は result report で区別する。

---

# 3. 推奨 module 構成

第一候補:

```text
DkMath/RH/CFBRC/PascalCenteredXiExplicitFormulaContourGeometry.lean
DkMath/RH/CFBRC/PascalCenteredXiExplicitFormulaSingularityLedger.lean
```

contour transport theorem まで Green にできる場合:

```text
DkMath/RH/CFBRC/PascalCenteredXiExplicitFormulaContourTransport.lean
```

もし rectangle/path geometry が RH 非依存の一般ライブラリとして十分きれいに切れる場合のみ、generic Core を

```text
DkMath/Analysis/Complex/...
```

へ置いてよい。

ただし無理に一般化しない。zeta/Gamma singularity ledger は `DkMath.RH.CFBRC` に置く。

公開 import は Green module のみ追加する。

---

# 4. Acceptance checklist

## Gate A — geometry

- [ ] centered circle ↔ ordinary critical-circle translation theorem
- [ ] symmetric rectangle parameter contract
- [ ] left/right edge symmetry about `1/2`
- [ ] top/bottom edge geometry

## Gate B — zero-set transport

- [ ] same-zero-set contract または difference ledger を明示
- [ ] safe-radius から勝手に rectangle equality を推論していない

## Gate C — singularity ledger

- [ ] `s = 0`
- [ ] `s = 1`
- [ ] nontrivial zeta zeros
- [ ] trivial-zero / negative-even locations
- [ ] Gammaℝ exceptional locations
- [ ] residue signを未証明のまま hard-codeしていない

## Gate D — boundary regularity

- [ ] rectangle/path integrability contract
- [ ] right edge `1 < re` theorem

## Gate E — prime hook

- [ ] right-edge pointwise von Mangoldt/Pascal endpoint adapter
- [ ] integral-limit exchangeを未証明で主張していない

## Gate F — transport

以下のいずれか:

- [ ] exact contour transport Green
- [ ] named conditional transport provider Green
- [ ] exact missing API を audit report に記録して Blocked

## Gate G — bookkeeping

- [ ] zeta / Gamma / elementary / crossed-local-charge を分離保持

## Gate H — safety

- [ ] RH を使用しない
- [ ] defect vanishing を使用しない
- [ ] full explicit formula を仮定しない
- [ ] new `sorry/admit/axiom/native_decide` なし

---

# 5. Validation

最低限:

```text
lake env lean <new modules>
lake build <new public modules>
./lean-build.sh
./lean-test.sh
git diff --check
```

principal declarations について `#print axioms` を実行する。

新規 source について文字列監査:

```text
sorry
admit
axiom
native_decide
```

---

# 6. Result report

作成:

```text
DkMath/RH/CFBRC/docs/wip/RH-CFBRC-explicit-formula-transport/
XDP-009-Symmetric-contour-transport-and-singularity-ledger-result.md
```

必須記載事項:

1. pinned Mathlib contour/path/residue API audit 結果。
2. 実際に採用した rectangle/path representation。
3. actual declaration 一覧。
4. same-zero-set contract または difference ledger の意味。
5. singularity class の分類。
6. Green にできた residue/local-charge coefficient と、未証明のものを分離。
7. right-edge `1 < re` と既存 prime hook の接続状況。
8. contour transport が F1/F2/F3 のどれになったか。
9. Gate G の各 contribution がどの形で残ったか。
10. XDP-010 に渡す exact missing theorem / hypothesis。
11. no-circularity audit。
12. validation 結果。

---

# 7. XDP-010 handoff candidate

XDP-009 が F1 または十分強い F2 まで到達した場合、次 phase の第一候補は

```text
XDP-010 — Functional-equation left-edge reflection and right-edge prime transport
```

とする。

狙い:

```text
symmetric rectangle
→ left edge functional-equation reflection
→ right edge ordinary-zeta contribution
 + explicit Gamma / elementary correction
→ right-edge prime-power approximants
→ weighted arithmetic observable
```

ただし integral-limit exchange が未解決なら、XDP-010 の前半を

```text
right-edge dominated/uniform convergence provider
```

に切り出してもよい。

---

## 最終注意

XDP-009 の価値は「explicit formula を一気に完成させること」ではない。

この phase で固定すべきなのは、

```text
どの contour geometry を使うか
どの singularity を横切るか
どの contribution に residue/local charge を帰属させるか
どこから `1 < re` の prime endpoint を読めるか
どの theorem が pinned Mathlib に不足しているか
```

である。

特に、closed contour を丸ごと `Re(s) > 1` に押し込む shortcut は採用しない。nontrivial zero information を保持したまま prime side を読むため、critical line 対称 rectangle と left/right edge decomposition を正本 geometry とする。
