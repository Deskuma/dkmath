# XDP-002 — Classical Weil / Mathlib adapter audit Codex 実装指示書

作成日: 2026-08-12

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-fixed-Xi-defect-provider-260812-v0
Lean: v4.32.2
mathlib: pinned project revision
```

作業 directory:

```text
lean/dk_math
```

XDP-001 は Green 完了済みである。

本 checkpoint の目的は、新しい RH 同値条件を作ることでも、Guinand–Weil explicit formula を一気に形式化することでもない。

**XDP-001 で得た finite centered-Xi mirror defect を、古典 Weil / explicit-formula machinery へ安全に接続するための adapter surface を監査し、Mathlib の既存部品・不足部品・論理的 obstruction を exact に確定すること**を目的とする。

XDP-002 は「先人の理論をどこまでそのまま継承できるか」を判定する phase である。

最終成果は、XDP-003 で実装すべき最小 test-function adapter の仕様が一意に近い形まで絞られていること。

---

# 1. 正本 — XDP-001 Green API

最初に必ず次を読むこと。

```text
DkMath/RH/CFBRC/PascalCenteredXiWeilMirrorDefectBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiFixedSecondMomentDefectBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiOuterContourResidueBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiRadialLayerCakeOuterCountBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiGlobalZeroDiskBridge.lean
DkMath/RH/CFBRC/CriticalMirrorGeometry.lean
DkMath/RH/CFBRC/CriticalMirrorZeroBridge.lean
```

XDP-001 の実 repository head を正本とする。

最低限、次の API を確認すること。

```lean
centeredMirrorPairTerm_eq_neg_sq
centeredComplex_sub_criticalMirror_eq_two_horizontal
half_normSq_centeredComplex_sub_criticalMirror_eq

pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair
pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair_eq_neg_centeredSecondMoment
pascalCenteredXiFixedHolomorphicSecondContourFunctional_eq_finiteWeilMirrorPair
pascalCenteredXiFixedSecondMomentDefectFunctional_eq_radial_sub_finiteWeilMirrorPair_re

pascalCriticalMirrorZeroWindowAntiMirrorEnergy
pascalCriticalMirrorZeroWindowAntiMirrorEnergy_eq_two_mul_horizontalEnergy
pascalCenteredXiFixedSecondMomentDefectFunctional_eq_antiMirrorEnergy
```

XDP-002 ではこれらを再証明しない。

既存 Green equality chain は次の有限構造を固定している。

$$
W_R
:=
\sum_{\rho\in W_R}
 m_\rho\,
 c(\rho)\,
 \overline{c(m(\rho))}
$$

$$
W_R=-M_{2,R}
$$

safe radius 上で

$$
D_\Xi(R)
=
Q_R-\operatorname{Re}W_R
$$

かつ

$$
D_\Xi(R)
=
\frac12
\sum_{\rho\in W_R}
 m_\rho
 \left|c(\rho)-c(m(\rho))\right|^2
$$

である。

ここで

```text
c(ρ) = centeredComplex ρ
m(ρ) = criticalMirror ρ
```

と読む。

この finite identity は RH を仮定しない。

---

# 2. XDP-002 の基本原則

## 2.1 classical Weil criterion を実装済みと主張しない

XDP-001 の `FiniteWeilMirrorPair` は deliberately `Weil-style` である。

XDP-002 でも次を区別する。

```text
A. DkMath finite zero-window mirror pairing
B. classical Weil quadratic functional
C. Guinand–Weil explicit formula
D. Li coefficients / Li criterion
```

A と B に構造類似性があっても、B の admissible test-function class、無限 zero sum、explicit formula、収束条件まで形式化されていない限り、Lean theorem として同一視しない。

## 2.2 RH-equivalent condition を provider と呼ばない

次の形を発見しても XDP provider の完成ではない。

```text
newCondition ↔ RiemannHypothesis
```

または

```text
newCondition ↔ PascalCenteredXiFixedDefectVanishesOnSafeRadii
```

XDP の最終目的は独立 provider である。

XDP-002 はその前段の adapter audit であり、RH を証明しない。

## 2.3 local pinned Mathlib を正本にする

Web documentation の API 名は探索の seed としてのみ使う。

最終判定は必ず現在 checkout の pinned Mathlib に対して行う。

```bash
rg -n "MellinConvergent|HasMellin|mellin_inversion|mellin_eq_fourier" .lake/packages/mathlib/Mathlib
rg -n "fourierTransformCLM|fourierTransformCLE|integral_inner_fourier_fourier" .lake/packages/mathlib/Mathlib
rg -n "LSeries_vonMangoldt_eq_deriv_riemannZeta_div" .lake/packages/mathlib/Mathlib
rg -n "Weil|Guinand|Li coefficient|LiCoefficient|explicit formula" .lake/packages/mathlib/Mathlib
```

path が project layout と異なる場合は実 checkout に合わせる。

`#check` 用 scratch file を作って compile で確認してよいが、単なる API probe file は commit しない。

---

# 3. Audit A — classical mathematical dictionary

XDP-001 と古典 Weil structure の対応関係を文書上で exact に整理する。

critical mirror は

$$
m(s)=1-\overline{s}
$$

であり、centered coordinate は

$$
c(s)=s-\frac12
$$

なので

$$
c(m(s))=-\overline{c(s)}
$$

となる。

XDP-001 の finite pairing は

$$
W_R(c,c)
=
\sum_{\rho\in W_R}
 m_\rho c(\rho)\overline{c(m(\rho))}
$$

である。

古典 Weil 側では、test function の Mellin/Fourier transform を零点で評価し、functional-equation reflection を含む quadratic functional が現れる。

XDP-002 では次を調べる。

1. 古典 Weil quadratic functional の test-function domain
2. zero-side expression の reflection/conjugation convention
3. multiplicative variable `x > 0` 側の involution convention
4. Mellin transform convention
5. Fourier transform の `2π` normalization
6. zeta pole / gamma / archimedean contribution の normalization
7. prime / prime-power contribution の von Mangoldt normalization

**符号・conjugation・`2π`・Mellin exponent の convention を曖昧にしたまま bridge theorem を設計しないこと。**

Audit result では、各 convention を DkMath / Mathlib / classical source の三列で比較する。

---

# 4. Audit B — Mathlib Mellin surface

現在の Mathlib には候補として次の API が存在する可能性が高い。

```lean
MellinConvergent
mellin
mellinInv
HasMellin
mellin_cpow_smul
mellin_comp_inv
mellin_differentiableAt_of_isBigO_rpow
mellin_eq_fourier
mellin_inversion
```

すべて local pinned tree で `#check` すること。

確認項目:

```text
- domain は ℝ → E か
- 積分 domain は Ioi 0 か
- kernel は t^(s-1) か
- complex power の convention
- inversion theorem の仮定
- holomorphicity / differentiability theorem の仮定
- x ↦ x⁻¹ 変換で s ↦ -s が得られる exact theorem
- critical line 1/2 + it に合わせる際に追加 shift が必要か
```

XDP で欲しい multiplicative involution は classical literature の convention により

$$
\widetilde h(x)
=
x^{-1}\overline{h(x^{-1})}
$$

または近い形を取る可能性がある。

これを Mathlib `mellin_comp_inv` などだけで組めるか、追加 lemma が必要かを記録する。

この段階では definitive definition を commit しなくてよい。

---

# 5. Audit C — Mathlib Fourier / Schwartz surface

次を local pinned Mathlib で監査する。

```lean
SchwartzMap
SchwartzMap.fourierTransformCLM
SchwartzMap.fourierTransformCLE
FourierTransform.fourier
SchwartzMap.integral_bilin_fourier_eq
SchwartzMap.integral_inner_fourier_fourier
```

確認項目:

```text
- SchwartzMap ℝ ℂ をそのまま test class に利用できるか
- Fourier transform normalization
- inversion
- Plancherel
- conjugation / reflection の API
- translation / scaling の API
- compact support bump との接続
```

注意:

classical Weil explicit formula の標準 test class が Mathlib `SchwartzMap` と定義上同じとは限らない。

「Schwartz だから classical Weil admissible」と自動で結論しない。

必要なら

```text
Classical required condition
Mathlib available structure
Missing bridge
```

の三段表にする。

---

# 6. Audit D — arithmetic / zeta surface

Prime side へ進むため、次を exact に確認する。

第一候補:

```lean
ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
```

期待する数学形は `re s > 1` で

$$
\sum_{n\ge1}\frac{\Lambda(n)}{n^s}
=
-\frac{\zeta'(s)}{\zeta(s)}.
$$

local theorem の exact statement を記録する。

さらに次を検索する。

```text
riemannZeta differentiable / analytic API
completedRiemannZeta functional equation API
logarithmic derivative API
Dirichlet/LSeries summability API
vonMangoldt support / prime-power API
contour-shift / residue API
```

DkMath 側で既に PPW により持っている bridge と重複する theorem は再実装しない。

特に prime-power / von Mangoldt / zeta log-derivative への bridge が既存 DkMath module にある場合は、それを XDP-003 以降の入口として記録する。

---

# 7. Audit E — classical explicit-formula availability

Mathlib 内を広く検索し、次のどれに該当するか明示する。

```text
A. Guinand–Weil explicit formula が既に theorem として存在
B. 一般 L-function explicit formula があり zeta に specialize 可能
C. 必要な Mellin/Fourier/LSeries 部品はあるが explicit formula theorem 自体はない
D. さらに下位部品から不足している
```

検索語は少なくとも次。

```text
Weil
Guinand
explicit formula
prime explicit
zero sum
Li coefficient
RiemannHypothesis
```

見つからなかったものを「Mathlib に存在しない」と断言する前に、synonym / namespace を変えて二度以上検索する。

Audit report には検索コマンドと結果概要を残す。

---

# 8. Hard-cutoff obstruction を named result として固定する

XDP-001 の finite defect は hard zero window を使う。

概念的には

$$
D_\Xi(R)
=
\frac12
\sum_\rho
m_\rho
\mathbf 1_{|\rho-1/2|\le R}
\left|c(\rho)-c(m(\rho))\right|^2.
$$

一方、classical explicit formula は通常、零点側へ admissible transform weight を与える。

したがって現在の hard cutoff は、そのままでは classical test-function transform の像である保証がない。

さらに centered coordinate

$$
c(s)=s-\frac12
$$

は無限遠で減衰しない。

XDP-002 ではこの二点を区別して obstruction とする。

```text
Obstruction H1: hard radial zero-window localization
Obstruction H2: unbounded centered coordinate
```

ここで重要なのは、これらは RH の obstruction ではなく、**classical explicit-formula test class へ入れるための adapter obstruction** であること。

この段階で H1/H2 が不可能性定理であるとは主張しない。

---

# 9. XDP-003 用 test-function adapter の最小仕様

XDP-002 の最終仕事は、具体関数を無理に決めることではなく、XDP-003 で構成する family が満たすべき条件を exact に決めることである。

候補 family を概念的に

$$
F_{R,\varepsilon}(s)
=
c(s)\,\Phi_{R,\varepsilon}(s)
$$

と書く。

ただしこの形を先に固定しない。

Audit の結果、multiplicative-side test function `h` を先に定義し、その Mellin transform `H` を `F` とする方が classical machinery に自然なら、そちらを優先する。

必要条件候補:

```text
T1. classical explicit formula の admissible class に入る
T2. critical-mirror / conjugation convention と整合する
T3. zero-side で centered coordinate を読む
T4. radial window を smooth に局所化できる
T5. ε → 0 で hard-window quantity へ近づける可能性がある
T6. boundary-safe radius 仮定を極限で利用できる
T7. prime side が von Mangoldt weighted sum へ exact に落ちる
T8. archimedean / pole contribution を明示的に分離できる
```

特に T5 は XDP-002 で証明しなくてよい。

しかし、どの topology / convergence notion を使えば T5 を将来 formalize できるか候補を示す。

例:

```text
pointwise + dominated convergence
L1 / L2 convergence
Schwartz topology
Mellin-side local uniform convergence
finite-zero-window eventual equality / boundary-safe stabilization
```

既存 XDP defect は safe radius で boundary zero が無いため、smooth cutoff の support transition を boundary annulus に閉じ込めれば finite zero set 上で eventual stabilization を使える可能性がある。

この route が利用可能か、既存 finite-zero APIs を確認する。

---

# 10. Boundary-safe radius を adapter に活かせるか監査する

既存定義:

```lean
IsPascalCenteredXiBoundarySafeRadius R
```

は「centered Xi zero が sphere `|z| = R` 上に存在しない」ことを意味する。

XDP-002 では次を調べる。

safe radius と finite zero discreteness から、ある `δ > 0` が存在して

```text
R - δ < |centered zero| < R + δ
```

という annulus に zero が無いことを既存 theorem だけで出せるか。

これが Green に近いなら、smooth radial cutoff `Φ_{R,ε}` が sufficiently small `ε` で zero values 上 hard cutoff と exact に一致する route が得られる。

これは dominated convergence より Lean で軽い可能性がある。

ただし theorem が無い場合、XDP-002 で無理に実装しない。

`XDP-003 candidate lemma` として記録する。

---

# 11. Generic finite Weil pairing abstraction の要否を監査する

XDP-001 は centered coordinate 専用の

```lean
pascalCriticalMirrorZeroWindowFiniteWeilMirrorPair R
```

を持つ。

XDP-003 以降では test function `F` を変えるため、generic finite pairing

```lean
finiteWeilMirrorPair R F G
```

のような abstraction が必要になる可能性がある。

XDP-002 で判断する。

導入する価値がある条件:

```text
- XDP-001 pairing が specialization で短く表せる
- XDP-003 test family にそのまま使える
- mirror reindexing を不要に保てる
- API が classical infinite Weil functional と誤認されない naming になる
```

導入する場合でも名称には `Finite` / `ZeroWindow` / `WeilStyle` のいずれかを残す。

例:

```lean
pascalCriticalMirrorZeroWindowFiniteWeilStylePair
```

XDP-002 自体で generic abstraction を commit するのは、それが XDP-003 の重複を確実に減らす場合だけとする。

単なる将来予測なら audit report に留める。

---

# 12. 実装物

XDP-002 の必須成果物は audit report である。

新規 file:

```text
DkMath/RH/CFBRC/docs/wip/RH-CFBRC-fixed-Xi-defect-provider/
  XDP-002-Classical-Weil-Mathlib-adapter-audit-result.md
```

report には最低限次を含める。

```text
1. XDP-001 Green API summary
2. classical Weil / DkMath convention dictionary
3. Mathlib Mellin API inventory
4. Mathlib Fourier / Schwartz API inventory
5. Mathlib zeta / von Mangoldt API inventory
6. explicit-formula theorem availability判定
7. hard-cutoff obstruction H1
8. centered-growth obstruction H2
9. safe-radius annulus stabilization route の可否
10. generic finite pairing abstraction の要否
11. XDP-003 の exact implementation target
12. Blocker / Risk / Non-goal
```

必要なら reusable Lean theorem を追加してよい。

ただし audit のためだけの `#check` module は commit しない。

新規 public module を追加した場合だけ `DkMath/RH.lean` root import を検討する。

report だけなら root import を変更しない。

---

# 13. Classical source の扱い

数式 normalization の正本候補として、一次資料を優先する。

最低限、次を確認する。

```text
Jeffrey C. Lagarias,
"Li Coefficients for Automorphic L-Functions",
Annales de l'Institut Fourier 57 (2007), 1689–1740.
DOI: 10.5802/aif.2311
arXiv: math/0404394
```

必要に応じて Bombieri–Lagarias の Li criterion / explicit formula 関連論文も確認する。

外部 source から theorem を Lean fact として輸入しない。

外部 source は数式 convention と target specification の確定に使う。

Lean で利用可能な theorem は local Mathlib / DkMath で別途確認する。

---

# 14. Mathlib seed API

2026-08-12 時点の公開 Mathlib documentation では、探索 seed として次が確認できる。

```text
Mathlib.Analysis.MellinTransform
Mathlib.Analysis.MellinInversion
Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
Mathlib.NumberTheory.LSeries.Dirichlet
Mathlib.NumberTheory.LSeries.RiemannZeta
```

特に seed theorem:

```lean
ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
```

公開 docs 上では `re s > 1` において von Mangoldt L-series と `-ζ'/ζ` を結ぶ。

ただし繰り返すが、XDP-002 の正本は local pinned Mathlib である。

---

# 15. 禁止事項

XDP-002 では次を行わない。

```text
- RH を仮定して adapter を閉じる
- PascalCenteredXiFixedDefectVanishesOnSafeRadii を仮定する
- DΞ(R) = 0 を仮定する
- horizontal energy = 0 を仮定する
- classical Weil criterion を実装済みと記述する
- finite pairing を classical infinite Weil functional と definitionally 同一視する
- convergence proof を `sorry` で先送りする
- hard cutoff を admissible test function と無根拠に宣言する
- Mathlib に無い theorem を存在するものとして instruction に固定する
- external source の theorem を axiom 化する
```

既存 module の `sorry` warning は今回 scope 外。

新規 committed Lean code には

```text
sorry
admit
axiom
native_decide
```

を追加しない。

---

# 16. Validation

Lean code を追加・変更した場合:

```bash
lake env lean DkMath/RH/CFBRC/<new-module>.lean
lake build DkMath.RH
./lean-build.sh
./lean-test.sh
git diff --check
```

report only の場合でも最低限:

```bash
git diff --check
```

を実行する。

Mathlib API audit では scratch file を使って `#check` が実際に通ることを確認する。

「検索で文字列を見つけた」だけで API 利用可能と判定しない。

---

# 17. Completion criteria

XDP-002 完了条件は次。

```text
Gate A: XDP-001 finite defect の classical dictionary が明文化された
Gate B: Mellin API の present / missing が compile 確認された
Gate C: Fourier/Schwartz API の present / missing が compile 確認された
Gate D: von Mangoldt / ζ'/ζ bridge が compile 確認された
Gate E: Guinand–Weil explicit formula の Mathlib availability が判定された
Gate F: hard-cutoff obstruction H1 が明文化された
Gate G: centered-growth obstruction H2 が明文化された
Gate H: safe-radius stabilization route が viable / blocked / unknown のいずれかに分類された
Gate I: generic finite Weil-style pairing abstraction の要否が決定された
Gate J: XDP-003 の最小 implementation target が一つに絞られた
```

XDP-002 は provider theorem を閉じなくてよい。

むしろ、ここで route を一つに絞り、不要な解析を捨てることが成功条件である。

---

# 18. Expected handoff to XDP-003

理想的な handoff は次のいずれかになる。

## Route M — Mellin-first

```text
multiplicative test function h
  → Mellin transform H(s)
  → critical-mirror compatible quadratic zero weight
  → smooth centered localization
  → finite fixed-Xi defect approximation
```

## Route S — Schwartz/Fourier-first

```text
Schwartz test function φ(t)
  → Fourier transform
  → Mellin coordinate via log x
  → explicit-formula admissible transform
  → centered zero weight
```

## Route P — existing PPW prime/zeta bridge first

```text
existing von Mangoldt / ζ'/ζ DkMath bridge
  → weighted contour identity
  → choose analytic kernel
  → zero-side smoothed defect
```

XDP-002 report で、一番 Lean の既存 Green Coreを再利用でき、かつ古典 theorem の仮定を正確に満たせる route を一つ primary として選ぶ。

他 route は fallback とする。

その primary route の最初の reusable definition / lemma 群を XDP-003 の実装対象として具体名まで提案すること。

---

# 19. Research frontier

XDP-002 終了時点でも、次は未証明である。

```lean
PascalCenteredXiFixedDefectVanishesOnSafeRadii
```

既知なのは safe radius 上の representation と nonnegativity である。

本 phase の役割は、先人の explicit-formula machinery へ入るための道具と convention を確定し、最終的に同じ scalar

```text
pascalCenteredXiFixedSecondMomentDefectFunctional R
```

へ独立に制約を与えられる route だけを残すことである。

Representation phase と provider phase を混同しないこと。
