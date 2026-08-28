# XDP-003 — Mellin centered-mirror test adapter Codex 実装指示書

作成日: 2026-08-12

## 0. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-fixed-Xi-defect-provider-260812-v0
Lean: v4.32.2
mathlib: repository pinned revision
```

作業 directory:

```text
lean/dk_math
```

XDP-001 は finite centered-Xi mirror defect の構造同一性を Green 化した。
XDP-002 は classical Weil / Mathlib adapter audit を完了し、primary route を **Mellin-first** と確定した。

本指示書 XDP-003 の目的は、Guinand–Weil explicit formula や Li criterion をまだ実装せず、古典側で必要となる multiplicative reflection を Mathlib の Mellin transform convention 上で exact に形式化することである。

今回の主対象は一般 test function `h : ℝ → ℂ` であり、Xi、zeta zero、finite zero window、RH は主定理の仮定に入れない。

最終的に次の三層を Green にする。

```text
multiplicative mirror on h
        ↓
Mellin reflection identity
        ↓
critical-line centered reflection z ↦ -conj z
```

この bridge を XDP-004 の localized admissible test-family 構築の基礎とする。

---

# 1. 正本

最初に必ず次を読むこと。

```text
DkMath/RH/CFBRC/docs/wip/RH-CFBRC-fixed-Xi-defect-provider/
  XDP-002-Classical-Weil-Mathlib-adapter-audit-result.md

DkMath/RH/CFBRC/PascalCenteredXiWeilMirrorDefectBridge.lean
DkMath/RH/CFBRC/CriticalMirrorGeometry.lean
```

XDP-002 の compile probe 結果を正本とする。

特に pinned Mathlib で確認済みの次の API を再確認すること。

```lean
MellinConvergent
HasMellin
mellin
mellinInv
mellin_cpow_smul
mellin_comp_inv
mellin_eq_fourier
mellinInv_mellin_eq
```

ただし theorem の正確な implicit arguments、namespace、scalar action、hypotheses は、必ず pinned source と `#check` を優先すること。

XDP-002 report に記載された概念形をそのまま写経して elaboration を強制しない。

---

# 2. 数学的 Core

Mathlib convention では Mellin transform を概念的に

$$
\mathcal M h(s)
:=
\int_0^\infty x^{s-1} h(x)\,dx
$$

と読む。

今回 multiplicative critical mirror を次で定める。

$$
h^\vee(x)
:=
x^{-1}\,\overline{h(x^{-1})}.
$$

正の実変数上で変数変換 `x ↦ x⁻¹` を行うと、形式的には

$$
\mathcal M(h^\vee)(s)
=
\overline{\mathcal M h(1-\overline{s})}.
$$

これが XDP-003 の主 theorem である。

この identity は Riemann hypothesis、zeta functional equation、zero symmetry を使用しない。

## 2.1 centered form

critical-line centered coordinate を

$$
s=\frac12+z
$$

と置くと、

$$
1-\overline{s}
=\frac12-\overline{z}.
$$

したがって Mellin transform 側では centered coordinate に対して

$$
z\longmapsto-\overline z
$$

が現れる。

これは XDP-001 の

```lean
centeredComplex (criticalMirror s) = -(starRingEnd ℂ) (centeredComplex s)
```

と同じ centered reflection である。

XDP-003 ではこの一致を theorem として明示する。

---

# 3. 実装配置

一般 Mellin theorem は RH 専用にしない。

第一候補として generic Core を次に置く。

```text
DkMath/Analysis/MellinCriticalMirror.lean
```

namespace 第一候補:

```lean
namespace DkMath.Analysis
```

その上で CFBRC 固有の centered-coordinate bridge が必要なら薄い module を追加する。

```text
DkMath/RH/CFBRC/MellinCenteredMirrorAdapter.lean
```

namespace:

```lean
namespace DkMath.RH.CFBRCProjection
```

ただし repository の既存 `DkMath.Analysis` 配置規則を確認し、既存 Mellin subdirectory があるならその構造を優先する。

一般 theorem を `DkMath.RH.CFBRC` の中へ閉じ込めないこと。

---

# 4. Phase A — multiplicative mirror の定義

一般 test function `h : ℝ → ℂ` に対し、positive multiplicative variable を想定した mirror transform を定義する。

候補名:

```lean
noncomputable def mellinCriticalMirror (h : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (x : ℂ)⁻¹ * (starRingEnd ℂ) (h x⁻¹)
```

実際の型 coercion と `x⁻¹` の位置は pinned Mathlib の `mellin` integrand と proof ergonomics に合わせて調整してよい。

重要なのは正の `x` 上で数学的に

$$
h^\vee(x)=x^{-1}\overline{h(x^{-1})}
$$

となることである。

## 4.1 pointwise theorem

定義展開を安定させる theorem を一つ置く。

候補:

```lean
@[simp] theorem mellinCriticalMirror_apply
    (h : ℝ → ℂ) (x : ℝ) :
    mellinCriticalMirror h x =
      (x : ℂ)⁻¹ * (starRingEnd ℂ) (h x⁻¹) := by
  rfl
```

## 4.2 involution

正の実変数上では mirror は involution になる。

概念形:

$$
(h^\vee)^\vee(x)=h(x),\qquad x>0.
$$

候補 theorem:

```lean
theorem mellinCriticalMirror_involutive_of_pos
    (h : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    mellinCriticalMirror (mellinCriticalMirror h) x = h x := by
  ...
```

`x = 0` を無理に含めない。
Mellin integration domain は `Set.Ioi 0` なので、positive-domain theorem で十分である。

必要なら function equality は `Set.EqOn` on `Set.Ioi 0` で提供する。

```lean
mellinCriticalMirror_involutiveOn_Ioi
```

---

# 5. Phase B — Mellin reflection identity の hypothesis audit

主 theorem を書く前に、Mathlib の integrability theorem を確認する。

今回は「存在しない古典 theorem を仮定する」ことを禁止する。

次の二通りを比較し、より短く Green にできる方を採用する。

## Route B1 — 既存 Mellin lemmas の合成

優先候補。

既存の

```lean
mellin_comp_inv
mellin_cpow_smul
```

と conjugation / integral transport theorem を合成する。

目標は概念的に、

```text
h(x⁻¹)
  → mellin_comp_inv
  → s ↦ -s

x⁻¹ · (...) 
  → mellin_cpow_smul / exponent shift
  → -s ↦ 1-s

conj
  → integral/star compatibility
  → s ↦ conj s
```

を exact に追跡すること。

## Route B2 — set integral の inverse substitution を直接証明

B1 が Mathlib API の型不一致で複雑になる場合のみ採用する。

`Ioi 0` 上で `x ↦ x⁻¹` の substitution theorem を使い、Mellin integrand を直接変形する。

独自の measure-theory infrastructure を大規模に作らない。

必要な generic inverse-substitution theorem が Mathlib に存在するなら必ず再利用する。

## Gate B

どちらの route を選んだかを module docstring または XDP-003 result report に明記する。

---

# 6. Phase C — 主 Mellin mirror theorem

最重要 endpoint は次。

数学的 target:

$$
\mathcal M(h^\vee)(s)
=
\overline{\mathcal M h(1-\overline{s})}.
$$

Lean theorem の exact hypothesis は pinned Mathlib API に従う。

候補形:

```lean
theorem mellin_mellinCriticalMirror
    (h : ℝ → ℂ) (s : ℂ)
    (hconv₁ : MellinConvergent (mellinCriticalMirror h) s)
    (hconv₂ : MellinConvergent h (1 - (starRingEnd ℂ) s)) :
    mellin (mellinCriticalMirror h) s =
      (starRingEnd ℂ)
        (mellin h (1 - (starRingEnd ℂ) s)) := by
  ...
```

ただし、この hypothesis 形が過剰または不適切なら変更してよい。

重要なのは theorem statement が convergence を隠さないこと。

`MellinConvergent` が definitionally sufficientでない場合、必要な `IntegrableOn` 条件を明示する。

RH・Xi・zero 条件を一切入れない。

## 6.1 theorem naming boundary

この theorem を `WeilExplicitFormula`、`WeilCriterion`、`LiCriterion` などと呼ばない。

これは純粋な Mellin reflection identity である。

---

# 7. Phase D — centered spectral parameter adapter

一般 centered spectral parameter を

$$
s(z):=\frac12+z
$$

とする helper を必要最小限で置く。

新定義を増やさず `((1 : ℂ) / 2 + z)` のまま証明できるならそれを優先する。

まず algebraic identity を証明する。

候補:

```lean
theorem one_sub_conj_half_add
    (z : ℂ) :
    1 - (starRingEnd ℂ) ((1 : ℂ) / 2 + z) =
      (1 : ℂ) / 2 - (starRingEnd ℂ) z := by
  ...
```

その上で主 theorem の centered corollary を置く。

概念形:

$$
\mathcal M(h^\vee)\!\left(\frac12+z\right)
=
\overline{
  \mathcal M h\!\left(\frac12-\overline z\right)
}.
$$

候補 theorem:

```lean
theorem mellin_mellinCriticalMirror_half_add
    ... :
    mellin (mellinCriticalMirror h) ((1 : ℂ) / 2 + z) =
      (starRingEnd ℂ)
        (mellin h ((1 : ℂ) / 2 - (starRingEnd ℂ) z)) := by
  ...
```

主 theorem から `simpa` / `rw` で導出する。

---

# 8. Phase E — CFBRC criticalMirror との薄い bridge

ここからだけ `DkMath.RH.CFBRC` に入る。

既存 API:

```lean
criticalMirror
centeredComplex
centeredComplex_criticalMirror_eq_neg_conj
```

を再利用する。

critical mirror は complex plane 上で

$$
m(s)=1-\overline s
$$

と同じ点を表すことが既存 bridge から得られている。

XDP-003 では、Mellin reflection parameter と CFBRC critical mirror が exact に一致する theorem を一つ置く。

候補:

```lean
theorem one_sub_conj_eq_criticalMirror
    (s : ℂ) :
    1 - (starRingEnd ℂ) s = criticalMirror s := by
  ...
```

ただし同等 theorem が既存にある場合は新規定義・新規 theorem を増やさず再利用する。

既存 `criticalMirror_eq_star_one_sub` は

```lean
criticalMirror s = star (1 - s)
```

の形なので、必要なら pure complex algebra だけで desired orientation を導く。

さらに centered coordinate の一致を theorem として表す。

目標の意味は

```text
Mellin parameter reflection s ↦ 1 - conj s
                ↓ centered
z ↦ -conj z
                ↓
CFBRC centered critical mirror
```

である。

この Phase では zero predicate を使わない。

---

# 9. Optional Phase F — self-mirror test data

主 theorem が Green 後、proof が小さければ self-mirror predicate を定義してよい。

候補:

```lean
def IsMellinCriticalMirrorSelfDual (h : ℝ → ℂ) : Prop :=
  Set.EqOn (mellinCriticalMirror h) h (Set.Ioi 0)
```

その場合、self-dual `h` に対して

$$
\mathcal M h(s)
=
\overline{\mathcal M h(1-\overline s)}
$$

を corollary として置く。

centered line `s=1/2+it` では必要に応じて実値性 / conjugation symmetry の corollary を調べてよい。

ただしこの Optional Phase が convergence proof を大きく増やす場合は実装しない。

XDP-003 の必須 endpoint ではない。

---

# 10. H1 / H2 obstruction は今回解かない

XDP-002 で次を確定済み。

```text
H1: hard radial zero-window cutoff
H2: centered coordinate s - 1/2 is unbounded
```

XDP-003 ではこれらを解決しない。

特に以下を禁止する。

1. zero-window indicator を Mellin test function と同一視する
2. `s - 1/2` 単独を admissible Mellin test function と主張する
3. compact support / Schwartz / Mellin convergence を無証明で付与する
4. safe radius から smooth cutoff の存在を自動的に仮定する

これらは XDP-004 の局所化 test-family phase で扱う。

---

# 11. Classical boundary

XDP-003 が Green になっても、次は未証明のままである。

```text
Guinand–Weil explicit formula
classical Weil positivity criterion
Li criterion
zero-side global sum formula
prime-side explicit formula
fixed Xi defect vanishing
PascalCenteredXiFixedDefectVanishesOnSafeRadii
RiemannHypothesis
```

module docstring にこの境界を明記する。

`mellinCriticalMirror` は classical Weil test-function class そのものではない。

---

# 12. 実装上の注意

## 12.1 conjugation

project の標準に合わせて

```lean
starRingEnd ℂ
```

を優先する。

`Complex.conj` と混在させて simp normal form を不安定にしない。

## 12.2 scalar coercion

`x : ℝ` の inverse と `(x : ℂ)⁻¹` を混同しない。

positive-domain proof では

```lean
ne_of_gt hx
```

などで zero denominator を明示する。

## 12.3 cpow

Mellin kernel は complex `cpow` である。

実数冪 `Real.rpow` へ勝手に変換しない。

`x > 0` の仮定を利用して exponent algebra を行う。

## 12.4 integrals

conjugation と integral の交換に既存 continuous linear map theorem が使える場合はそれを優先する。

手動で real/imag parts に分解するのは最後の手段とする。

## 12.5 theorem statement

数学的 statement を proof convenience のために弱めない。

特に centered reflection の `1 - conj s` を `1 - s` へ落とさない。

---

# 13. Build Gate

最低限次を実行する。

```bash
cd lean/dk_math
lake env lean DkMath/Analysis/MellinCriticalMirror.lean
```

CFBRC adapter module を追加した場合:

```bash
lake env lean DkMath/RH/CFBRC/MellinCenteredMirrorAdapter.lean
lake build DkMath.RH
```

さらに repository standard gate を実行する。

```bash
./lean-build.sh
./lean-test.sh
git diff --check
```

新規 module について次を確認する。

```bash
rg -n '\bsorry\b|\badmit\b|\baxiom\b|native_decide' \
  DkMath/Analysis/MellinCriticalMirror.lean \
  DkMath/RH/CFBRC/MellinCenteredMirrorAdapter.lean
```

存在しない optional file は対象から外してよい。

既存別 module 由来の warning は今回追加したものと区別して報告する。

---

# 14. Completion Gate

XDP-003 完了条件は次の全て。

1. positive multiplicative variable 上の `mellinCriticalMirror` が定義されている
2. mirror involution が positive domain 上で Green
3. Mellin reflection identity

$$
\mathcal M(h^\vee)(s)
=
\overline{\mathcal M h(1-\overline s)}
$$

が適切な convergence hypotheses の下で Green
4. centered corollary

$$
\mathcal M(h^\vee)\!\left(\frac12+z\right)
=
\overline{\mathcal M h\!\left(\frac12-\overline z\right)}
$$

が Green
5. CFBRC `criticalMirror` / `centeredComplex` と同じ reflection であることが薄い bridge で Green
6. Xi / zero / RH を generic Core の仮定に入れていない
7. classical Weil criterion / explicit formula を実装済みと主張していない
8. build / test / diff-check が Green
9. 新規 code に `sorry` / `admit` / `axiom` / `native_decide` を追加していない

---

# 15. XDP-003 result report

完了時、同 directory に次を作成する。

```text
XDP-003-Mellin-centered-mirror-test-adapter-result.md
```

必ず記録する。

```text
1. 採用 module path
2. 採用した Mellin reflection proof route B1 / B2
3. exact theorem names and signatures
4. convergence / integrability hypotheses
5. reused Mathlib lemmas
6. centered CFBRC bridge
7. optional self-dual API の有無
8. build/test result
9. unresolved H1 / H2
10. XDP-004 への最小 handoff
```

---

# 16. XDP-004 への handoff criterion

XDP-003 が Green になった後にのみ XDP-004 へ進む。

XDP-004 の予定対象は **localized admissible Mellin test family** である。

概念候補:

$$
F_{R,\varepsilon}(s)
=
\left(s-\frac12\right)\Phi_{R,\varepsilon}(s).
$$

ただし XDP-003 では `Φ_{R,ε}` を定義しない。

次 phase では以下を比較する。

```text
A. compact-support multiplicative cutoff
B. log-coordinate Schwartz cutoff
C. safe-radius zero-free annulus を利用した finite-zero exact localization
```

XDP-003 は、その比較に必要な reflection law だけを確実に提供して終了する。

---

# 17. 禁止事項

今回、次は行わない。

1. `PascalCenteredXiFixedDefectVanishesOnSafeRadii` の証明
2. `RiemannHypothesis` の証明
3. defect upper bound `DΞ(R) ≤ 0` の主張
4. classical Weil positivity の再命名
5. Li coefficient の新規形式化
6. Guinand–Weil explicit formula の大規模実装
7. infinite zero sum の導入
8. hard zero-window cutoff の Mellin admissibility の無証明主張
9. XDP-001 Green theorem の再証明
10. Mathlib に存在しない theorem をあるものとして扱うこと

XDP-003 の仕事はただ一つである。

**multiplicative mirror と critical-line centered mirror が Mellin transform 上で同じ reflection law を持つことを Lean で exact に固定する。**
