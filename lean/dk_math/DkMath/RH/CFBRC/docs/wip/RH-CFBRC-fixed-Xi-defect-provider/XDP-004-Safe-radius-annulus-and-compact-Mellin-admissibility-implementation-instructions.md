# XDP-004 — Safe-radius annulus and compact Mellin admissibility Codex 実装指示書

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

XDP-001 は finite centered-Xi defect を finite Weil-style mirror pairing / anti-mirror energy と exact に同一視した。

XDP-002 は classical Weil / Mathlib surface を監査し、primary route を Mellin-first とした。

XDP-003 は generic Mellin reflection

$$
\mathcal M(h^\vee)(s)
=
\overline{\mathcal M h(1-\bar s)}
$$

と、CFBRC の `criticalMirror` / centered reflection を Green 化した。

XDP-004 の目的は、XDP-003 で明示的に残した二つの obstruction

```text
H1: hard radial zero-window cutoff
H2: centered coordinate / spectral parameter の非有界性
```

を **同じ theorem で無理に解かず、二つの独立した reusable Core に分解すること**である。

本 phase の endpoint は次の二本である。

```text
A. safe radius の近傍では finite zero window が局所的に不変
B. positive multiplicative variable 上で 0 と ∞ から離れた compact support を持つ test function は Mellin admissibility を得る
```

重要: XDP-004 は Guinand–Weil explicit formula、classical Weil criterion、Li criterion、RH、fixed-Xi defect vanishing を証明しない。

さらに、spectral plane 上の hard radial cutoff が Mellin transform と exact に一致するとは主張しない。

---

# 1. 正本 — 必ず先に読む module / report

```text
DkMath/Analysis/MellinCriticalMirror.lean
DkMath/RH/CFBRC/MellinCenteredMirrorAdapter.lean
DkMath/RH/CFBRC/PascalCenteredXiGlobalZeroDiskBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiFixedSecondMomentDefectBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiWeilMirrorDefectBridge.lean

DkMath/RH/CFBRC/docs/wip/RH-CFBRC-fixed-Xi-defect-provider/
  XDP-002-Classical-Weil-Mathlib-adapter-audit-result.md
  XDP-003-Mellin-centered-mirror-test-adapter-result.md
```

XDP-003 から最低限次を継承する。

```lean
DkMath.Analysis.mellinCriticalMirror
DkMath.Analysis.mellinCriticalMirror_involutive_on_pos
DkMath.Analysis.mellin_mellinCriticalMirror
DkMath.Analysis.mellin_mellinCriticalMirror_centered

DkMath.RH.CFBRCProjection.one_sub_conj_eq_criticalMirror
DkMath.RH.CFBRCProjection.mellinCenteredReflectionParameter_eq_criticalMirror
```

safe-radius 側では repository head の正確な theorem 名を検索し、最低限次の定義を正本とする。

```lean
IsPascalCenteredXiBoundarySafeRadius
pascalCenteredRiemannXiKernel
pascalCriticalMirrorZeroWindow
pascalCriticalMirrorZeroWindowFinset
```

既存 theorem 名・引数はこの文書より repository head を優先する。

---

# 2. 数学的分解

## 2.1 H1 は「cutoff function」ではなく「zero-window local constancy」に落とす

safe radius `R` の定義は概念的に

```lean
0 < R ∧
∀ z ∈ Metric.sphere (0 : ℂ) R,
  pascalCenteredRiemannXiKernel z ≠ 0
```

である。

欲しいのは、まず smooth cutoff ではない。

最初に次を示す。

$$
\exists \varepsilon>0,\quad
|r-R|<\varepsilon
\Longrightarrow
W_r=W_R.
$$

ここで `W_r` は既存の centered finite zero window。

つまり boundary-safe radius の近傍では、境界を少し動かしても zero が出入りしない。

これを **safe-radius annulus / window stability theorem** として Green 化する。

この theorem により hard cutoff の不連続性を、zero set 上では局所的に無害化できる。

ただしこれは spectral test function が smooth/holomorphic になったことを意味しない。

## 2.2 H2 は x-space compact support で処理する

Mellin transform は

$$
\mathcal M h(s)
=
\int_0^\infty x^{s-1}h(x)\,dx.
$$

`h` が

$$
0<a\le x\le b<\infty
$$

の compact interval に support を持つなら、`x=0` と `x=∞` の singular/growth 問題を避けられる。

XDP-004 では、十分な regularity / measurability / integrability 仮定のもとで

$$
\forall s\in\mathbb C,\quad \operatorname{MellinConvergent}(h,s)
$$

を与える generic theorem を構成する。

さらに mirror

$$
h^\vee(x)=x^{-1}\overline{h(x^{-1})}
$$

の support は概念的に

$$
[1/b,1/a]
$$

へ移るため、mirror side の Mellin convergence も同様に得られる。

これにより XDP-003 の

```lean
mellin_mellinCriticalMirror
```

へ必要だった二つの `MellinConvergent` hypothesis を、compact-support data から供給できるようにする。

---

# 3. 重要な解析境界 — spectral hard cutoff を Mellin transform と同一視しない

XDP-004 では次を禁止する。

```text
Mellin transform H(s) = hard radial indicator of {|s - 1/2| ≤ R}
```

または

```text
H(s) = (s - 1/2) * radial compact-support bump in the complex s-plane
```

を、x-space compactly supported test function の Mellin transformとして無検証に宣言してはならない。

理由は、Mellin transform 側には holomorphic / analytic structure があり、spectral plane 上の任意の radial smooth cutoff や hard cutoff は自動的にその像には入らないからである。

XDP-004 の役割は次だけである。

```text
zero side: safe radius → window locally constant
Mellin side: compact positive support → convergence / reflection admissible
```

この二本の間の **spectral interpolation / explicit-formula test realization** は XDP-005 以降の別問題として残す。

必要ならこの境界を module docstring と result report に明記する。

---

# 4. 実装 Phase A — safe-radius API audit

最初に repository / pinned Mathlib を検索し、次を compile probe する。

```text
Metric.sphere / closedBall / ball
IsCompact sphere
Continuous / IsClosed preimage zero
Finite / Finset zero sets in compact sets
norm / dist continuity
finite set minimum distance API
```

既存 DkMath の zero finiteness theorem を優先する。

候補として過去 PPW layer にある compact zero finiteness theorem / zero-window finiteness theorem を検索すること。

新しい analytic zero-discreteness theorem を再実装しない。

## Gate A0

結果 report に次を記録する。

```text
1. safe radius の exact definition
2. zero window の exact membership condition
3. compact zero finiteness API の exact theorem name
4. 採用する annulus proof route
```

---

# 5. 実装 Phase B — safe-radius annulus theorem

第一候補 route は **finite radial gap route** とする。

### Route B1 — finite radial gap (preferred)

`R` が safe なら、例えば `R + 1` までの compact zero set を既存 finiteness theorem で Finset 化する。

その有限集合中の各 zero `ρ` について

$$
\left|\|c(\rho)\|-R\right|>0
$$

である。

有限集合なので boundary までの正の最小 radial gap を取れる。

`ε` はその gap と `1`、必要なら `R/2` の最小値から選ぶ。

これにより

$$
0<\varepsilon
$$

かつ

$$
|r-R|<\varepsilon
$$

なら `R` と `r` の間に zero radius がなく、window membership は一致する。

### Route B2 — compactness + continuity (fallback)

B1 が既存 Finset API の都合で過剰に重い場合のみ、sphere compactness と Xi continuity/nonvanishing から zero-free neighborhood を作る。

ただし新しい複素解析の大 theorem を導入するより、既存 finite-zero infrastructure を使う B1 を優先する。

## theorem target

exact type は既存 window definition に合わせるが、最低限次のいずれかを Green にする。

```lean
theorem exists_pascalCenteredXi_safeRadius_window_stability
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ r : ℝ, |r - R| < ε →
        pascalCriticalMirrorZeroWindow r =
          pascalCriticalMirrorZeroWindow R
```

Set equality が扱いやすければこれを第一 target にする。

Finset equality が既存 canonical Finset を通じて容易なら追加する。

```lean
theorem exists_pascalCenteredXi_safeRadius_windowFinset_stability ...
```

または annulus no-zero theorem を先に置いてよい。

```lean
theorem exists_pascalCenteredXi_zeroFreeRadialAnnulus
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ z : ℂ,
        |Complex.abs z - R| < ε →
        pascalCenteredRiemannXiKernel z ≠ 0
```

ただし centered kernel の変数がすでに centered coordinate `z` なら `Complex.abs z`、標準 zeta zero `s` を使う既存 API なら `dist s criticalLineCenter` を使う。

**座標を混同しないこと。**

### Gate B

少なくとも Set window local constancy または equivalent annulus theorem が Green。

RH を使わない。

---

# 6. 実装 Phase C — generic compact Mellin admissibility Core

新規 generic module 第一候補:

```text
DkMath/Analysis/MellinCompactSupport.lean
```

namespace:

```lean
namespace DkMath.Analysis
```

CFBRC や zeta を import しない。

## 6.1 API shape

最初から一つの巨大 structure を作る必要はない。

まず theorem-oriented API を優先する。

概念的に、`h : ℝ → ℂ` と `0 < a`, `a < b` に対して

```text
support h ⊆ Icc a b
```

と、十分な integrability/continuity 条件から Mellin convergence を導く。

候補 theorem:

```lean
theorem mellinConvergent_of_support_subset_Icc_pos
    {h : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a)
    (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (... minimal regularity hypotheses ...) :
    ∀ s : ℂ, MellinConvergent h s := by
  ...
```

`Function.support` / `tsupport` / `HasCompactSupport` のどれを使うかは pinned Mathlib API と proof ergonomics で決める。

重要なのは **support が 0 から正距離離れている**ことを theorem statement で保持すること。

単なる `HasCompactSupport h` だけでは support が `0` に触れる可能性があり、任意 `s` に対する Mellin convergence を自動的に主張しない。

## 6.2 regularity assumptions

可能なら次の弱い順で採用を検討する。

```text
A. IntegrableOn h (Icc a b) + support containment
B. ContinuousOn h (Icc a b) + compact interval
C. ContDiff / compact smooth function
```

Mellin kernel `x^(s-1)` は `a ≤ x ≤ b`, `a>0` 上で bounded/continuous なので、A または B で十分なら不要に `ContDiff` を要求しない。

XDP-005 で smooth explicit-formula class が必要になれば後で強める。

### Gate C

任意 `s : ℂ` に対する Mellin convergence theoremが Green。

---

# 7. 実装 Phase D — mirror support transport

XDP-003 の

```lean
mellinCriticalMirror h x
```

について、positive-domain support が reciprocal interval に移ることを証明する。

概念的に

$$
\operatorname{supp}(h)\subseteq[a,b],\quad0<a\le b
$$

なら

$$
\operatorname{supp}(h^\vee)\cap(0,\infty)
\subseteq[1/b,1/a].
$$

`mellinCriticalMirror` は positive domain 外の定義を確認し、global support equality を無理に主張しない。

候補 theorem:

```lean
theorem mellinCriticalMirror_support_pos_subset
    {h : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b) :
    {x : ℝ | 0 < x ∧ mellinCriticalMirror h x ≠ 0} ⊆
      Set.Icc b⁻¹ a⁻¹ := by
  ...
```

exact formulation は current definition に合わせる。

これを Phase C の convergence theorem と接続して、mirror side にも

```lean
∀ s, MellinConvergent (mellinCriticalMirror h) s
```

を得る。

候補 endpoint:

```lean
theorem mellinConvergent_mellinCriticalMirror_of_support_subset_Icc_pos ...
```

### Gate D

XDP-003 の reflection theorem の両 convergence hypotheses を compact-positive-support data から供給できる。

---

# 8. 実装 Phase E — admissible reflection corollary

Phase C/D を使い、XDP-003 の main theorem を convergence hypotheses を外から手渡さず使える corollary にする。

候補:

```lean
theorem mellin_mellinCriticalMirror_of_compact_pos_support
    {h : ℝ → ℂ} {a b : ℝ}
    (... support / regularity hypotheses ...)
    (s : ℂ) :
    mellin (mellinCriticalMirror h) s =
      (starRingEnd ℂ) (mellin h (1 - (starRingEnd ℂ) s)) := by
  ...
```

centered formも短い corollary として追加可能。

```lean
theorem mellin_mellinCriticalMirror_centered_of_compact_pos_support ...
```

既存 XDP-003 theorem を再証明せず、convergence provider として合成する。

### Gate E

compact-positive-support → two-sided Mellin admissibility → centered mirror identity の chain が Green。

---

# 9. CFBRC thin bridge — optional / minimal

safe-radius theorem を CFBRC module に置く第一候補:

```text
DkMath/RH/CFBRC/PascalCenteredXiSafeRadiusAnnulusBridge.lean
```

Mellin compact-support Core は `DkMath.Analysis` に置く。

必要なら CFBRC 側で XDP-003 adapter と generic compact-support theorem を import し、次の convenience theorem を一つだけ置く。

```text
compact-positive-support h
→ Mellin reflection at criticalMirror parameter without manual convergence proofs
```

ただし Xi / zero window と `h` をこの phase で結合しない。

---

# 10. 明示的禁止事項

XDP-004 では次を行わない。

1. `RiemannHypothesis` を仮定しない。
2. `PascalCenteredXiFixedDefectVanishesOnSafeRadii` を仮定しない。
3. fixed Xi defect `= 0` / `≤ 0` を証明しない。
4. classical Weil criterion を実装済みと呼ばない。
5. Guinand–Weil explicit formula を実装済みと呼ばない。
6. finite Weil-style pairing を classical infinite Weil form と同一視しない。
7. spectral radial bump が Mellin transform の像にあると無証明で置かない。
8. hard zero-window indicator を Mellin test function と同一視しない。
9. `HasCompactSupport h` だけから任意 `s` の Mellin convergence を主張しない。support が 0 から離れる hypothesis を保持する。
10. XDP-001 / XDP-003 Green theorem を再証明しない。
11. `sorry`, `admit`, 新規 `axiom`, `native_decide` を導入しない。

---

# 11. Build / validation gates

新規 module ごとに単体 build を行う。

例:

```bash
cd lean/dk_math

lake env lean DkMath/Analysis/MellinCompactSupport.lean
lake env lean DkMath/RH/CFBRC/PascalCenteredXiSafeRadiusAnnulusBridge.lean
```

その後 repository standard gates:

```bash
./lean-build.sh
./lean-test.sh
git diff --check
```

新規 module について:

```bash
grep -R "sorry\|admit\|axiom\|native_decide" \
  DkMath/Analysis/MellinCompactSupport.lean \
  DkMath/RH/CFBRC/PascalCenteredXiSafeRadiusAnnulusBridge.lean
```

既存別 module の `sorry` warning は本 phase の failure としないが、新規追加は禁止。

public root import は単体 Green 後に追加する。

---

# 12. XDP-004 完了条件

XDP-004 は次を満たしたとき完了とする。

## H1 side

- safe radius から正の radial margin / annulus が得られる。
- その margin 内で zero window が局所的に不変である。
- RH を使わない。

## H2 side

- support が `[a,b]`, `0<a≤b` に入る generic complex-valued `h` について、適切な minimal regularity hypothesis から `MellinConvergent h s` を任意 `s` に対して得る。
- `mellinCriticalMirror h` の reciprocal positive support を制御する。
- mirror side についても任意 `s` の Mellin convergence を得る。
- XDP-003 reflection theoremを convergence proof 込みで呼べる corollary を得る。

## Boundary

- spectral hard cutoff / radial smooth cutoff と Mellin transform の exact realization は未解決として明記する。
- explicit formula はまだ未実装と明記する。

---

# 13. 実装結果 report

完了時に次を作成する。

```text
DkMath/RH/CFBRC/docs/wip/RH-CFBRC-fixed-Xi-defect-provider/
  XDP-004-Safe-radius-annulus-and-compact-Mellin-admissibility-result.md
```

report には最低限次を記録する。

```text
1. safe-annulus proof route (B1/B2)
2. exact theorem names / signatures
3. zero-window local constancy の exact statement
4. compact Mellin convergence theorem の minimal hypotheses
5. mirror support transport theorem
6. XDP-003 reflection への合成 theorem
7. pinned Mathlib で再利用した主要 API
8. build/test result
9. H1/H2 のどこまでが閉じたか
10. spectral realization obstruction として残ったもの
11. XDP-005 に渡す最小 endpoint
```

---

# 14. XDP-005 への想定 handoff

XDP-004 が成功した後でも、次はまだ自動的に explicit formula ではない。

得られるのは

```text
safe R
→ finite zero window stable under small radius motion

compact-positive-support h
→ Mellin transform / mirror transform globally convergent
→ exact critical-mirror reflection law
```

までである。

XDP-005 の課題は、この二つを結ぶ **spectral realization / interpolation layer** を監査・構成することである。

候補は次の二系統を比較する。

```text
Route I: admissible Mellin family whose zero evaluations approximate/control the finite defect
Route C: fixed-Xi contourを prime-safe half-plane へ変形し、Mellin kernelを contour weight として使う
```

XDP-004 の report では、実装結果に照らしてどちらが少ない新規解析で済むかを推奨する。

ここで初めて、Mellin-first を続けるか fixed-contour transport を併用するか判断する。
