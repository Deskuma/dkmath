# PPW-023 — fixed centered-Xi full second-moment defect functional 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
verified head before this handoff: fab95a8c7d1e714fca1c824c2622c80e0cc24781
previous checkpoint: PPW-022 complete Green
previous implementation: PascalCenteredXiRadialLayerCakeOuterCountBridge.lean
Lean toolchain: v4.32.2
mathlib rev: 905b95818eb32af7874a58b427f50c1711a5e96c
```

PPW-021 と PPW-022 により、有限 zero window の second-moment identity に現れる二つの量は、どちらも fixed centered-Xi observable から取得できるようになった。

```text
holomorphic side:
  M2_R = Σ m_a a^2
  ← one fixed z^2 outer contour of -Xi_c'/Xi_c

radial side:
  Q_R = Σ m_a |a|^2
  ← radius-indexed fixed Xi outer multiplicity counts
  ← layer-cake interval integral
```

既存 PPW-016 の exact identity は

```text
2 * HorizontalEnergy_R
  = RadialSecondMoment_R + Re(CenteredSecondMoment_R)
```

である。

PPW-021 の normalized second outer contour は centered second moment の負値を読むため、既存 defect は概念的に

```text
Defect_R
  = Q_R - Re(C2_R)
```

ここで

```text
C2_R := (2πi)^(-1) * XiSecondOuterContourMass(R)
```

と書ける。

PPW-022 では `Q_R` 自身も fixed Xi outer-count family だけで

```text
Q_R
  = R^2 * OuterCount(R)
      - ∫ r in 0..R, 2*r*OuterCount(r)
```

へ変換された。

PPW-023 の目的は、これら二本を一つに束ねて、**zero list を定義に含まない fixed centered-Xi second-moment defect functional** を作ることである。

これは新しい RH estimate を証明する checkpoint ではない。

最終的に得る functional は既存 finite defect と exact に一致し、その nonnegativity / zero detector / off-critical detector をすべて transport する。さらに global vanishing condition が RH と同値であることを frontier audit として明示してよいが、**その vanishing を独立に証明してはならない。**

---

## 2. 推奨 module

```text
DkMath.RH.CFBRC.PascalCenteredXiFixedSecondMomentDefectBridge
```

新規 file:

```text
lean/dk_math/DkMath/RH/CFBRC/
  PascalCenteredXiFixedSecondMomentDefectBridge.lean
```

公開 import:

```lean
import DkMath.RH.CFBRC.PascalCenteredXiFixedSecondMomentDefectBridge
```

を `DkMath/RH.lean` の PPW-022 import の直後へ追加する。

推奨 import は最小限にする。

```lean
import DkMath.RH.CFBRC.PascalCenteredXiRadialLayerCakeOuterCountBridge
import Mathlib.Tactic
```

PPW-022 が PPW-021 以下を transitively import しているため、不必要な重複 import は避ける。

---

## 3. 既存 exact API — 再実装禁止

PPW-016 には既に次がある。

```lean
pascalCriticalMirrorZeroWindowSecondMomentDefect
pascalCriticalMirrorZeroWindowSecondMomentDefect_eq
pascalCriticalMirrorZeroWindowSecondMomentDefect_eq_zero_iff
pascalCriticalMirrorZeroWindowSecondMomentDefect_pos_iff
pascalCriticalMirrorZeroWindowHorizontalEnergy_nonneg
pascalCriticalMirrorZeroWindowHorizontalEnergy_eq_zero_iff
pascalCriticalMirrorZeroWindowHorizontalEnergy_pos_iff
```

特に

```text
pascalCriticalMirrorZeroWindowSecondMomentDefect R
  = 2 * pascalCriticalMirrorZeroWindowHorizontalEnergy R
```

は Green 済み。

PPW-021 には既に

```lean
pascalCenteredXiNormalizedSecondOuterContourMass_eq_windowCenteredSecondMoment
pascalSecondMomentDefect_eq_radial_sub_centeredXiOuter_re
```

がある。

PPW-022 には既に

```lean
pascalCenteredXiOuterCount
pascalCenteredXiZeroDiskRadialSecondMoment_eq_fixedXiOuterCountLayerCake
pascalCriticalMirrorZeroWindowRadialSecondMoment_eq_fixedXiOuterCountLayerCake
pascalCriticalMirrorZeroWindowCF2DRadialMass_eq_fixedXiOuterCountLayerCake
```

がある。

これらを再証明しない。

---

# Phase A — fixed Xi radial functional を theorem-facing name で固定

PPW-022 の RHS を新しい theorem-facing observable として定義する。

候補:

```lean
noncomputable def pascalCenteredXiFixedRadialSecondMomentFunctional
    (R : ℝ) : ℝ :=
  R ^ 2 * pascalCenteredXiOuterCount R -
    (∫ r in 0..R, 2 * r * pascalCenteredXiOuterCount r)
```

この定義には zero Finset、zero multiplicity、`Complex.normSq` を直接入れない。

boundary-safe `R` について次を証明する。

```lean
theorem pascalCenteredXiFixedRadialSecondMomentFunctional_eq_windowRadial
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedRadialSecondMomentFunctional R =
      pascalCriticalMirrorZeroWindowRadialSecondMoment R
```

さらに CF2D route との exact compatibility を出す。

```lean
theorem pascalCenteredXiFixedRadialSecondMomentFunctional_eq_cf2dRadial
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedRadialSecondMomentFunctional R =
      pascalCriticalMirrorZeroWindowCF2DRadialMass R
```

ここで PPW-017 の frozen radial contour weight へ戻らない。

---

# Phase B — fixed holomorphic second-contour functional

PPW-021 の normalized second outer contour に読みやすい名前を与える。

```lean
noncomputable def pascalCenteredXiFixedHolomorphicSecondContourFunctional
    (R : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    pascalCenteredXiSecondOuterContourMass R
```

boundary-safe `R` で既存 theorem から

```lean
theorem pascalCenteredXiFixedHolomorphicSecondContourFunctional_eq
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedHolomorphicSecondContourFunctional R =
      -pascalCriticalMirrorZeroWindowCenteredSecondMoment R
```

を出す。

注意:

```text
この functional は C2_R = -M2_R を読む。
```

符号を逆に記憶しないこと。

---

# Phase C — full fixed-Xi second-moment defect functional

PPW-023 の主定義。

```lean
noncomputable def pascalCenteredXiFixedSecondMomentDefectFunctional
    (R : ℝ) : ℝ :=
  pascalCenteredXiFixedRadialSecondMomentFunctional R -
    (pascalCenteredXiFixedHolomorphicSecondContourFunctional R).re
```

展開すると、定義は fixed Xi observable のみからなる。

```text
R^2 * OuterCount(R)
- ∫_0^R 2r OuterCount(r) dr
- Re[(2πi)^(-1) * XiSecondOuterContourMass(R)]
```

zero list、mirror-frozen weight、`normSq` を定義へ戻さない。

boundary-safe `R` で最重要 theorem:

```lean
@[simp] theorem pascalCenteredXiFixedSecondMomentDefectFunctional_eq_existing
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedSecondMomentDefectFunctional R =
      pascalCriticalMirrorZeroWindowSecondMomentDefect R
```

これが PPW-023 の第一 mandatory endpoint。

---

# Phase D — horizontal energy detector を fixed Xi functional へ transport

既存 PPW-016 から、boundary-safe `R` で

```lean
theorem pascalCenteredXiFixedSecondMomentDefectFunctional_eq_two_mul_horizontalEnergy
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedSecondMomentDefectFunctional R =
      2 * pascalCriticalMirrorZeroWindowHorizontalEnergy R
```

を得る。

その直後に次を transport する。

```lean
theorem pascalCenteredXiFixedSecondMomentDefectFunctional_nonneg
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    0 ≤ pascalCenteredXiFixedSecondMomentDefectFunctional R
```

```lean
theorem pascalCenteredXiFixedSecondMomentDefectFunctional_eq_zero_iff
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedSecondMomentDefectFunctional R = 0 ↔
      ∀ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
        ρ.re = (1 : ℝ) / 2
```

```lean
theorem pascalCenteredXiFixedSecondMomentDefectFunctional_pos_iff
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    0 < pascalCenteredXiFixedSecondMomentDefectFunctional R ↔
      ∃ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
        ρ.re ≠ (1 : ℝ) / 2
```

これにより new functional は finite window 上で exact off-critical detector になる。

**ただしこの detector が常に zero であることは証明しない。**

---

# Phase E — Pascal prime-mirror energy との zero-condition compatibility

既存 PPW-013 / PPW-016 の zero-condition bridge をそのまま transport する。

```lean
theorem pascalCenteredXiFixedSecondMomentDefectFunctional_eq_zero_iff_primeMirrorEnergy
    {n : ℕ} (hn : 1 < n)
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedSecondMomentDefectFunctional R = 0 ↔
      pascalCriticalMirrorZeroWindowEnergy n R = 0
```

ここで termwise equality を作らない。

```text
fixed Xi defect
```

と

```text
primeMirror window energy
```

の equality を主張するのではなく、既存どおり **zero condition の同値だけ**を使う。

---

# Phase F — CF2D `q2` / Xi holomorphic contour の合流表示

PPW-022 の CF2D radial theorem を使い、同じ defect を

```text
CF2D radial q2 mass
  - fixed Xi holomorphic second contour real part
```

として表す theorem を追加する。

候補:

```lean
theorem pascalCenteredXiFixedSecondMomentDefectFunctional_eq_cf2d_sub_secondContour_re
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiFixedSecondMomentDefectFunctional R =
      pascalCriticalMirrorZeroWindowCF2DRadialMass R -
        (pascalCenteredXiFixedHolomorphicSecondContourFunctional R).re
```

これは PPW-017 の CF2D `q2` route と PPW-021/022 の fixed Xi route を同じ theorem surface へ集約するための bridge である。

ここでも `q2` 保存だけから defect zero を導かない。

---

# Phase G — global frontier audit

PPW-023 で最も重要な研究監査。

fixed functional が全 boundary-safe disk で消えるという property を明示的に定義する。

候補:

```lean
def PascalCenteredXiFixedDefectVanishesOnSafeRadii : Prop :=
  ∀ R : ℝ,
    IsPascalCenteredXiBoundarySafeRadius R →
      pascalCenteredXiFixedSecondMomentDefectFunctional R = 0
```

そして、可能なら次を証明する。

```lean
theorem pascalCenteredXiFixedDefectVanishesOnSafeRadii_iff_riemannHypothesis :
    PascalCenteredXiFixedDefectVanishesOnSafeRadii ↔
      RiemannHypothesis
```

証明方針:

### RH → vanishing

任意の boundary-safe `R` を固定する。
RH から window 内の全 nontrivial zero が `re = 1 / 2`。
Phase D の zero iff theorem で functional zero。

### vanishing → RH

任意の nontrivial zero `ρ` を固定する。

既存 PPW-020 の

```lean
exists_isPascalCenteredXiBoundarySafeRadius_gt
```

を使い、

```text
R > dist ρ criticalLineCenter
```

を満たす boundary-safe radius を選ぶ。

すると `ρ` は PPW window `R` に入る。
global vanishing hypothesis から fixed defect は zero。
Phase D の zero iff theorem から `ρ.re = 1 / 2`。

最後に project 既存の RH packaging theorem または `RiemannHypothesis` の定義へ戻す。

### 重要

この iff theorem は **frontier audit** である。

```text
fixed Xi functional vanishing
```

を別名で RH より弱い theorem のように扱ってはならない。

この theorem が Green になったら、PPW-023 は

```text
Prime/Pascal/Xi/CF2D の形式化が
どの exact scalar functional の vanishing に集約されたか
```

を完全に監査できたことになる。

---

# Phase H — optional bounded-window packaging

実装量に余裕がある場合のみ、boundary-safe `R` に対する finite condition を structure / proposition にまとめてもよい。

例:

```lean
def PascalCenteredXiFixedDefectZeroAtSafeRadius (R : ℝ) : Prop :=
  IsPascalCenteredXiBoundarySafeRadius R ∧
    pascalCenteredXiFixedSecondMomentDefectFunctional R = 0
```

ただし API 増殖のためだけの wrapper は不要。
Phase A〜G の theorem surface が十分なら追加しない。

---

## 4. 必須 acceptance criteria

PPW-023 complete Green の最低条件は次。

```text
A. fixed radial functional
B. fixed normalized holomorphic second-contour functional
C. full fixed Xi defect functional
D. fixed defect = existing PPW-016 defect on boundary-safe radii
E. fixed defect = 2 * horizontal energy
F. nonnegative / zero iff all window zeros critical / positive iff off-critical exists
G. primeMirror window energy との zero-condition bridge
H. CF2D radial mass + fixed Xi second contour の合流表示
I. RH frontier を過剰主張しない module documentation
```

Phase G の global iff RH theorem は **strongly recommended**。
実装 API 上の予期せぬ障害がある場合だけ、blocking にせず handoff に exact obstruction を記録する。

---

## 5. 数学的停止条件

以下は禁止。

1. `pascalCenteredXiFixedSecondMomentDefectFunctional R = 0` を独立証明したことにしない。
2. global vanishing property を RH より弱い新条件として宣伝しない。全 safe radii vanishing は RH-equivalent frontier の候補である。
3. unsafe radius で `OuterCount(r) = multiplicity(r)` を pointwise 使用しない。PPW-022 と同じく a.e. replacement のみ。
4. `Complex.normSq` を holomorphic contour weight にしない。
5. PPW-017 の zero-dependent mirror-frozen weight を fixed functional の定義へ戻さない。
6. `q2` 保存だけから horizontal energy zero を導かない。
7. Xi evenness や mirror symmetry だけから defect zero を導かない。
8. finite window の identity を無条件に `R → ∞` へ極限移行しない。
9. contour と radius integral の順序交換を新たに行わない。PPW-022 の既証明 layer-cake representation をそのまま使う。
10. prime-side energy と fixed Xi defect の termwise equality を作らない。現時点では zero-condition bridge のみ。
11. RH、off-critical exclusion、`HorizontalEnergy = 0` を theorem 名だけ変えて新しい provider としない。

---

## 6. docstring に明記する研究上の意味

module 冒頭に次の趣旨を書く。

```text
PPW-023 packages the two fixed centered-Xi representations obtained in
PPW-021 and PPW-022 into one zero-list-free finite second-moment defect
functional.  On boundary-safe radii this functional is exactly the existing
PPW-016 defect and therefore exactly twice the finite horizontal energy.

This is a representation and frontier-audit module.  It does not prove the
functional vanishes.  Proving its vanishing for every sufficiently large
boundary-safe radius would be an RH-level statement, not routine contour
bookkeeping.
```

---

## 7. build / audit

最低限:

```bash
lake build DkMath.RH.CFBRC.PascalCenteredXiFixedSecondMomentDefectBridge
lake build DkMath.RH
./lean-build.sh DkMath.RH.CFBRC.PascalCenteredXiFixedSecondMomentDefectBridge
git diff --check
```

新規 module 内を監査:

```bash
grep -nE '\bsorry\b|\baxiom\b|\badmit\b|TODO|FIXME' \
  lean/dk_math/DkMath/RH/CFBRC/PascalCenteredXiFixedSecondMomentDefectBridge.lean
```

既存 repository 全体の研究 `sorry` を PPW-023 の failure と誤認しない。

---

# 8. PPW-023 後の ROADMAP

PPW-023 が Green なら、representation layer は次の一個の scalar functional へ完全に収束する。

```text
FixedXiDefect(R)
  = fixed Xi radial outer-count layer cake
      - Re(fixed Xi normalized z^2 outer contour)

  = existing SecondMomentDefect(R)
  = 2 * HorizontalEnergy(R)
```

ここから先は contour bookkeeping の続きではない。
独立な analytic / arithmetic provider を探す frontier に入る。

次 checkpoint は一本に決め打ちせず、三方向の audit から最も独立性の高いものを選ぶ。

```text
PPW-024A — Prime / explicit-formula provider audit
  fixed Xi defect またはその差分を Λ / prime-side quantity へ変換できるか

PPW-024B — CF2D q2 / ThreeElement provider audit
  fixed radial functional と CF2D conserved q2 から独立 constraint が出るか

PPW-024C — centered Xi symmetry / moment identity audit
  evenness・conjugation・functional equation が
  M2 と radial layer count の間に RH を仮定しない追加 identity を与えるか
```

どの route でも、最初に確認すべき問いは一つ。

```text
その新しい theorem は、既に
  FixedXiDefect = 0
または
  RH
と同値な statement を名前だけ変えたものではないか？
```

独立な identity / estimate が見つからない場合は、その failure を named obstruction として残す。

PPW-023 の目的は RH を閉じることではなく、**ここまでの Prime → Xi → contour → radial q2 の全形式化が、どの exact fixed observable の独立評価を待っているのかを一意に固定すること**である。
