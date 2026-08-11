# PPW-013 — critical-mirror finite zero-window energy bridge 実装指示

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-012 Green
Lean toolchain: v4.32.2
```

PPW-012 までで、Pascal prime-power 側から得た有限 PHZ cutoff の安全領域極限は

```text
pascalZetaNegLogDeriv s = - logDeriv riemannZeta s
```

という meromorphic target に固定され、simple zeta zero では punctured neighborhood で residue signature `-1` を持つことまで Green になった。

一方、CFBRC 側には既に

```text
criticalMirror s = ⟨1 - s.re, s.im⟩
```

という critical-line reflection と、nontrivial zeta zero が `criticalMirror` で再び nontrivial zeta zero へ移る theorem が存在する。

PPW-013 の目的は、この二つを **有限 mirror-stable zero window** の中で接続し、各 zero の横ずれを既存 `primeMirrorOffsetGapAt` で読み取る **非負有限 energy** を構成することである。

この checkpoint の本質は次の有限構造である。

```text
nontrivial zeta zeros in a compact window
        ↓ finite
criticalMirror-stable Finset
        ↓
primeMirrorOffsetGapAt n ρ ≥ 0
        ↓
window energy = finite sum of mirror Gaps
```

この energy がゼロであることと、その有限 window 内の全 nontrivial zero が critical line 上にあることを exact に同値化する。

**重要:** これは有限 window の局所的 zero-geometry theorem であり、RH の証明ではない。全 window に対するゼロ energy を独立に証明してはならない。その全称化は RH と同値な境界へ戻るため、この checkpoint では行わない。

---

## 2. 新規 module

```text
DkMath.RH.CFBRC.PascalCriticalMirrorZeroWindowEnergyBridge
```

候補 file:

```text
lean/dk_math/DkMath/RH/CFBRC/PascalCriticalMirrorZeroWindowEnergyBridge.lean
```

推奨 import:

```lean
import DkMath.RH.CFBRC.PascalZetaLogDerivativeZeroBridge
import DkMath.RH.CFBRC.CriticalMirrorZeroBridge
import DkMath.RH.CFBRC.PrimeMirrorOffsetCore
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
```

単体 Green 後に `DkMath/RH.lean` へ公開 import を追加する。

---

## 3. 既存 API — 再実装禁止

### 3.1 CFBRC critical mirror

現在 branch には既に以下がある。

```lean
noncomputable def criticalMirror (s : ℂ) : ℂ :=
  ⟨1 - s.re, s.im⟩

@[simp] theorem criticalMirror_re (s : ℂ) :
    (criticalMirror s).re = 1 - s.re

@[simp] theorem criticalMirror_im (s : ℂ) :
    (criticalMirror s).im = s.im

theorem criticalMirror_involutive (s : ℂ) :
    criticalMirror (criticalMirror s) = s

theorem criticalMirror_eq_self_iff_re_eq_half (s : ℂ) :
    criticalMirror s = s ↔ s.re = (1 : ℝ) / 2
```

`criticalMirror` の duplicate definition を作らないこと。

### 3.2 nontrivial zero mirror bridge

既存 `CriticalMirrorZeroBridge` に以下がある。

```lean
theorem nontrivialRiemannZetaZero_mem_openCriticalStrip
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    0 < s.re ∧ s.re < 1

theorem riemannZeta_criticalMirror_eq_zero_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    riemannZeta (criticalMirror s) = 0

theorem criticalMirror_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    NontrivialRiemannZetaZero (criticalMirror s)
```

したがって PPW-013 で functional equation を再証明しないこと。

### 3.3 PPW-012 zero-side API

```lean
noncomputable def pascalZetaNegLogDeriv (s : ℂ) : ℂ :=
  - logDeriv riemannZeta s

theorem tendsto_mul_pascalZetaNegLogDeriv_simpleZero ...

theorem finite_riemannZetaZeros_in_compact
    {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ riemannZetaZeros).Finite
```

### 3.4 prime-mirror Gap API

既存 `PrimeMirrorOffsetCore` に以下がある。

```lean
noncomputable def primeMirrorOffsetGapAt
    (n : ℕ) (s : ℂ) : ℝ

theorem primeMirrorOffsetGap_nonneg ...

theorem primeMirrorOffsetGapAt_eq_zero_iff_re_eq_half
    {n : ℕ} (hn : 1 < n) (s : ℂ) :
    primeMirrorOffsetGapAt n s = 0 ↔
      s.re = (1 : ℝ) / 2

theorem primeMirrorOffsetGapAt_pos_of_re_ne_half
    {n : ℕ} (hn : 1 < n) {s : ℂ}
    (hre : s.re ≠ (1 : ℝ) / 2) :
    0 < primeMirrorOffsetGapAt n s
```

これを zero-window energy の正本 detector とする。新しい平方距離 detector を別定義しない。

---

## 4. Mathlib API audit

実装時に `#check` で current toolchain の exact type を確認すること。

利用候補:

```lean
isCompact_closedBall
Set.Finite.subset
Set.Finite.toFinset
Finset.mem_image
Finset.sum_nonneg
Finset.sum_eq_zero_iff_of_nonneg
Finset.sum_pos_iff_of_nonneg
```

`ℂ` は proper metric space なので、closed ball は compact。

必要であれば

```lean
#check isCompact_closedBall
#check Finset.sum_eq_zero_iff_of_nonneg
#check Finset.sum_pos_iff_of_nonneg
```

で確認する。

---

## 5. Phase A — `NontrivialRiemannZetaZero` と `riemannZetaZeros` の薄い bridge

まず theorem-facing convenience lemma を追加する。

候補:

```lean
/-- Every CFBRC nontrivial zero belongs to Mathlib's zeta-zero set. -/
theorem nontrivialRiemannZetaZero_mem_riemannZetaZeros
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) :
    s ∈ riemannZetaZeros := by
  exact mem_riemannZetaZeros.mpr hs.1
```

逆向きは一般には trivial zero 除外条件を含まないため、無条件 iff を作らない。

---

## 6. Phase B — critical-line centered compact window

### 6.1 center

局所 helper として critical-line の real-axis center を定義してよい。

```lean
noncomputable def criticalLineCenter : ℂ :=
  ((1 : ℂ) / 2)
```

ただし repository 内に同値の既存定義がある場合はそれを再利用する。

### 6.2 mirror は center からの距離を保存

load-bearing geometry:

```lean
theorem dist_criticalMirror_criticalLineCenter
    (s : ℂ) :
    dist (criticalMirror s) criticalLineCenter =
      dist s criticalLineCenter
```

証明は `Complex.ext` ではなく距離 / norm の実部・虚部展開で行ってよい。

狙いは reflection の isometry 全般を構築することではなく、centered closed ball の membership 保存だけである。

続けて

```lean
@[simp] theorem criticalMirror_mem_closedBall_iff
    {R : ℝ} {s : ℂ} :
    criticalMirror s ∈ Metric.closedBall criticalLineCenter R ↔
      s ∈ Metric.closedBall criticalLineCenter R
```

を作る。

`criticalMirror_involutive` と距離保存を使い、余計な global isometry structure は作らなくてよい。

---

## 7. Phase C — finite nontrivial zero window

### 7.1 Set definition

```lean
noncomputable def pascalCriticalMirrorZeroWindow (R : ℝ) : Set ℂ :=
  {s | s ∈ Metric.closedBall criticalLineCenter R ∧
    NontrivialRiemannZetaZero s}
```

この window は **nontrivial zero 専用** とする。

`Metric.closedBall ... R ∩ riemannZetaZeros` そのものを window としてはいけない。そこには trivial zeros が入り、`criticalMirror` closure が壊れる。

### 7.2 membership theorem

```lean
@[simp] theorem mem_pascalCriticalMirrorZeroWindow_iff
    {R : ℝ} {s : ℂ} :
    s ∈ pascalCriticalMirrorZeroWindow R ↔
      s ∈ Metric.closedBall criticalLineCenter R ∧
      NontrivialRiemannZetaZero s := by
  rfl
```

### 7.3 finiteness

```lean
theorem finite_pascalCriticalMirrorZeroWindow
    (R : ℝ) :
    (pascalCriticalMirrorZeroWindow R).Finite
```

推奨 proof route:

1. `isCompact_closedBall criticalLineCenter R` を取得。
2. PPW-012 `finite_riemannZetaZeros_in_compact` から
   `closedBall ∩ riemannZetaZeros` が finite。
3. `pascalCriticalMirrorZeroWindow R` がその subset であることを示す。
4. `Set.Finite.subset` で閉じる。

nontrivial-zero set 自体の closedness を新規証明する必要はない。

### 7.4 Finset packaging

```lean
noncomputable def pascalCriticalMirrorZeroWindowFinset
    (R : ℝ) : Finset ℂ :=
  (finite_pascalCriticalMirrorZeroWindow R).toFinset
```

membership API:

```lean
@[simp] theorem mem_pascalCriticalMirrorZeroWindowFinset_iff
    {R : ℝ} {s : ℂ} :
    s ∈ pascalCriticalMirrorZeroWindowFinset R ↔
      s ∈ pascalCriticalMirrorZeroWindow R
```

---

## 8. Phase D — mirror-stability of the finite window

まず Set-level:

```lean
@[simp] theorem criticalMirror_mem_pascalCriticalMirrorZeroWindow_iff
    {R : ℝ} {s : ℂ} :
    criticalMirror s ∈ pascalCriticalMirrorZeroWindow R ↔
      s ∈ pascalCriticalMirrorZeroWindow R
```

必要なものは既に揃っている。

- closed ball membership: Phase B
- zero predicate closure: `criticalMirror_nontrivialRiemannZetaZero`
- reverse direction: `criticalMirror_involutive`

続けて Finset-level image equality:

```lean
theorem image_criticalMirror_pascalCriticalMirrorZeroWindowFinset
    (R : ℝ) :
    (pascalCriticalMirrorZeroWindowFinset R).image criticalMirror =
      pascalCriticalMirrorZeroWindowFinset R
```

これは今後 finite orbit pairing / finite sums を行うための load-bearing theorem。

**注意:** mirror stability は off-critical zero の不可能性を意味しない。off-critical zero が存在するなら、window 内で distinct mirror pair を作るだけである。

---

## 9. Phase E — prime-mirror Gap の criticalMirror invariance

既存 `primeMirrorOffsetGapAt` は centered offset の符号反転に対して不変であるはずなので、これを exact theorem にする。

目標:

```lean
@[simp] theorem primeMirrorOffsetGapAt_criticalMirror
    (n : ℕ) (s : ℂ) :
    primeMirrorOffsetGapAt n (criticalMirror s) =
      primeMirrorOffsetGapAt n s
```

推奨 proof route:

```text
criticalMirror_re
centeredSigma (1 - s.re) = - centeredSigma s.re
left/right amplitude swap under δ ↦ -δ
square of the difference is unchanged
```

既存 theorem が repository 内に存在する場合は再利用し、新規 duplicate を作らない。

この theorem は zero-window energy が mirror orbit 上で同じ座標 energy を持つことを保証する。

---

## 10. Phase F — finite zero-window mirror energy

### 10.1 definition

mode `n` を一般に保つ。

```lean
noncomputable def pascalCriticalMirrorZeroWindowEnergy
    (n : ℕ) (R : ℝ) : ℝ :=
  ∑ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
    primeMirrorOffsetGapAt n ρ
```

固定 `n = 2` 専用定義は不要。必要なら最後に convenience theorem を置く程度にする。

### 10.2 nonnegative

```lean
theorem pascalCriticalMirrorZeroWindowEnergy_nonneg
    (n : ℕ) (R : ℝ) :
    0 ≤ pascalCriticalMirrorZeroWindowEnergy n R
```

各 summand は square Gap なので非負。

### 10.3 zero iff every zero in the window is critical

この checkpoint の主定理。

```lean
theorem pascalCriticalMirrorZeroWindowEnergy_eq_zero_iff
    {n : ℕ} (hn : 1 < n) (R : ℝ) :
    pascalCriticalMirrorZeroWindowEnergy n R = 0 ↔
      ∀ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
        ρ.re = (1 : ℝ) / 2
```

推奨 route:

1. `Finset.sum_eq_zero_iff_of_nonneg`。
2. 各 term について `primeMirrorOffsetGapAt_eq_zero_iff_re_eq_half hn ρ`。

この theorem は finite energy と finite RH-condition の exact equivalence である。

### 10.4 positive iff an off-critical zero exists in the window

可能なら同 checkpoint で閉じる。

```lean
theorem pascalCriticalMirrorZeroWindowEnergy_pos_iff
    {n : ℕ} (hn : 1 < n) (R : ℝ) :
    0 < pascalCriticalMirrorZeroWindowEnergy n R ↔
      ∃ ρ ∈ pascalCriticalMirrorZeroWindowFinset R,
        ρ.re ≠ (1 : ℝ) / 2
```

`Finset.sum_pos_iff_of_nonneg` と
`primeMirrorOffsetGapAt_pos_of_re_ne_half` を使う。

これは hypothetical off-critical zero を **正の有限 mirror energy** として検出する theorem になる。

---

## 11. Phase G — PPW-012 pole signature の window wrapper

これは薄い wrapper でよいが、PPW-014 の contour audit に備えて追加する価値がある。

```lean
theorem tendsto_mul_pascalZetaNegLogDeriv_simpleZero_of_mem_window
    {R : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ pascalCriticalMirrorZeroWindow R)
    (hρsimple : deriv riemannZeta ρ ≠ 0) :
    Tendsto (fun w => (w - ρ) * pascalZetaNegLogDeriv w)
      (nhdsWithin ρ {ρ}ᶜ) (nhds (-1))
```

proof は PPW-012 theorem へ membership から `riemannZetaZeros` を渡すだけ。

**重要:** これを使って「window 内の全 zero は simple」としない。zeta zero の simplicity は未知である。

---

## 12. 今回やらないこと

PPW-013 では以下を実装しない。

```text
argument principle
contour integral
residue sum theorem
explicit formula
zero multiplicity の完全 transport
全 zeta zero の simplicity
critical strip での finite PHZ convergence
window radius R → ∞ の energy limit
∀ R, windowEnergy = 0
RiemannHypothesis の導出
```

特に

```lean
∀ R, pascalCriticalMirrorZeroWindowEnergy n R = 0
```

を independent theorem として証明しようとしてはいけない。これは全 nontrivial zero を critical line へ押し込む内容であり、本質的に RH の再表現になる。

---

## 13. Stop conditions / audit warnings

次の推論は禁止。

1. `criticalMirror` が zero set を保存することから `criticalMirror s = s` を結論しない。
2. mirror pair が存在することからその pair が衝突すると結論しない。
3. scalar `-ζ'/ζ` の cancellation から prime coordinatewise Gap がゼロと結論しない。
4. finite window energy の非負性だけから energy `= 0` を結論しない。
5. simple-zero residue `-1` を multiplicity > 1 の zero にそのまま適用しない。
6. critical strip へ `∑ Λ(n)n^{-s}` の通常 partial sum convergence を延長しない。
7. `riemannZetaZeros` 全体を `criticalMirror` invariant としない。trivial zeros があるため、mirror invariance は `NontrivialRiemannZetaZero` 上で使う。
8. 新しい RH-equivalent theorem を「RH への前進」と呼ばない。独立 estimate / positivity が無ければ単なる reformulation である。

---

## 14. Build / acceptance criteria

最低限:

```text
lake build DkMath.RH.CFBRC.PascalCriticalMirrorZeroWindowEnergyBridge
lake build DkMath.RH
git diff --check
```

可能なら wrapper build も実行。

新規 module に

```text
sorry
axiom
admit
```

を追加しない。

acceptance theorem 群:

```lean
nontrivialRiemannZetaZero_mem_riemannZetaZeros

dist_criticalMirror_criticalLineCenter
criticalMirror_mem_closedBall_iff

finite_pascalCriticalMirrorZeroWindow
mem_pascalCriticalMirrorZeroWindowFinset_iff
criticalMirror_mem_pascalCriticalMirrorZeroWindow_iff
image_criticalMirror_pascalCriticalMirrorZeroWindowFinset

primeMirrorOffsetGapAt_criticalMirror

pascalCriticalMirrorZeroWindowEnergy_nonneg
pascalCriticalMirrorZeroWindowEnergy_eq_zero_iff
pascalCriticalMirrorZeroWindowEnergy_pos_iff
```

pole-signature wrapper は推奨だが、上記 finite mirror-window energy が Green なら PPW-013 必須 checkpoint は完了扱いでよい。

---

## 15. PPW-013 の意味

PPW-012 まででは、prime-side の Pascal / von Mangoldt object が zeta zero の局所 pole signature に到達した。

PPW-013 では、その zero を CFBRC の exact `criticalMirror` 幾何へ戻し、有限 window 内で

```text
zero geometry
  ↔ criticalMirror fixed-point condition
  ↔ primeMirrorOffsetGapAt = 0
  ↔ finite mirror energy = 0
```

を Green にする。

これにより次段階 PPW-014 は、finite window に含まれる meromorphic poles / zero multiplicities を contour または argument-principle 型の global quantityへ集約できるかを監査する段階になる。

PPW-014 で必要になる本当の新規数学は、**prime-side / boundary data からこの有限 mirror energy を強制的にゼロへ落とす独立 identity または positivity mechanism が存在するか**、という点である。
