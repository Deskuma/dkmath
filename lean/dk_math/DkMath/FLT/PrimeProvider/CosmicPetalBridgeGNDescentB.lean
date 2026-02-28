/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNCore

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.GcdNext

/-- Branch B の縮小に必要な純算術データ。 -/
structure WieferichDescentDataB (p x y z q : ℕ) : Prop where
  hqP : Nat.Prime q
  hpB : ¬ p ∣ (z - y)
  hq_not_dvd_gap : ¬ q ∣ (z - y)
  hdiff_eq : z ^ p - y ^ p = x ^ p
  hqpow_dvd_diff : q ^ p ∣ (z ^ p - y ^ p)
  hfactor : z ^ p - y ^ p = (z - y) * GN p (z - y) y
  hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y

/-- `PrimeGe5CounterexamplePack` + Branch B + `WieferichLift` から、縮小に使う純算術データを抽出する。 -/
theorem wieferichDescentDataB_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hLift : WieferichLift p y z q) :
    WieferichDescentDataB p x y z q := by
  rcases hLift with ⟨hqP, hq_dvd_diff, hq_not_dvd_gap, _hq2_dvd_diff⟩
  have hyz_pow : y ^ p ≤ z ^ p := by
    exact Nat.pow_le_pow_left hpack.hyz p
  have hdiff_eq : z ^ p - y ^ p = x ^ p := by
    have hcancel : z ^ p - y ^ p + y ^ p = x ^ p + y ^ p := by
      rw [Nat.sub_add_cancel hyz_pow, hpack.hEq]
    exact Nat.add_right_cancel hcancel
  have hq_dvd_xpow : q ∣ x ^ p := by
    simpa [hdiff_eq] using hq_dvd_diff
  have hq_dvd_x : q ∣ x := hqP.dvd_of_dvd_pow hq_dvd_xpow
  have hqpow_dvd_xpow : q ^ p ∣ x ^ p := by
    exact pow_dvd_pow_of_dvd hq_dvd_x p
  have hqpow_dvd_diff : q ^ p ∣ z ^ p - y ^ p := by
    simpa [hdiff_eq] using hqpow_dvd_xpow
  have hp_pos : 0 < p := hpack.hp.pos
  have hfactor : z ^ p - y ^ p = (z - y) * GN p (z - y) y := by
    simpa using pow_sub_pow_factor_cosmic_N hp_pos hpack.hyz_lt
  have hcop_q_gap : Nat.Coprime q (z - y) := by
    exact (Nat.Prime.coprime_iff_not_dvd hqP).2 hq_not_dvd_gap
  have hcop_qpow_gap : Nat.Coprime (q ^ p) (z - y) := by
    exact (Nat.coprime_pow_left_iff hp_pos q (z - y)).2 hcop_q_gap
  have hqpow_dvd_mul : q ^ p ∣ (z - y) * GN p (z - y) y := by
    simpa [hfactor] using hqpow_dvd_diff
  have hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y := by
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop_qpow_gap hqpow_dvd_mul
  exact ⟨hqP, hpB, hq_not_dvd_gap, hdiff_eq, hqpow_dvd_diff, hfactor, hqpow_dvd_GN⟩

/--
Branch B 縮小の成果物。

`z` を strictly に減らしつつ、prime-ge5 反例パックと Branch B 条件を保った次状態を表す。
-/
structure TriominoWieferichDescentResultB (p z : ℕ) where
  x' : ℕ
  y' : ℕ
  z' : ℕ
  hpack' : PrimeGe5CounterexamplePack p x' y' z'
  hpB' : ¬ p ∣ (z' - y')
  hzlt : z' < z

/--
縮小候補の証明材料。

候補数値 `(x', y', z')` について、再パック化に必要な不変量を一束にする。
-/
structure TriominoWieferichShrinkWitnessB
    (p x y z q x' y' z' : ℕ) : Prop where
  hEq' : x' ^ p + y' ^ p = z' ^ p
  hyz' : y' ≤ z'
  hyzLt : y' < z'
  hxy' : Nat.Coprime x' y'
  hx0' : x' ≠ 0
  hy0' : y' ≠ 0
  hz0' : z' ≠ 0

/--
縮小候補の「数値」と、その候補を正当化する証明材料。

最後の未解決点は、この data をどう構成するかに集約する。
-/
structure TriominoWieferichShrinkNumsB (p x y z q : ℕ) where
  x' : ℕ
  y' : ℕ
  z' : ℕ
  hzlt : z' < z
  hpB' : ¬ p ∣ (z' - y')
  hW : TriominoWieferichShrinkWitnessB p x y z q x' y' z'

/--
shrink の候補生成成果物。

ここでは「数値」だけでなく、再パック化を no-`sorry` で行うための証明材料まで保持する。
-/
structure TriominoWieferichShrinkCandB (p z : ℕ) where
  x' : ℕ
  y' : ℕ
  z' : ℕ
  hEq' : x' ^ p + y' ^ p = z' ^ p
  hyz' : y' ≤ z'
  hyzLt : y' < z'
  hxy' : Nat.Coprime x' y'
  hx0' : x' ≠ 0
  hy0' : y' ≠ 0
  hz0' : z' ≠ 0
  hpB' : ¬ p ∣ (z' - y')
  hzlt : z' < z

/-- 候補から prime-ge5 反例パックを組み直す。 -/
def TriominoWieferichShrinkCandB.toPack
    {p z : ℕ}
    (hp5 : 5 ≤ p)
    (hp : Nat.Prime p)
    (c : TriominoWieferichShrinkCandB p z) :
    PrimeGe5CounterexamplePack p c.x' c.y' c.z' :=
  { toPrimeCounterexamplePack :=
      { hp := hp
        hxy := c.hxy'
        hyz := c.hyz'
        hyz_lt := c.hyzLt
        hEq := c.hEq' }
    hp5 := hp5
    hx0 := c.hx0'
    hy0 := c.hy0'
    hz0 := c.hz0' }

/-- 候補を最終的な Branch B 縮小結果へ変換する。 -/
def TriominoWieferichShrinkCandB.toResult
    {p z : ℕ}
    (hp5 : 5 ≤ p)
    (hp : Nat.Prime p)
    (c : TriominoWieferichShrinkCandB p z) :
    TriominoWieferichDescentResultB p z :=
  { x' := c.x'
    y' := c.y'
    z' := c.z'
    hpack' := c.toPack hp5 hp
    hpB' := c.hpB'
    hzlt := c.hzlt }

/-- `Nums` から `Cand` へ戻す配線。 -/
def triominoWieferichShrinkCandB_of_nums
    {p x y z q : ℕ}
    (n : TriominoWieferichShrinkNumsB p x y z q) :
    TriominoWieferichShrinkCandB p z :=
  { x' := n.x'
    y' := n.y'
    z' := n.z'
    hEq' := n.hW.hEq'
    hyz' := n.hW.hyz'
    hyzLt := n.hW.hyzLt
    hxy' := n.hW.hxy'
    hx0' := n.hW.hx0'
    hy0' := n.hW.hy0'
    hz0' := n.hW.hz0'
    hpB' := n.hpB'
    hzlt := n.hzlt }

/--
第2層の最小核: Triomino/Cosmic 固有の縮小器 step。

純算術データから、次の反例候補を `Result` 構造体として返すだけにする。
-/
abbrev TriominoWieferichDescentStepB : Type :=
  ∀ {p x y z q : ℕ},
    PrimeGe5CounterexamplePack p x y z →
    WieferichDescentDataB p x y z q →
    TriominoWieferichDescentResultB p z

/--
第2層: Triomino/Cosmic 固有の縮小器コア。

`q^p ∣ GN` まで整備済みの純算術データから、Branch B 条件を保ったより小さい反例を返す。
-/
abbrev TriominoWieferichDescentCoreB : Prop :=
  ∀ {p x y z q : ℕ},
    PrimeGe5CounterexamplePack p x y z →
    WieferichDescentDataB p x y z q →
    ∃ x' y' z' : ℕ,
      PrimeGe5CounterexamplePack p x' y' z' ∧ ¬ p ∣ (z' - y') ∧ z' < z

/-- `step` 形式の縮小器があれば、`∃` 形式の core へ戻せる。 -/
theorem triominoWieferichDescentCoreB_of_step
    (hStep : TriominoWieferichDescentStepB) :
    TriominoWieferichDescentCoreB := by
  intro p x y z q hpack hData
  rcases hStep hpack hData with ⟨x', y', z', hpack', hpB', hzlt⟩
  exact ⟨x', y', z', hpack', hpB', hzlt⟩

/-- 純算術データ抽出と縮小器コアを合成すると、Branch B の下降仕様になる。 -/
theorem triominoWieferichDescent_impl_of_core
    (hCore : TriominoWieferichDescentCoreB) :
    WieferichDescentB := by
  intro p x y z q hpack hpB hLift
  have hData : WieferichDescentDataB p x y z q :=
    wieferichDescentDataB_of_pack hpack hpB hLift
  exact hCore hpack hData

/--
Triomino/Cosmic 固有の縮小候補データ生成（本丸）。

最後の未解決点は、この候補データ `Nums` をどう作るかに隔離する。
-/
def triominoWieferichShrinkNumsB_impl
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkNumsB p x y z q := by
  -- TODO:
  -- `q^p ∣ GN p (z - y) y` と `¬ q ∣ (z - y)` を使い、
  -- Triomino/Cosmic の縮小操作で `x' y' z'` と証明材料を構成する。
  let _u : ℕ := z - y
  let _ := hpack
  let _ := hpB
  let _ := hqP
  let _ := hq_not_dvd_gap
  let _ := hqpow_dvd_GN
  sorry

/--
Triomino/Cosmic 固有の縮小候補（配線）。
-/
def triominoWieferichShrinkCandB_impl
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkCandB p z := by
  let n : TriominoWieferichShrinkNumsB p x y z q :=
    triominoWieferichShrinkNumsB_impl
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact triominoWieferichShrinkCandB_of_nums n

/--
Triomino/Cosmic 固有の縮小器（配線）。
-/
def triominoWieferichShrinkB
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichDescentResultB p z := by
  let c : TriominoWieferichShrinkCandB p z :=
    triominoWieferichShrinkCandB_impl
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact c.toResult hpack.hp5 hpack.hp

/--
`step` 実装は、データ抽出済みの項目を縮小器へ渡すだけの glue に保つ。
-/
def triominoWieferichDescentStepB_impl : TriominoWieferichDescentStepB := by
  intro p x y z q hpack hData
  exact triominoWieferichShrinkB
    (p := p) (x := x) (y := y) (z := z) (q := q)
    hpack
    hData.hpB
    hData.hqP
    hData.hq_not_dvd_gap
    hData.hqpow_dvd_GN

/-- `step` 実装から `core` を回収する。 -/
theorem triominoWieferichDescentCoreB_impl : TriominoWieferichDescentCoreB := by
  exact triominoWieferichDescentCoreB_of_step
    triominoWieferichDescentStepB_impl

/--
Branch B の下降法本体。

このファイルだけが、一般 `GN` 降下の新規理論（縮小器）を保持する隔離室。
-/
theorem triominoWieferichDescent_impl : WieferichDescentB := by
  exact triominoWieferichDescent_impl_of_core
    triominoWieferichDescentCoreB_impl

end DkMath.FLT
