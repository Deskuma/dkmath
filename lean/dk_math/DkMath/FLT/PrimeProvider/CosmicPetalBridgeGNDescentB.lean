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

/-- witness の「等式と順序」部分。 -/
structure TriominoWieferichShrinkWitnessEqB
    (p x y z q x' y' z' : ℕ) : Prop where
  hEq' : x' ^ p + y' ^ p = z' ^ p
  hyz' : y' ≤ z'
  hyzLt : y' < z'

/-- witness の「不変量」部分（互いに素・非零）。 -/
structure TriominoWieferichShrinkWitnessInvB
    (p x y z q x' y' z' : ℕ) : Prop where
  hxy' : Nat.Coprime x' y'
  hx0' : x' ≠ 0
  hy0' : y' ≠ 0
  hz0' : z' ≠ 0

/--
縮小候補の完全 witness。

`Eq / Inv` の分割版からの回収先としても使う。
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

/-- 完全 witness から「等式と順序」部分だけを取り出す。 -/
def TriominoWieferichShrinkWitnessB.toEq
    {p x y z q x' y' z' : ℕ}
    (hW : TriominoWieferichShrinkWitnessB p x y z q x' y' z') :
    TriominoWieferichShrinkWitnessEqB p x y z q x' y' z' :=
  { hEq' := hW.hEq'
    hyz' := hW.hyz'
    hyzLt := hW.hyzLt }

/-- 完全 witness から「不変量」部分だけを取り出す。 -/
def TriominoWieferichShrinkWitnessB.toInv
    {p x y z q x' y' z' : ℕ}
    (hW : TriominoWieferichShrinkWitnessB p x y z q x' y' z') :
    TriominoWieferichShrinkWitnessInvB p x y z q x' y' z' :=
  { hxy' := hW.hxy'
    hx0' := hW.hx0'
    hy0' := hW.hy0'
    hz0' := hW.hz0' }

/-- `Eq / Inv` から従来の完全 witness を回収する。 -/
def TriominoWieferichShrinkWitnessB.ofEqInv
    {p x y z q x' y' z' : ℕ}
    (hEq : TriominoWieferichShrinkWitnessEqB p x y z q x' y' z')
    (hInv : TriominoWieferichShrinkWitnessInvB p x y z q x' y' z') :
    TriominoWieferichShrinkWitnessB p x y z q x' y' z' :=
  { hEq' := hEq.hEq'
    hyz' := hEq.hyz'
    hyzLt := hEq.hyzLt
    hxy' := hInv.hxy'
    hx0' := hInv.hx0'
    hy0' := hInv.hy0'
    hz0' := hInv.hz0' }

/--
縮小 triple に埋め込む構成の痕跡。

`XYZ` だけから `Trace` を回収できるよう、strict 減少・Branch B 維持・witness を保持する。
-/
structure TriominoWieferichShrinkCtorB
    (p x y z q x' y' z' : ℕ) : Prop where
  hzlt : z' < z
  hpB' : ¬ p ∣ (z' - y')
  hEq : TriominoWieferichShrinkWitnessEqB p x y z q x' y' z'
  hInv : TriominoWieferichShrinkWitnessInvB p x y z q x' y' z'

/-- `ctor` から従来の完全 witness を回収する。 -/
def TriominoWieferichShrinkCtorB.hW
    {p x y z q x' y' z' : ℕ}
    (c : TriominoWieferichShrinkCtorB p x y z q x' y' z') :
    TriominoWieferichShrinkWitnessB p x y z q x' y' z' :=
  TriominoWieferichShrinkWitnessB.ofEqInv c.hEq c.hInv

/-- まずは縮小候補の数値 triple だけを与える層。 -/
structure TriominoWieferichShrinkXYZB (p x y z q : ℕ) where
  x' : ℕ
  y' : ℕ
  z' : ℕ
  ctor : TriominoWieferichShrinkCtorB p x y z q x' y' z'

/-- 生成した triple に対する縮小の証明材料。 -/
structure TriominoWieferichShrinkCertB
    (p x y z q : ℕ)
    (t : TriominoWieferichShrinkXYZB p x y z q) : Prop where
  hzlt : t.z' < z
  hpB' : ¬ p ∣ (t.z' - t.y')
  hW : TriominoWieferichShrinkWitnessB p x y z q t.x' t.y' t.z'

/-- `XYZ` から `Cert` を回収するための縮小 trace。 -/
structure TriominoWieferichShrinkTraceB
    (p x y z q : ℕ)
    (t : TriominoWieferichShrinkXYZB p x y z q) : Prop where
  hzlt : t.z' < z
  hpB' : ¬ p ∣ (t.z' - t.y')
  hW : TriominoWieferichShrinkWitnessB p x y z q t.x' t.y' t.z'

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

/-- `XYZ` と `Cert` を 1 束にした shrink 候補生成の核。 -/
structure TriominoWieferichShrinkXYZCertB (p x y z q : ℕ) where
  t : TriominoWieferichShrinkXYZB p x y z q
  hc : TriominoWieferichShrinkCertB p x y z q t

/-- trace を `XYZ + Cert` 束へ再梱包する。 -/
def triominoWieferichShrinkXYZCertB_of_trace
    {p x y z q : ℕ}
    (t : TriominoWieferichShrinkXYZB p x y z q)
    (htr : TriominoWieferichShrinkTraceB p x y z q t) :
    TriominoWieferichShrinkXYZCertB p x y z q :=
  { t := t
    hc :=
      { hzlt := htr.hzlt
        hpB' := htr.hpB'
        hW := htr.hW } }

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

/-- `XYZ` と `Cert` から `Nums` へ戻す glue。 -/
def triominoWieferichShrinkNumsB_of_XYZ_Cert
    {p x y z q : ℕ}
    (t : TriominoWieferichShrinkXYZB p x y z q)
    (hc : TriominoWieferichShrinkCertB p x y z q t) :
    TriominoWieferichShrinkNumsB p x y z q :=
  { x' := t.x'
    y' := t.y'
    z' := t.z'
    hzlt := hc.hzlt
    hpB' := hc.hpB'
    hW := hc.hW }

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
`XYZ` 候補へ束ねる直前の内部データ。

唯一の未解決点は、この data をどう生成するかに押し込める。
-/
structure TriominoWieferichShrinkKernelDataB (p x y z q : ℕ) where
  x' : ℕ
  y' : ℕ
  z' : ℕ
  hzlt : z' < z
  hpB' : ¬ p ∣ (z' - y')
  hEq : TriominoWieferichShrinkWitnessEqB p x y z q x' y' z'
  hInv : TriominoWieferichShrinkWitnessInvB p x y z q x' y' z'

/--
数値生成＋strict 減少＋Branch B 維持の切断面。

最終的に `Eq / Inv` をこの上へ接ぐための最小核。
-/
structure TriominoWieferichShrinkKernelNumsB (p x y z q : ℕ) where
  x' : ℕ
  y' : ℕ
  z' : ℕ
  hzlt : z' < z
  hpB' : ¬ p ∣ (z' - y')

/--
`Nums` と、その上に乗る `Eq / Inv` witness を束ねた内部 seed。

本丸の縮小変換は、この seed を 1 回構成できれば足りる。
-/
structure TriominoWieferichShrinkKernelSeedB (p x y z q : ℕ) where
  n : TriominoWieferichShrinkKernelNumsB p x y z q
  hEq : TriominoWieferichShrinkWitnessEqB p x y z q n.x' n.y' n.z'

/--
`KernelSeedB` の上に `Inv` witness を載せた内部 core 束。

`hInv` を seed から切り離し、必要な箇所だけで回収できるようにする。
-/
structure TriominoWieferichShrinkKernelCoreB (p x y z q : ℕ) where
  s : TriominoWieferichShrinkKernelSeedB p x y z q
  hInv : TriominoWieferichShrinkWitnessInvB p x y z q s.n.x' s.n.y' s.n.z'

/-- 内部 data から `Nums` 部分を取り出す。 -/
def TriominoWieferichShrinkKernelDataB.toNums
    {p x y z q : ℕ}
    (d : TriominoWieferichShrinkKernelDataB p x y z q) :
    TriominoWieferichShrinkKernelNumsB p x y z q :=
  { x' := d.x'
    y' := d.y'
    z' := d.z'
    hzlt := d.hzlt
    hpB' := d.hpB' }

/-- 内部 seed と `Inv` witness から `KernelData` へ戻す。 -/
def TriominoWieferichShrinkKernelSeedB.toData
    {p x y z q : ℕ}
    (s : TriominoWieferichShrinkKernelSeedB p x y z q)
    (hInv : TriominoWieferichShrinkWitnessInvB p x y z q s.n.x' s.n.y' s.n.z') :
    TriominoWieferichShrinkKernelDataB p x y z q :=
  { x' := s.n.x'
    y' := s.n.y'
    z' := s.n.z'
    hzlt := s.n.hzlt
    hpB' := s.n.hpB'
    hEq := s.hEq
    hInv := hInv }

/-- 内部 core 束から `KernelSeed` を取り出す。 -/
def TriominoWieferichShrinkKernelCoreB.toSeed
    {p x y z q : ℕ}
    (c : TriominoWieferichShrinkKernelCoreB p x y z q) :
    TriominoWieferichShrinkKernelSeedB p x y z q :=
  c.s

/-- 内部 core 束から `KernelData` へ戻す。 -/
def TriominoWieferichShrinkKernelCoreB.toData
    {p x y z q : ℕ}
    (c : TriominoWieferichShrinkKernelCoreB p x y z q) :
    TriominoWieferichShrinkKernelDataB p x y z q :=
  c.s.toData c.hInv

/-- seed から `Inv` を回収するための最小 trace。 -/
structure TriominoWieferichShrinkKernelInvTraceB
    (p x y z q : ℕ)
    (s : TriominoWieferichShrinkKernelSeedB p x y z q) where
  hInv : TriominoWieferichShrinkWitnessInvB p x y z q s.n.x' s.n.y' s.n.z'

/--
Triomino/Cosmic 固有の等式側 trace 生成 pack（本丸）。

最後の未解決点は、この eq-side pack をどう作るかに隔離する。
-/
def triominoWieferichShrinkKernelEqSeedTracePackB_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelCoreB p x y z q := by
  -- TODO:
  -- `q^p ∣ GN p (z - y) y` と `¬ q ∣ (z - y)` を使い、
  -- Triomino/Cosmic の縮小操作で seed（`Nums + Eq`）と `Inv` witness を構成する。
  let _u : ℕ := z - y
  let _ := hpack
  let _ := hpB
  let _ := hqP
  let _ := hq_not_dvd_gap
  let _ := hqpow_dvd_GN
  sorry

/--
canonical eq-side trace pack から `Nums` 部分だけを回収する。

eq-side trace の「数値生成」投影版。
-/
def triominoWieferichShrinkKernelNums_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelNumsB p x y z q :=
  (triominoWieferichShrinkKernelEqSeedTracePackB_kernel
    (p := p) (x := x) (y := y) (z := z) (q := q)
    hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).s.n

/-- canonical eq-side trace pack から `Eq` witness を回収する投影版。 -/
theorem triominoWieferichShrinkKernelEq_of_nums_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkWitnessEqB
      p x y z q
      (triominoWieferichShrinkKernelNums_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkKernelNums_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      (triominoWieferichShrinkKernelNums_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  let c : TriominoWieferichShrinkKernelCoreB p x y z q :=
    triominoWieferichShrinkKernelEqSeedTracePackB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa [triominoWieferichShrinkKernelNums_of_pack, c] using c.s.hEq

/-- canonical eq-side trace pack から `Inv` witness を回収する投影版。 -/
theorem triominoWieferichShrinkKernelInv_of_nums_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkWitnessInvB
      p x y z q
      (triominoWieferichShrinkKernelNums_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkKernelNums_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      (triominoWieferichShrinkKernelNums_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  let c : TriominoWieferichShrinkKernelCoreB p x y z q :=
    triominoWieferichShrinkKernelEqSeedTracePackB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa [triominoWieferichShrinkKernelNums_of_pack, c] using c.hInv

/--
独立実装へ差し替えるための最小核。

`Nums` と `Inv` を同一ソースから供給し、後段の差し替えで数値のズレを防ぐ。
-/
structure TriominoWieferichShrinkNumsInvCoreB (p x y z q : ℕ) where
  n : TriominoWieferichShrinkKernelNumsB p x y z q
  hInv : TriominoWieferichShrinkWitnessInvB p x y z q n.x' n.y' n.z'

/--
独立実装の「生成結果」だけを持つレシピ。

まずはここに縮小ロジックを閉じ込め、`NumsInvCoreB` 側は梱包だけに保つ。
-/
structure TriominoWieferichShrinkNumsInvRecipeB (p x y z q : ℕ) where
  x' : ℕ
  y' : ℕ
  z' : ℕ
  hzlt : z' < z
  hpB' : ¬ p ∣ (z' - y')
  hInv : TriominoWieferichShrinkWitnessInvB p x y z q x' y' z'

/-- `Nums + Inv` 独立実装で先に決める数値候補。 -/
structure TriominoWieferichShrinkNumsInvCandidateB (p x y z q : ℕ) where
  x' : ℕ
  y' : ℕ
  z' : ℕ

/-- `Candidate` に要求する `Nums + Inv` 側の仕様。 -/
structure TriominoWieferichShrinkNumsInvCandidateSpecB
    (p x y z q : ℕ)
    (c : TriominoWieferichShrinkNumsInvCandidateB p x y z q) : Prop where
  hzlt : c.z' < z
  hpB' : ¬ p ∣ (c.z' - c.y')
  hInv : TriominoWieferichShrinkWitnessInvB p x y z q c.x' c.y' c.z'

/-- `Candidate + Spec` から `Recipe` を復元する。 -/
def TriominoWieferichShrinkNumsInvRecipeB.ofCandidateSpec
    {p x y z q : ℕ}
    (c : TriominoWieferichShrinkNumsInvCandidateB p x y z q)
    (hs : TriominoWieferichShrinkNumsInvCandidateSpecB p x y z q c) :
    TriominoWieferichShrinkNumsInvRecipeB p x y z q :=
  { x' := c.x'
    y' := c.y'
    z' := c.z'
    hzlt := hs.hzlt
    hpB' := hs.hpB'
    hInv := hs.hInv }

/-- `Recipe` から `KernelNums` を梱包する。 -/
def TriominoWieferichShrinkNumsInvRecipeB.toNums
    {p x y z q : ℕ}
    (r : TriominoWieferichShrinkNumsInvRecipeB p x y z q) :
    TriominoWieferichShrinkKernelNumsB p x y z q :=
  { x' := r.x'
    y' := r.y'
    z' := r.z'
    hzlt := r.hzlt
    hpB' := r.hpB' }

/-- `Recipe` から `NumsInvCore` を梱包する。 -/
def TriominoWieferichShrinkNumsInvRecipeB.toCore
    {p x y z q : ℕ}
    (r : TriominoWieferichShrinkNumsInvRecipeB p x y z q) :
    TriominoWieferichShrinkNumsInvCoreB p x y z q := by
  refine { n := r.toNums, hInv := ?_ }
  simpa [TriominoWieferichShrinkNumsInvRecipeB.toNums] using r.hInv

/--
独立実装へ差し替えるための `Nums + Inv` レシピ kernel。

現時点では `_of_pack` 投影版の結果を並べ直すだけに留める。
-/
def triominoWieferichShrinkNumsInvRecipe_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkNumsInvRecipeB p x y z q := by
  let n : TriominoWieferichShrinkKernelNumsB p x y z q :=
    triominoWieferichShrinkKernelNums_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hInv :
      TriominoWieferichShrinkWitnessInvB p x y z q n.x' n.y' n.z' := by
    simpa [n] using
      triominoWieferichShrinkKernelInv_of_nums_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact
    { x' := n.x'
      y' := n.y'
      z' := n.z'
      hzlt := n.hzlt
      hpB' := n.hpB'
      hInv := hInv }

/-- `_of_pack` backend から数値候補だけを取り出す。 -/
def triominoWieferichShrinkNumsInvCandidate_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkNumsInvCandidateB p x y z q := by
  let r0 : TriominoWieferichShrinkNumsInvRecipeB p x y z q :=
    triominoWieferichShrinkNumsInvRecipe_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact
    { x' := r0.x'
      y' := r0.y'
      z' := r0.z' }

/--
独立実装へ差し替えるための数値候補 kernel。

現時点では計算可能性を保つため、
`triominoWieferichShrinkNumsInvCandidate_of_pack` への委譲に留める。
-/
def triominoWieferichShrinkNumsInvCandidateB_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
  triominoWieferichShrinkNumsInvCandidate_of_pack
    (p := p) (x := x) (y := y) (z := z) (q := q)
    hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `CandidateB_kernel` 用に `Eq` を先行回収する pack 依存 helper。 -/
theorem triominoWieferichShrinkNumsInvCandidateEq_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkWitnessEqB
      p x y z q
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let r0 : TriominoWieferichShrinkNumsInvRecipeB p x y z q :=
    triominoWieferichShrinkNumsInvRecipe_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let n : TriominoWieferichShrinkKernelNumsB p x y z q :=
    triominoWieferichShrinkKernelNums_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa
      [c, triominoWieferichShrinkNumsInvCandidateB_kernel,
        triominoWieferichShrinkNumsInvCandidate_of_pack,
        r0, triominoWieferichShrinkNumsInvRecipe_of_pack, n] using
    triominoWieferichShrinkKernelEq_of_nums_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `CandidateB_kernel` 用に `hEq'` を先行回収する pack 依存 helper。 -/
theorem triominoWieferichShrinkNumsInvCandidate_hEq_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' ^ p
      +
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' ^ p
      =
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' ^ p := by
  exact
    (triominoWieferichShrinkNumsInvCandidateEq_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).hEq'

/-- `CandidateB_kernel` 用に `hyz'` を先行回収する pack 依存 helper。 -/
theorem triominoWieferichShrinkNumsInvCandidate_hyz_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      ≤
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  exact
    (triominoWieferichShrinkNumsInvCandidateEq_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).hyz'

/-- `CandidateB_kernel` 用に `hyzLt` を先行回収する pack 依存 helper。 -/
theorem triominoWieferichShrinkNumsInvCandidate_hyzLt_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      <
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  exact
    (triominoWieferichShrinkNumsInvCandidateEq_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).hyzLt

/-- `CandidateB_kernel` 用に `Eq` を回収する公開 core helper。 -/
theorem triominoWieferichShrinkNumsInvCandidateEqCore_of_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkWitnessEqB
      p x y z q
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hEq' : c.x' ^ p + c.y' ^ p = c.z' ^ p := by
    simpa [c] using
      triominoWieferichShrinkNumsInvCandidate_hEq_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hyz' : c.y' ≤ c.z' := by
    simpa [c] using
      triominoWieferichShrinkNumsInvCandidate_hyz_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hyzLt : c.y' < c.z' := by
    simpa [c] using
      triominoWieferichShrinkNumsInvCandidate_hyzLt_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact { hEq' := hEq', hyz' := hyz', hyzLt := hyzLt }

/-- `CandidateB_kernel` 用に `hEq'` を回収する公開 core helper。 -/
theorem triominoWieferichShrinkNumsInvCandidate_hEq_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' ^ p
      +
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' ^ p
      =
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' ^ p := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa [c] using
    (triominoWieferichShrinkNumsInvCandidateEqCore_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).hEq'

/-- `CandidateB_kernel` 用に `hyz'` を回収する公開 core helper。 -/
theorem triominoWieferichShrinkNumsInvCandidate_hyz_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      ≤
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa [c] using
    (triominoWieferichShrinkNumsInvCandidateEqCore_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).hyz'

/-- `CandidateB_kernel` 用に `hyzLt` を回収する公開 core helper。 -/
theorem triominoWieferichShrinkNumsInvCandidate_hyzLt_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      <
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa [c] using
    (triominoWieferichShrinkNumsInvCandidateEqCore_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).hyzLt

/--
`q^p ∣ GN p (z - y) y` から、`q ∣ x` を回収する。

後で独立 shrink の `Inv` を組む際の前処理として使う。
-/
theorem triominoWieferichShrink_q_dvd_x
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    q ∣ x := by
  let _ := hpB
  let _ := hq_not_dvd_gap
  have hp_pos : 0 < p := hpack.hp.pos
  have hq_dvd_qpow : q ∣ q ^ p := by
    simpa using (pow_dvd_pow q (Nat.succ_le_of_lt hp_pos) : q ^ 1 ∣ q ^ p)
  have hq_dvd_GN : q ∣ GN p (z - y) y := by
    exact dvd_trans hq_dvd_qpow hqpow_dvd_GN
  have hxpow : x ^ p = (z - y) * GN p (z - y) y := by
    simpa [PrimeGe5CounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN
  have hq_dvd_xpow : q ∣ x ^ p := by
    have hq_dvd_rhs : q ∣ (z - y) * GN p (z - y) y := by
      exact dvd_mul_of_dvd_right hq_dvd_GN (z - y)
    simpa [hxpow] using hq_dvd_rhs
  exact hqP.dvd_of_dvd_pow hq_dvd_xpow

/--
`q ∣ x` と元の互いに素条件から、`q ∤ y` を回収する。

後で独立 shrink の `Inv` を組む際の前処理として使う。
-/
theorem triominoWieferichShrink_q_not_dvd_y
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    ¬ q ∣ y := by
  intro hq_dvd_y
  have hq_dvd_x : q ∣ x :=
    triominoWieferichShrink_q_dvd_x
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hnot : ¬ Nat.Coprime x y :=
    Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt hqP) hq_dvd_x hq_dvd_y
  exact hnot hpack.hxy

/--
`hpB' : ¬ p ∣ (z' - y')` から、`z' ≠ 0` を回収する。

`Nat` では `0 - y' = 0` なので、`z' = 0` はただちに `p ∣ (z' - y')` を与える。
-/
theorem triominoWieferichShrink_hz0_of_hpB'
    {p y' z' : ℕ}
    (hpB' : ¬ p ∣ (z' - y')) :
    z' ≠ 0 := by
  intro hz0
  have hdiv : p ∣ (z' - y') := by
    simp [hz0]
  exact hpB' hdiv

/-- `z' - y' = z - y` が分かれば、元の Branch B 条件を移送できる。 -/
theorem triominoWieferichShrink_hpB'_of_eq_gap
    {p y z y' z' : ℕ}
    (hpB : ¬ p ∣ (z - y))
    (hgap : z' - y' = z - y) :
    ¬ p ∣ (z' - y') := by
  intro hpB'
  apply hpB
  simpa [hgap] using hpB'

/-- `z' = z / q` が分かれば、`Nat.div_lt_self` で strict 減少を回収できる。 -/
theorem triominoWieferichShrink_hzlt_of_eq_div
    {z q z' : ℕ}
    (hz0 : z ≠ 0)
    (hqP : Nat.Prime q)
    (hz' : z' = z / q) :
    z' < z := by
  have hz_pos : 0 < z := Nat.pos_of_ne_zero hz0
  have hq_gt1 : 1 < q := Nat.Prime.one_lt hqP
  calc
    z' = z / q := hz'
    _ < z := Nat.div_lt_self hz_pos hq_gt1

/-- `y' = y` が分かれば、元の反例パックから `y' ≠ 0` を回収できる。 -/
theorem triominoWieferichShrink_hy0_of_eq_y
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    {y' : ℕ}
    (hy' : y' = y) :
    y' ≠ 0 := by
  simpa [hy'] using hpack.hy0

/--
公開 `CandidateB_kernel` の `y' = y` が示せれば、`hy0'` を回収できる。

独立候補で `y' := y` を採る時の最短ルートとして使う。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hy0_of_eq_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y)
    (hy' :
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = y) :
    (triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' ≠ 0 := by
  let _ := hpB
  let _ := hqP
  let _ := hq_not_dvd_gap
  let _ := hqpow_dvd_GN
  exact
    triominoWieferichShrink_hy0_of_eq_y
      (p := p) (x := x) (y := y) (z := z) hpack hy'

/--
公開 `CandidateB_kernel` に対して `z' - y' = z - y` が示せれば、
`hpB'` を回収できる。

独立候補で gap を保つ時の最短ルートとして使う。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hpB'_of_eq_gap_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y)
    (hgap :
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' -
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' =
      z - y) :
    ¬ p ∣
      ((triominoWieferichShrinkNumsInvCandidateB_kernel
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' -
        (triominoWieferichShrinkNumsInvCandidateB_kernel
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y') := by
  let _ := hpack
  let _ := hqP
  let _ := hq_not_dvd_gap
  let _ := hqpow_dvd_GN
  exact triominoWieferichShrink_hpB'_of_eq_gap hpB hgap

/--
公開 `CandidateB_kernel` に対して `z' = z / q` が示せれば、
strict 減少 `z' < z` を回収できる。

独立候補で `z' := z / q` を採る時の最短ルートとして使う。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hzlt_of_eq_div_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y)
    (hz' :
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' =
      z / q) :
    (triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' < z := by
  let _ := hpB
  let _ := hq_not_dvd_gap
  let _ := hqpow_dvd_GN
  exact
    triominoWieferichShrink_hzlt_of_eq_div
      (z := z) (q := q)
      hpack.hz0 hqP hz'

/-- `Spec_of_kernel` 用に `hzlt` を先行回収する pack 依存 helper。 -/
theorem triominoWieferichShrinkNumsInvCandidate_hzlt_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' < z := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let r0 : TriominoWieferichShrinkNumsInvRecipeB p x y z q :=
    triominoWieferichShrinkNumsInvRecipe_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa
    [c, triominoWieferichShrinkNumsInvCandidateB_kernel,
      triominoWieferichShrinkNumsInvCandidate_of_pack, r0] using r0.hzlt

/--
`Spec_of_kernel` 用に `hzlt` を回収する公開 core helper。

現時点では pack 依存版への委譲に留め、次段の独立化ではここだけ差し替える。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hzlt_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' < z := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa [c] using
    triominoWieferichShrinkNumsInvCandidate_hzlt_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `Spec_of_kernel` 用に `hpB'` を先行回収する pack 依存 helper。 -/
theorem triominoWieferichShrinkNumsInvCandidate_hpB'_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    ¬ p ∣
      ((triominoWieferichShrinkNumsInvCandidateB_kernel
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' -
        (triominoWieferichShrinkNumsInvCandidateB_kernel
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y') := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let r0 : TriominoWieferichShrinkNumsInvRecipeB p x y z q :=
    triominoWieferichShrinkNumsInvRecipe_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa
    [c, triominoWieferichShrinkNumsInvCandidateB_kernel,
      triominoWieferichShrinkNumsInvCandidate_of_pack, r0] using r0.hpB'

/--
`Spec_of_kernel` 用に `hpB'` を回収する公開 core helper。

現時点では pack 依存版への委譲に留め、次段の独立化ではここだけ差し替える。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hpB'_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    ¬ p ∣
      ((triominoWieferichShrinkNumsInvCandidateB_kernel
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' -
        (triominoWieferichShrinkNumsInvCandidateB_kernel
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y') := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa [c] using
    triominoWieferichShrinkNumsInvCandidate_hpB'_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `Spec_of_kernel` 用に `hxy'` を先行回収する pack 依存 helper。 -/
theorem triominoWieferichShrinkNumsInvCandidate_hxy_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    Nat.Coprime
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let r0 : TriominoWieferichShrinkNumsInvRecipeB p x y z q :=
    triominoWieferichShrinkNumsInvRecipe_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa
    [c, triominoWieferichShrinkNumsInvCandidateB_kernel,
      triominoWieferichShrinkNumsInvCandidate_of_pack, r0] using r0.hInv.hxy'

/-- `x = q * x'` が分かれば、`x ≠ 0` から `x' ≠ 0` を回収できる。 -/
theorem triominoWieferichShrink_hx0_of_eq_mul_right
    {x q x' : ℕ}
    (hx0 : x ≠ 0)
    (hx' : x = q * x') :
    x' ≠ 0 := by
  intro hx'0
  apply hx0
  calc
    x = q * x' := hx'
    _ = 0 := by simp [hx'0]

/--
`x = q * x'` と `y' = y` が分かれば、
元の互いに素条件から `Nat.Coprime x' y'` を回収できる。
-/
theorem triominoWieferichShrink_hxy_of_eq_mul_eq_y
    {x y q x' y' : ℕ}
    (hxy : Nat.Coprime x y)
    (hx' : x = q * x')
    (hy' : y' = y) :
    Nat.Coprime x' y' := by
  refine (Nat.coprime_iff_gcd_eq_one).2 ?_
  by_contra hg1
  have hg_ne1 : Nat.gcd x' y' ≠ 1 := by
    simpa using hg1
  rcases Nat.exists_prime_and_dvd (n := Nat.gcd x' y') hg_ne1 with ⟨d, hdP, hd_dvd_g⟩
  have hd_dvd_x' : d ∣ x' := dvd_trans hd_dvd_g (Nat.gcd_dvd_left x' y')
  have hd_dvd_y' : d ∣ y' := dvd_trans hd_dvd_g (Nat.gcd_dvd_right x' y')
  have hd_dvd_x : d ∣ x := by
    have hd_dvd_rhs : d ∣ q * x' := dvd_mul_of_dvd_right hd_dvd_x' q
    simpa [hx'] using hd_dvd_rhs
  have hd_dvd_y : d ∣ y := by
    simpa [hy'] using hd_dvd_y'
  have hnot : ¬ Nat.Coprime x y :=
    Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt hdP) hd_dvd_x hd_dvd_y
  exact hnot hxy

/--
公開 `CandidateB_kernel` に対して `x = q * x'` が示せれば、`hx0'` を回収できる。

独立候補で `x = q * x'` を確保する時の最短ルートとして使う。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hx0_of_eq_mul_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y)
    (hx' :
      x =
        q *
          (triominoWieferichShrinkNumsInvCandidateB_kernel
            (p := p) (x := x) (y := y) (z := z) (q := q)
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x') :
    (triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' ≠ 0 := by
  let _ := hpB
  let _ := hqP
  let _ := hq_not_dvd_gap
  let _ := hqpow_dvd_GN
  exact triominoWieferichShrink_hx0_of_eq_mul_right hpack.hx0 hx'

/--
公開 `CandidateB_kernel` に対して `x = q * x'` と `y' = y` が示せれば、
`Nat.Coprime x' y'` を回収できる。

独立候補で `x = q * x'` と `y' = y` を採る時の最短ルートとして使う。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hxy_of_eq_mul_eq_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y)
    (hx' :
      x =
        q *
          (triominoWieferichShrinkNumsInvCandidateB_kernel
            (p := p) (x := x) (y := y) (z := z) (q := q)
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x')
    (hy' :
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = y) :
    Nat.Coprime
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' := by
  let _ := hpB
  let _ := hqP
  let _ := hq_not_dvd_gap
  let _ := hqpow_dvd_GN
  exact triominoWieferichShrink_hxy_of_eq_mul_eq_y hpack.hxy hx' hy'

/--
公開 `CandidateB_kernel` に対して `x' = x / q` が示せれば、`hx0'` を回収できる。

`q ∣ x` は既に前処理補題から得られるので、
独立候補で `x' := x / q` を採る時の最短ルートとして使う。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hx0_of_div_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y)
    (hxdiv :
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' = x / q) :
    (triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' ≠ 0 := by
  have hxq : q ∣ x :=
    triominoWieferichShrink_q_dvd_x
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hxmul :
      x =
        q *
          (triominoWieferichShrinkNumsInvCandidateB_kernel
            (p := p) (x := x) (y := y) (z := z) (q := q)
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' := by
    calc
      x = q * (x / q) := by
        simpa using (Nat.mul_div_cancel' hxq).symm
      _ =
          q *
            (triominoWieferichShrinkNumsInvCandidateB_kernel
              (p := p) (x := x) (y := y) (z := z) (q := q)
              hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' := by
        simp [hxdiv]
  exact
    triominoWieferichShrinkNumsInvCandidate_hx0_of_eq_mul_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN hxmul

/--
公開 `CandidateB_kernel` に対して `x' = x / q` と `y' = y` が示せれば、
`Nat.Coprime x' y'` を回収できる。

独立候補で `x' := x / q`, `y' := y` を採る時の最短ルートとして使う。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hxy_of_div_eq_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y)
    (hxdiv :
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' = x / q)
    (hy' :
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = y) :
    Nat.Coprime
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' := by
  have hxq : q ∣ x :=
    triominoWieferichShrink_q_dvd_x
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hxmul :
      x =
        q *
          (triominoWieferichShrinkNumsInvCandidateB_kernel
            (p := p) (x := x) (y := y) (z := z) (q := q)
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' := by
    calc
      x = q * (x / q) := by
        simpa using (Nat.mul_div_cancel' hxq).symm
      _ =
          q *
            (triominoWieferichShrinkNumsInvCandidateB_kernel
              (p := p) (x := x) (y := y) (z := z) (q := q)
              hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' := by
        simp [hxdiv]
  exact
    triominoWieferichShrinkNumsInvCandidate_hxy_of_eq_mul_eq_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN hxmul hy'

/--
`Spec_of_kernel` 用に `hxy'` を回収する公開 core helper。

現時点では pack 依存版への委譲に留め、次段の独立化ではここだけ差し替える。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hxy_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    Nat.Coprime
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa [c] using
    triominoWieferichShrinkNumsInvCandidate_hxy_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `Spec_of_kernel` 用に `hx0'` を先行回収する pack 依存 helper。 -/
theorem triominoWieferichShrinkNumsInvCandidate_hx0_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' ≠ 0 := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let r0 : TriominoWieferichShrinkNumsInvRecipeB p x y z q :=
    triominoWieferichShrinkNumsInvRecipe_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa
    [c, triominoWieferichShrinkNumsInvCandidateB_kernel,
      triominoWieferichShrinkNumsInvCandidate_of_pack, r0] using r0.hInv.hx0'

/--
`Spec_of_kernel` 用に `hx0'` を回収する公開 core helper。

現時点では pack 依存版への委譲に留め、次段の独立化ではここだけ差し替える。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hx0_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' ≠ 0 := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa [c] using
    triominoWieferichShrinkNumsInvCandidate_hx0_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `Spec_of_kernel` 用に `hy0'` を先行回収する pack 依存 helper。 -/
theorem triominoWieferichShrinkNumsInvCandidate_hy0_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' ≠ 0 := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let r0 : TriominoWieferichShrinkNumsInvRecipeB p x y z q :=
    triominoWieferichShrinkNumsInvRecipe_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa
    [c, triominoWieferichShrinkNumsInvCandidateB_kernel,
      triominoWieferichShrinkNumsInvCandidate_of_pack, r0] using r0.hInv.hy0'

/--
`Spec_of_kernel` 用に `hy0'` を回収する公開 core helper。

現時点では pack 依存版への委譲に留め、次段の独立化ではここだけ差し替える。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hy0_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' ≠ 0 := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa [c] using
    triominoWieferichShrinkNumsInvCandidate_hy0_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `Spec_of_kernel` 用の `Inv` 構成 core helper。 -/
theorem triominoWieferichShrinkNumsInvCandidateInvCore_of_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y)
    (hpB' :
      ¬ p ∣
        ((triominoWieferichShrinkNumsInvCandidateB_kernel
            (p := p) (x := x) (y := y) (z := z) (q := q)
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' -
          (triominoWieferichShrinkNumsInvCandidateB_kernel
            (p := p) (x := x) (y := y) (z := z) (q := q)
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y')) :
    TriominoWieferichShrinkWitnessInvB
      p x y z q
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hpB'' : ¬ p ∣ (c.z' - c.y') := by
    simpa [c] using hpB'
  have hInv : TriominoWieferichShrinkWitnessInvB p x y z q c.x' c.y' c.z' := by
    refine
      { hxy' := ?_
        hx0' := ?_
        hy0' := ?_
        hz0' := ?_ }
    · simpa [c] using
        triominoWieferichShrinkNumsInvCandidate_hxy_core
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
    · simpa [c] using
        triominoWieferichShrinkNumsInvCandidate_hx0_core
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
    · simpa [c] using
        triominoWieferichShrinkNumsInvCandidate_hy0_core
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
    · exact
        triominoWieferichShrink_hz0_of_hpB'
          (p := p) (y' := c.y') (z' := c.z') hpB''
  simpa [c] using hInv

/--
公開 `CandidateB_kernel` が満たす `Nums + Inv` 仕様。

現時点では `_of_pack` backend から回収するが、
独立 shrink 実装への差し替え点はこの定理 1 本に集約する。
-/
theorem triominoWieferichShrinkNumsInvCandidateSpec_of_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkNumsInvCandidateSpecB
      p x y z q
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN) := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hzlt : c.z' < z := by
    simpa [c] using
      triominoWieferichShrinkNumsInvCandidate_hzlt_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hpB' : ¬ p ∣ (c.z' - c.y') := by
    simpa [c] using
      triominoWieferichShrinkNumsInvCandidate_hpB'_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hInv : TriominoWieferichShrinkWitnessInvB p x y z q c.x' c.y' c.z' := by
    simpa [c] using
      triominoWieferichShrinkNumsInvCandidateInvCore_of_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN hpB'
  exact { hzlt := hzlt, hpB' := hpB', hInv := hInv }

/--
独立 shrink による数値候補の存在。

存在証明自体は `CandidateB_kernel` とその `Spec` を束ねる薄皮に保つ。
-/
theorem triominoWieferichShrinkNumsInvCandidate_exists
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    ∃ c : TriominoWieferichShrinkNumsInvCandidateB p x y z q,
      TriominoWieferichShrinkNumsInvCandidateSpecB p x y z q c := by
  refine
    ⟨triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN, ?_⟩
  exact
    triominoWieferichShrinkNumsInvCandidateSpec_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- 現在の数値候補に対する `hzlt` の回収 helper。 -/
theorem triominoWieferichShrinkNumsInvCandidate_hzlt
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' < z := by
  exact
    (triominoWieferichShrinkNumsInvCandidateSpec_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).hzlt

/-- 現在の数値候補に対する `hpB'` の回収 helper。 -/
theorem triominoWieferichShrinkNumsInvCandidate_hpB'
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    ¬ p ∣
      ((triominoWieferichShrinkNumsInvCandidateB_kernel
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' -
        (triominoWieferichShrinkNumsInvCandidateB_kernel
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y') := by
  exact
    (triominoWieferichShrinkNumsInvCandidateSpec_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).hpB'

/-- 現在の数値候補に対する `Inv` の回収 helper。 -/
theorem triominoWieferichShrinkNumsInvCandidate_hInv
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkWitnessInvB
      p x y z q
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      (triominoWieferichShrinkNumsInvCandidateB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  exact
    (triominoWieferichShrinkNumsInvCandidateSpec_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).hInv

/--
独立実装へ差し替えるための `Nums + Inv` レシピ kernel。

現時点では `CandidateB_kernel + Spec_of_kernel` の包装に留め、
公開側の束ねはこの 2 点だけを見るように保つ。
-/
def triominoWieferichShrinkNumsInvRecipeB_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkNumsInvRecipeB p x y z q := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let hs : TriominoWieferichShrinkNumsInvCandidateSpecB p x y z q c :=
    triominoWieferichShrinkNumsInvCandidateSpec_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact TriominoWieferichShrinkNumsInvRecipeB.ofCandidateSpec c hs

/--
独立実装へ差し替えるための `Nums + Inv` kernel 枠。

現時点では `Recipe` を `NumsInvCoreB` へ梱包するだけに留める。
-/
def triominoWieferichShrinkNumsInvCoreB_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkNumsInvCoreB p x y z q :=
  (triominoWieferichShrinkNumsInvRecipeB_kernel
    (p := p) (x := x) (y := y) (z := z) (q := q)
    hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).toCore

/--
独立実装へ差し替えるための `Nums` kernel 枠。

現時点では `_of_pack` 投影版への委譲に留める。
-/
def triominoWieferichShrinkKernelNumsCoreB_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelNumsB p x y z q :=
  (triominoWieferichShrinkNumsInvCoreB_kernel
    (p := p) (x := x) (y := y) (z := z) (q := q)
    hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).n

/--
独立実装へ差し替えるための `Eq` kernel 枠。

現時点では `_of_pack` 投影版への委譲に留める。
-/
theorem triominoWieferichShrinkKernelEq_of_nums_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkWitnessEqB
      p x y z q
      (triominoWieferichShrinkKernelNumsCoreB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkKernelNumsCoreB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      (triominoWieferichShrinkKernelNumsCoreB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hEq' : c.x' ^ p + c.y' ^ p = c.z' ^ p := by
    simpa [c] using
      triominoWieferichShrinkNumsInvCandidate_hEq_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hyz' : c.y' ≤ c.z' := by
    simpa [c] using
      triominoWieferichShrinkNumsInvCandidate_hyz_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hyzLt : c.y' < c.z' := by
    simpa [c] using
      triominoWieferichShrinkNumsInvCandidate_hyzLt_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hEq :
      TriominoWieferichShrinkWitnessEqB p x y z q c.x' c.y' c.z' := by
    exact { hEq' := hEq', hyz' := hyz', hyzLt := hyzLt }
  simpa
      [triominoWieferichShrinkKernelNumsCoreB_kernel,
        triominoWieferichShrinkNumsInvCoreB_kernel,
        TriominoWieferichShrinkNumsInvRecipeB.toCore,
        TriominoWieferichShrinkNumsInvRecipeB.toNums,
        triominoWieferichShrinkNumsInvRecipeB_kernel, c] using
    hEq

/--
独立実装へ差し替えるための `Inv` kernel 枠。

現時点では `_of_pack` 投影版への委譲に留める。
-/
theorem triominoWieferichShrinkKernelInv_of_nums_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkWitnessInvB
      p x y z q
      (triominoWieferichShrinkKernelNumsCoreB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkKernelNumsCoreB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      (triominoWieferichShrinkKernelNumsCoreB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  let core : TriominoWieferichShrinkNumsInvCoreB p x y z q :=
    triominoWieferichShrinkNumsInvCoreB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa [triominoWieferichShrinkKernelNumsCoreB_kernel, core] using core.hInv

/--
Triomino/Cosmic 固有の等式側 trace 生成 core（glue）。

`Nums / Eq / Inv` の named kernel を束ね直すだけに保つ。
-/
def triominoWieferichShrinkKernelEqSeedTraceCoreB_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelCoreB p x y z q := by
  let n : TriominoWieferichShrinkKernelNumsB p x y z q :=
    triominoWieferichShrinkKernelNumsCoreB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hEq :
      TriominoWieferichShrinkWitnessEqB p x y z q n.x' n.y' n.z' := by
    simpa [n] using
      triominoWieferichShrinkKernelEq_of_nums_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hInv :
      TriominoWieferichShrinkWitnessInvB p x y z q n.x' n.y' n.z' := by
    simpa [n] using
      triominoWieferichShrinkKernelInv_of_nums_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact ⟨⟨n, hEq⟩, hInv⟩

/--
Triomino/Cosmic 固有の等式側 trace 生成 kernel（glue）。

eq-side trace core への完全委譲に保つ。
-/
def triominoWieferichShrinkKernelEqSeedTraceB_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelCoreB p x y z q :=
  triominoWieferichShrinkKernelEqSeedTraceCoreB_kernel
    (p := p) (x := x) (y := y) (z := z) (q := q)
    hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/--
Triomino/Cosmic 固有の等式側 seed 生成 core（glue）。

eq-side trace から `KernelSeed` だけを回収する。
-/
def triominoWieferichShrinkKernelEqSeedCoreB_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelSeedB p x y z q :=
  (triominoWieferichShrinkKernelEqSeedTraceB_kernel
    (p := p) (x := x) (y := y) (z := z) (q := q)
    hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).toSeed

/-- canonical eq-side core から `KernelSeed` を回収する。 -/
def triominoWieferichShrinkKernelEqSeedB_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelSeedB p x y z q :=
  triominoWieferichShrinkKernelEqSeedCoreB_kernel
    (p := p) (x := x) (y := y) (z := z) (q := q)
    hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- trace 付きの canonical seed から `Inv` witness を回収する。 -/
theorem triominoWieferichShrinkKernelInv_of_seed_core'
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y)
    (s : TriominoWieferichShrinkKernelSeedB p x y z q)
    (tr : TriominoWieferichShrinkKernelInvTraceB p x y z q s) :
    TriominoWieferichShrinkWitnessInvB p x y z q s.n.x' s.n.y' s.n.z' := by
  let _ := hpack
  let _ := hpB
  let _ := hqP
  let _ := hq_not_dvd_gap
  let _ := hqpow_dvd_GN
  exact tr.hInv

/-- canonical eq-side seed から `Inv` witness を回収する。 -/
theorem triominoWieferichShrinkKernelInv_of_seed_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkWitnessInvB
      p x y z q
      (triominoWieferichShrinkKernelEqSeedB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).n.x'
      (triominoWieferichShrinkKernelEqSeedB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).n.y'
      (triominoWieferichShrinkKernelEqSeedB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).n.z' := by
  let c : TriominoWieferichShrinkKernelCoreB p x y z q :=
    triominoWieferichShrinkKernelEqSeedTraceB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let s : TriominoWieferichShrinkKernelSeedB p x y z q := c.toSeed
  let tr : TriominoWieferichShrinkKernelInvTraceB p x y z q s :=
    { hInv := c.hInv }
  simpa
      [triominoWieferichShrinkKernelEqSeedB_kernel,
        triominoWieferichShrinkKernelEqSeedCoreB_kernel,
        TriominoWieferichShrinkKernelCoreB.toSeed, c, s] using
    triominoWieferichShrinkKernelInv_of_seed_core'
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN s tr

/--
Triomino/Cosmic 固有の縮小候補内部 core 生成 kernel（glue）。

eq-side seed と `Inv` 回収を束ね直すだけに保つ。
-/
def triominoWieferichShrinkKernelCoreB_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelCoreB p x y z q := by
  let c : TriominoWieferichShrinkKernelCoreB p x y z q :=
    triominoWieferichShrinkKernelEqSeedTraceB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let s : TriominoWieferichShrinkKernelSeedB p x y z q := c.toSeed
  let tr : TriominoWieferichShrinkKernelInvTraceB p x y z q s :=
    { hInv := c.hInv }
  have hInv :
      TriominoWieferichShrinkWitnessInvB p x y z q s.n.x' s.n.y' s.n.z' := by
    exact
      triominoWieferichShrinkKernelInv_of_seed_core'
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN s tr
  exact ⟨s, hInv⟩

/-- canonical internal seed から `KernelSeed` を回収する。 -/
def triominoWieferichShrinkKernelSeedB_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelSeedB p x y z q :=
  triominoWieferichShrinkKernelEqSeedB_kernel
    (p := p) (x := x) (y := y) (z := z) (q := q)
    hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- canonical internal seed から `Nums` 部分だけを回収する。 -/
def triominoWieferichShrinkKernelNumsB_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelNumsB p x y z q :=
  (triominoWieferichShrinkKernelSeedB_kernel
    (p := p) (x := x) (y := y) (z := z) (q := q)
    hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).n

/-- canonical internal seed から `Eq` witness を回収する。 -/
theorem triominoWieferichShrinkKernelEq_of_seed
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkWitnessEqB
      p x y z q
      (triominoWieferichShrinkKernelSeedB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).n.x'
      (triominoWieferichShrinkKernelSeedB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).n.y'
      (triominoWieferichShrinkKernelSeedB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).n.z' := by
  let s : TriominoWieferichShrinkKernelSeedB p x y z q :=
    triominoWieferichShrinkKernelSeedB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa [s] using s.hEq

/-- canonical `Nums` から `Eq` witness を回収する。 -/
theorem triominoWieferichShrinkKernelEq_of_nums
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkWitnessEqB
      p x y z q
      (triominoWieferichShrinkKernelNumsB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkKernelNumsB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      (triominoWieferichShrinkKernelNumsB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  simpa [triominoWieferichShrinkKernelNumsB_kernel] using
    triominoWieferichShrinkKernelEq_of_seed
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- canonical internal seed から `Inv` witness を回収する。 -/
theorem triominoWieferichShrinkKernelInv_of_seed
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkWitnessInvB
      p x y z q
      (triominoWieferichShrinkKernelSeedB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).n.x'
      (triominoWieferichShrinkKernelSeedB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).n.y'
      (triominoWieferichShrinkKernelSeedB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).n.z' := by
  let c : TriominoWieferichShrinkKernelCoreB p x y z q :=
    triominoWieferichShrinkKernelCoreB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let s : TriominoWieferichShrinkKernelSeedB p x y z q := c.s
  let tr : TriominoWieferichShrinkKernelInvTraceB p x y z q s :=
    { hInv := c.hInv }
  simpa
      [triominoWieferichShrinkKernelSeedB_kernel,
        triominoWieferichShrinkKernelEqSeedB_kernel,
        triominoWieferichShrinkKernelEqSeedCoreB_kernel,
        triominoWieferichShrinkKernelCoreB_kernel, c, s] using
    triominoWieferichShrinkKernelInv_of_seed_core'
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN s tr

/-- canonical `Nums` から `Inv` witness を回収する。 -/
theorem triominoWieferichShrinkKernelInv_of_nums
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkWitnessInvB
      p x y z q
      (triominoWieferichShrinkKernelNumsB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkKernelNumsB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      (triominoWieferichShrinkKernelNumsB_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  simpa [triominoWieferichShrinkKernelNumsB_kernel] using
    triominoWieferichShrinkKernelInv_of_seed
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/--
Triomino/Cosmic 固有の縮小候補内部データ生成 kernel（glue）。

canonical `Nums / Eq / Inv` を束ね直すだけに保つ。
-/
def triominoWieferichShrinkKernelDataB_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelDataB p x y z q := by
  let c : TriominoWieferichShrinkKernelCoreB p x y z q :=
    triominoWieferichShrinkKernelCoreB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let s : TriominoWieferichShrinkKernelSeedB p x y z q := c.s
  let tr : TriominoWieferichShrinkKernelInvTraceB p x y z q s :=
    { hInv := c.hInv }
  have hInv :
      TriominoWieferichShrinkWitnessInvB p x y z q s.n.x' s.n.y' s.n.z' := by
    exact
      triominoWieferichShrinkKernelInv_of_seed_core'
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN s tr
  exact s.toData hInv

/--
Triomino/Cosmic 固有の縮小候補 `XYZ` 生成 kernel（glue）。

内部 data を `XYZ + ctor` へ束ね直すだけに保つ。
-/
def triominoWieferichShrinkXYZ_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkXYZB p x y z q := by
  let d : TriominoWieferichShrinkKernelDataB p x y z q :=
    triominoWieferichShrinkKernelDataB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact
    { x' := d.x'
      y' := d.y'
      z' := d.z'
      ctor :=
        { hzlt := d.hzlt
          hpB' := d.hpB'
          hEq := d.hEq
          hInv := d.hInv } }

/-- kernel から `XYZ` 候補だけを回収する。 -/
def triominoWieferichShrinkXYZ_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkXYZB p x y z q :=
  triominoWieferichShrinkXYZ_kernel
    (p := p) (x := x) (y := y) (z := z) (q := q)
    hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- kernel から canonical `XYZ` に対する trace を回収する。 -/
theorem triominoWieferichShrinkTrace_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkTraceB p x y z q
      (triominoWieferichShrinkXYZ_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN) := by
  let t : TriominoWieferichShrinkXYZB p x y z q :=
    triominoWieferichShrinkXYZ_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  refine
    { hzlt := t.ctor.hzlt
      hpB' := t.ctor.hpB'
      hW := t.ctor.hW }

/--
Triomino/Cosmic 固有の縮小候補データ生成 core（glue）。

`XYZ` と `Trace` の回収を束ねて `XYZ + Trace` へ再構成する。
-/
def triominoWieferichShrinkXYZTraceB_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    { t : TriominoWieferichShrinkXYZB p x y z q //
      TriominoWieferichShrinkTraceB p x y z q t } := by
  let t : TriominoWieferichShrinkXYZB p x y z q :=
    triominoWieferichShrinkXYZ_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have htr :
      TriominoWieferichShrinkTraceB p x y z q t := by
    simpa [t, triominoWieferichShrinkXYZ_core] using
      triominoWieferichShrinkTrace_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact ⟨t, htr⟩

/--
Triomino/Cosmic 固有の縮小候補データ生成（glue）。

`XYZ` と `Trace` の回収を束ねて `XYZ + Trace` へ再構成する。
-/
def triominoWieferichShrinkXYZTraceB_impl
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    { t : TriominoWieferichShrinkXYZB p x y z q //
      TriominoWieferichShrinkTraceB p x y z q t } := by
  let t : TriominoWieferichShrinkXYZB p x y z q :=
    triominoWieferichShrinkXYZ_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have htr :
      TriominoWieferichShrinkTraceB p x y z q t := by
    simpa [t, triominoWieferichShrinkXYZ_core] using
      triominoWieferichShrinkTrace_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact ⟨t, htr⟩

/-- `XYZ + Trace` から `XYZ + Cert` 束へ戻す glue。 -/
def triominoWieferichShrinkXYZCertB_impl
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkXYZCertB p x y z q := by
  let s :
      { t : TriominoWieferichShrinkXYZB p x y z q //
        TriominoWieferichShrinkTraceB p x y z q t } :=
    triominoWieferichShrinkXYZTraceB_impl
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact triominoWieferichShrinkXYZCertB_of_trace s.1 s.2

/-- `XYZ + Cert` 束から、候補 triple だけを取り出す。 -/
def triominoWieferichShrinkXYZB_of_core
    {p x y z q : ℕ}
    (s : TriominoWieferichShrinkXYZCertB p x y z q) :
    TriominoWieferichShrinkXYZB p x y z q :=
  s.t

/-- core 値から strict 減少を回収する。 -/
theorem triominoWieferichShrink_hzlt_of_core
    {p x y z q : ℕ}
    (s : TriominoWieferichShrinkXYZCertB p x y z q) :
    s.t.z' < z :=
  s.hc.hzlt

/-- core 値から Branch B 条件保存を回収する。 -/
theorem triominoWieferichShrink_hpB'_of_core
    {p x y z q : ℕ}
    (s : TriominoWieferichShrinkXYZCertB p x y z q) :
    ¬ p ∣ (s.t.z' - s.t.y') :=
  s.hc.hpB'

/-- core 値から witness を回収する。 -/
theorem triominoWieferichShrink_witness_of_core
    {p x y z q : ℕ}
    (s : TriominoWieferichShrinkXYZCertB p x y z q) :
    TriominoWieferichShrinkWitnessB p x y z q s.t.x' s.t.y' s.t.z' :=
  s.hc.hW

/-- `XYZ + Cert` 束から、候補 triple だけを取り出す。 -/
def triominoWieferichShrinkXYZB_impl
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkXYZB p x y z q :=
  triominoWieferichShrinkXYZB_of_core
    (triominoWieferichShrinkXYZCertB_impl
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN)

/-- canonical shrink candidate の strict 減少。 -/
theorem triominoWieferichShrink_hzlt
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkXYZB_impl
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' < z :=
  triominoWieferichShrink_hzlt_of_core
    (triominoWieferichShrinkXYZCertB_impl
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN)

/-- canonical shrink candidate は Branch B 条件を保つ。 -/
theorem triominoWieferichShrink_hpB'
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    ¬ p ∣
      ((triominoWieferichShrinkXYZB_impl
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z'
        -
        (triominoWieferichShrinkXYZB_impl
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y') :=
  triominoWieferichShrink_hpB'_of_core
    (triominoWieferichShrinkXYZCertB_impl
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN)

/-- canonical shrink candidate に対する witness 回収。 -/
theorem triominoWieferichShrink_witness
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkWitnessB
      p x y z q
      (triominoWieferichShrinkXYZB_impl
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkXYZB_impl
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      (triominoWieferichShrinkXYZB_impl
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' :=
  triominoWieferichShrink_witness_of_core
    (triominoWieferichShrinkXYZCertB_impl
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN)

/-- `Nums` の生成は、`XYZ + Cert` からの glue に寄せる。 -/
def triominoWieferichShrinkNumsB_impl
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkNumsB p x y z q := by
  let s : TriominoWieferichShrinkXYZCertB p x y z q :=
    triominoWieferichShrinkXYZCertB_impl
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let t : TriominoWieferichShrinkXYZB p x y z q :=
    triominoWieferichShrinkXYZB_of_core s
  have hc : TriominoWieferichShrinkCertB p x y z q t :=
    by
      refine
        { hzlt := ?_
          hpB' := ?_
          hW := ?_ }
      · simpa [t, triominoWieferichShrinkXYZB_of_core] using
          triominoWieferichShrink_hzlt_of_core s
      · simpa [t, triominoWieferichShrinkXYZB_of_core] using
          triominoWieferichShrink_hpB'_of_core s
      · simpa [t, triominoWieferichShrinkXYZB_of_core] using
          triominoWieferichShrink_witness_of_core s
  exact triominoWieferichShrinkNumsB_of_XYZ_Cert t hc

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
