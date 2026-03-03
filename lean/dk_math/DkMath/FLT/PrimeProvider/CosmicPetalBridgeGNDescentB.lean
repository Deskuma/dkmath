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

/--
`x'^p + y'^p = z'^p` と `x' ≠ 0` から、`y' < z'` と `y' ≤ z'` を回収する。

shadow triple 用に `hEq'` だけを独立実装したい段で、`Eq` witness の残り 2 フィールドを
transport なしで再構成するための補助補題。
-/
theorem triominoWieferichShrinkWitnessEq_of_eq_and_hx0
    {p x y z q x' y' z' : ℕ}
    (hx0' : x' ≠ 0)
    (hEq' : x' ^ p + y' ^ p = z' ^ p) :
    TriominoWieferichShrinkWitnessEqB p x y z q x' y' z' := by
  have hxpos : 0 < x' := Nat.pos_of_ne_zero hx0'
  have hxpow_pos : 0 < x' ^ p := by
    apply Nat.pow_pos
    exact hxpos
  have hy_pow_lt_hz_pow : y' ^ p < z' ^ p := by
    have : y' ^ p < x' ^ p + y' ^ p := Nat.lt_add_of_pos_left hxpow_pos
    simpa [hEq'] using this
  have hyzLt : y' < z' := by
    by_contra hyz_ge
    have hzy : z' ≤ y' := le_of_not_gt hyz_ge
    have hz_pow_le_hy_pow : z' ^ p ≤ y' ^ p := Nat.pow_le_pow_left hzy p
    exact (not_le_of_gt hy_pow_lt_hz_pow) hz_pow_le_hy_pow
  exact
    { hEq' := hEq'
      hyz' := le_of_lt hyzLt
      hyzLt := hyzLt }

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
  hxMul : x = q * s.n.x'
  hyEq : s.n.y' = y

/--
`KernelSeedB` に `hxMul / hyEq` だけを載せた薄い bundle。

最後の `sorry` には `Inv` を要求せず、`Seed + links` だけを構成させる。
-/
structure TriominoWieferichShrinkKernelSeedLinkB (p x y z q : ℕ) where
  s : TriominoWieferichShrinkKernelSeedB p x y z q
  hxMul : x = q * s.n.x'
  hyEq : s.n.y' = y

/--
最後の数学 kernel が返すべき最小物。

`Eq` witness 全体ではなく `hEq'` だけを要求し、`hyz / hyzLt` は外で再構成する。
-/
structure TriominoWieferichShrinkKernelNumsEqLinkB (p x y z q : ℕ) where
  n : TriominoWieferichShrinkKernelNumsB p x y z q
  hEq' : n.x' ^ p + n.y' ^ p = n.z' ^ p
  hxMul : x = q * n.x'
  hyEq : n.y' = y

/--
`z_core` が最終的に必要とする候補 `z'` と、その trace を束ねた最小データ。

ここでは「どの候補を採るか」は固定せず、非循環に供給できる
`x' / y' / z'` とその `hzlt / links / Eq` だけを要求する。
-/
structure TriominoWieferichShrinkKernelCandidateZDataB (p x y z q : ℕ) where
  x' : ℕ
  y' : ℕ
  z' : ℕ
  hzlt : z' < z
  hxdiv : x' = x / q
  hyEq : y' = y
  hpB' : ¬ p ∣ (z' - y)
  hEq' : (x / q) ^ p + y ^ p = z' ^ p

/-- `candidateZ` 用データから最終の `Subtype` を組む薄い包装。 -/
def TriominoWieferichShrinkKernelCandidateZDataB.toSubtype
    {p x y z q : ℕ}
    (d : TriominoWieferichShrinkKernelCandidateZDataB p x y z q) :
    { z' : ℕ //
      z' < z
        ∧ ¬ p ∣ (z' - y)
        ∧ (x / q) ^ p + y ^ p = z' ^ p } :=
  ⟨d.z', ⟨d.hzlt, ⟨d.hpB', d.hEq'⟩⟩⟩

/--
shadow 方針で固定した `x' := x / q`, `y' := y` のもとで、
最後の数学 kernel が返すべき最小物。

残る本丸は `z'` とその shrink 条件、そして
`(x / q)^p + y^p = z'^p` だけに押し込める。
-/
structure TriominoWieferichShrinkKernelZEqB (p x y z q : ℕ) where
  z' : ℕ
  hzlt : z' < z
  hpB' : ¬ p ∣ (z' - y)
  hEq' : (x / q) ^ p + y ^ p = z' ^ p

/--
`q^p ∣ GN p (z - y) y` から、`q ∣ x` を回収する早期補助。

`x = q * (x / q)` を構成する複数の core で共有する。
-/
theorem triominoWieferichShrink_q_dvd_x_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    q ∣ x := by
  let _ := hpB
  let _ := hq_not_dvd_gap
  have hq_dvd_qpow : q ∣ q ^ p := by
    exact dvd_pow (dvd_refl q) hpack.hp.ne_zero
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
`q^p ∣ GN p (z - y) y` から、`x = q * (x / q)` を回収する早期補助。

`q ∣ x` の直後に必ず使う割り算正規化を、複数の core で共有する。
-/
theorem triominoWieferichShrink_x_eq_q_mul_div_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    x = q * (x / q) := by
  have hxq : q ∣ x :=
    triominoWieferichShrink_q_dvd_x_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa using (Nat.mul_div_cancel' hxq).symm

/--
`GN p (z-y) y` は、整数環では差の冪和 `Sd z y p` と一致する。

これは gcd ルートで `gcd_specialized_divides_d` を `GN` へ接続するための橋。
-/
theorem triominoWieferichShrink_int_GN_eq_Sd_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    GN p (((z - y : ℕ) : ℤ)) (y : ℤ) = DkMath.Algebra.DiffPow.diffPowSum (z : ℤ) (y : ℤ) p := by
  let _ := hpB
  let _ := hqP
  let _ := hq_not_dvd_gap
  let _ := hqpow_dvd_GN
  have hp_pos : 0 < p := hpack.hp.pos
  have hGN_nat : z ^ p - y ^ p = (z - y) * GN p (z - y) y := by
    simpa using pow_sub_pow_factor_cosmic_N hp_pos hpack.hyz_lt
  have hyz_pow : y ^ p ≤ z ^ p := by
    exact Nat.pow_le_pow_left hpack.hyz p
  have hGN_int :
      (z : ℤ) ^ p - (y : ℤ) ^ p =
        (((z - y : ℕ) : ℤ) * GN p (((z - y : ℕ) : ℤ)) (y : ℤ)) := by
    calc
      (z : ℤ) ^ p - (y : ℤ) ^ p = (↑(z ^ p) : ℤ) - ↑(y ^ p) := by
        simp [Nat.cast_pow]
      _ = ((z ^ p - y ^ p : ℕ) : ℤ) := by
        rw [← Nat.cast_sub hyz_pow]
      _ = (((z - y) * GN p (z - y) y : ℕ) : ℤ) := by
        rw [hGN_nat]
      _ = (((z - y : ℕ) : ℤ) * GN p (((z - y : ℕ) : ℤ)) (y : ℤ)) := by
        simp [GN]
  have hSd :
      (z : ℤ) ^ p - (y : ℤ) ^ p =
        (((z - y : ℕ) : ℤ) * DkMath.Algebra.DiffPow.diffPowSum (z : ℤ) (y : ℤ) p) := by
    simpa [Int.ofNat_sub hpack.hyz] using
      (DkMath.Algebra.DiffPow.pow_sub_pow_factor
        (a := (z : ℤ)) (b := (y : ℤ)) (d := p))
  have hgap_ne0 : (((z - y : ℕ) : ℤ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt))
  have hmul :
      (((z - y : ℕ) : ℤ) * GN p (((z - y : ℕ) : ℤ)) (y : ℤ)) =
        (((z - y : ℕ) : ℤ) * DkMath.Algebra.DiffPow.diffPowSum (z : ℤ) (y : ℤ) p) := by
    rw [← hGN_int, hSd]
  exact Int.eq_of_mul_eq_mul_left hgap_ne0 hmul

/--
primitive な Branch B 文脈では、`gcd (z-y, GN p (z-y) y)` は整数環で `p` を割る。

まずは `Int.gcd` 版で押さえ、必要なら下流で `Nat.gcd` 版へ落とす。
-/
theorem triominoWieferichShrink_gap_gcd_GN_dvd_p_int
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    Int.gcd (((z - y : ℕ) : ℤ)) (GN p (((z - y : ℕ) : ℤ)) (y : ℤ)) ∣ p := by
  let _ := hpB
  let _ := hqP
  let _ := hq_not_dvd_gap
  let _ := hqpow_dvd_GN
  have hcop_yz : Nat.Coprime y z := by
    exact coprime_right_of_add_pow_eq_pow hpack.hp hpack.hxy hpack.hEq
  have hgcd_zy : Nat.gcd z y = 1 := by
    exact (Nat.coprime_iff_gcd_eq_one).1 (by simpa [Nat.coprime_comm] using hcop_yz)
  have hab : Int.gcd (z : ℤ) (y : ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs]
    simp [hgcd_zy]
  have hp1 : 1 ≤ p := Nat.succ_le_of_lt hpack.hp.pos
  have hSd :
      Int.gcd (((z - y : ℕ) : ℤ)) (DkMath.Algebra.DiffPow.diffPowSum (z : ℤ) (y : ℤ) p) ∣ p := by
    simpa [Int.ofNat_sub hpack.hyz] using
      (DkMath.NumberTheory.GcdDiffPow.gcd_divides_d
        (a := (z : ℤ)) (b := (y : ℤ)) (d := p) hp1 hab)
  have hGN_eq_Sd :
      GN p (((z - y : ℕ) : ℤ)) (y : ℤ) = DkMath.Algebra.DiffPow.diffPowSum (z : ℤ) (y : ℤ) p := by
    exact
      triominoWieferichShrink_int_GN_eq_Sd_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  change Int.gcd (((z - y : ℕ) : ℤ)) (GN p (((z - y : ℕ) : ℤ)) (y : ℤ)) ∣ p
  rw [hGN_eq_Sd]
  exact hSd

/--
Branch B 文脈では `gap = z - y` と `GN p gap y` は互いに素になる。

`gcd(gap, GN) ∣ p` と `p ∤ gap` を組み合わせ、共通素因子があれば `p` 自身になって
`hpB` に矛盾する、という形で押す。
-/
theorem triominoWieferichShrink_gap_coprime_GN_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    Nat.Coprime (z - y) (GN p (z - y) y) := by
  let _ := hqP
  let _ := hq_not_dvd_gap
  let _ := hqpow_dvd_GN
  refine (Nat.coprime_iff_gcd_eq_one).2 ?_
  by_contra hg1
  have hg_ne1 : Nat.gcd (z - y) (GN p (z - y) y) ≠ 1 := by
    simpa using hg1
  rcases Nat.exists_prime_and_dvd hg_ne1 with ⟨r, hrP, hr_gcd⟩
  have hr_gap : r ∣ (z - y) := dvd_trans hr_gcd (Nat.gcd_dvd_left (z - y) (GN p (z - y) y))
  have hr_GN : r ∣ GN p (z - y) y := dvd_trans hr_gcd (Nat.gcd_dvd_right (z - y) (GN p (z - y) y))
  have hr_gap_int : (r : ℤ) ∣ (((z - y : ℕ) : ℤ)) := by
    exact_mod_cast hr_gap
  have hr_GN_cast : (r : ℤ) ∣ ((GN p (z - y) y : ℕ) : ℤ) := by
    exact_mod_cast hr_GN
  have hr_GN_int : (r : ℤ) ∣ GN p (((z - y : ℕ) : ℤ)) (y : ℤ) := by
    simpa [GN] using hr_GN_cast
  have hr_gcd_int :
      r ∣ Int.gcd (((z - y : ℕ) : ℤ)) (GN p (((z - y : ℕ) : ℤ)) (y : ℤ)) := by
    exact Int.dvd_gcd hr_gap_int hr_GN_int
  have hgapgcd_dvd_p :
      Int.gcd (((z - y : ℕ) : ℤ)) (GN p (((z - y : ℕ) : ℤ)) (y : ℤ)) ∣ p := by
    exact
      triominoWieferichShrink_gap_gcd_GN_dvd_p_int
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hr_dvd_p : r ∣ p := dvd_trans hr_gcd_int hgapgcd_dvd_p
  have hr_eq_p : r = p := (Nat.prime_dvd_prime_iff_eq hrP hpack.hp).1 hr_dvd_p
  exact hpB (by simpa [hr_eq_p] using hr_gap)

private lemma triominoWieferichShrink_exists_eq_pow_of_factorization_dvd_core
    {n p : ℕ} (hn0 : n ≠ 0)
    (hdiv : ∀ r : ℕ, p ∣ n.factorization r) :
    ∃ t : ℕ, n = t ^ p := by
  classical
  let t : ℕ := n.factorization.support.prod (fun r => r ^ (n.factorization r / p))
  refine ⟨t, ?_⟩
  have hn_prod :
      n.factorization.support.prod (fun r => r ^ n.factorization r) = n :=
    Nat.factorization_prod_pow_eq_self hn0
  calc
    n = n.factorization.support.prod (fun r => r ^ n.factorization r) := by
      exact hn_prod.symm
    _ = n.factorization.support.prod (fun r => r ^ ((n.factorization r / p) * p)) := by
      refine Finset.prod_congr rfl (fun r _ => ?_)
      have hr : p ∣ n.factorization r := hdiv r
      rw [Nat.div_mul_cancel hr]
    _ = n.factorization.support.prod (fun r => (r ^ (n.factorization r / p)) ^ p) := by
      refine Finset.prod_congr rfl (fun r _ => ?_)
      rw [pow_mul]
    _ = (n.factorization.support.prod (fun r => r ^ (n.factorization r / p))) ^ p := by
      rw [Finset.prod_pow]
    _ = t ^ p := rfl

/--
Branch B 文脈では `x^p = gap * GN` かつ `gap ⟂ GN` なので、
`gap` と `GN` はそれぞれ `p` 乗になる。

これは `candidateZ_data` を explicit な `z'` で殴る代わりに、
矛盾ルートを試すための最小補助定理。
-/
theorem triominoWieferichShrink_gap_GN_are_pth_powers_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    ∃ u v : ℕ, (z - y) = u ^ p ∧ GN p (z - y) y = v ^ p := by
  classical
  let gap : ℕ := z - y
  let body : ℕ := GN p (z - y) y
  have hgap0 : gap ≠ 0 := by
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt)
  have hbody0 : body ≠ 0 := by
    intro h0
    have hxpow : x ^ p = gap * body := by
      simpa [gap, body] using hpack.xpow_eq_gap_mul_GN
    apply (pow_ne_zero p hpack.hx0)
    calc
      x ^ p = gap * body := hxpow
      _ = 0 := by simp [h0]
  have hcop : Nat.Coprime gap body := by
    simpa [gap, body] using
      triominoWieferichShrink_gap_coprime_GN_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hgcd : Nat.gcd gap body = 1 := (Nat.coprime_iff_gcd_eq_one).1 hcop
  have hgap_body_eq : gap * body = x ^ p := by
    simpa [gap, body] using hpack.xpow_eq_gap_mul_GN.symm
  have hdiv_gap : ∀ r : ℕ, p ∣ gap.factorization r := by
    intro r
    have h_inf : gap.factorization ⊓ body.factorization = 0 := by
      have h := Nat.factorization_gcd hgap0 hbody0
      rw [hgcd] at h
      simpa using h.symm
    have hmin : (gap.factorization ⊓ body.factorization) r = 0 := by
      rw [h_inf]
      rfl
    have h_or : gap.factorization r = 0 ∨ body.factorization r = 0 := by
      simp only [Finsupp.inf_apply] at hmin
      omega
    have hsum : gap.factorization r + body.factorization r = p * x.factorization r := by
      have hmul :
          (gap * body).factorization r = gap.factorization r + body.factorization r := by
        simp [Nat.factorization_mul hgap0 hbody0]
      have hpow :
          (x ^ p).factorization r = p * x.factorization r := by
        simp [Nat.factorization_pow x p]
      calc
        gap.factorization r + body.factorization r = (gap * body).factorization r := hmul.symm
        _ = (x ^ p).factorization r := by simp [hgap_body_eq]
        _ = p * x.factorization r := hpow
    cases h_or with
    | inl hgap_zero =>
        simp [hgap_zero]
    | inr hbody_zero =>
        refine ⟨x.factorization r, ?_⟩
        omega
  have hdiv_body : ∀ r : ℕ, p ∣ body.factorization r := by
    intro r
    have h_inf : gap.factorization ⊓ body.factorization = 0 := by
      have h := Nat.factorization_gcd hgap0 hbody0
      rw [hgcd] at h
      simpa using h.symm
    have hmin : (gap.factorization ⊓ body.factorization) r = 0 := by
      rw [h_inf]
      rfl
    have h_or : gap.factorization r = 0 ∨ body.factorization r = 0 := by
      simp only [Finsupp.inf_apply] at hmin
      omega
    have hsum : gap.factorization r + body.factorization r = p * x.factorization r := by
      have hmul :
          (gap * body).factorization r = gap.factorization r + body.factorization r := by
        simp [Nat.factorization_mul hgap0 hbody0]
      have hpow :
          (x ^ p).factorization r = p * x.factorization r := by
        simp [Nat.factorization_pow x p]
      calc
        gap.factorization r + body.factorization r = (gap * body).factorization r := hmul.symm
        _ = (x ^ p).factorization r := by simp [hgap_body_eq]
        _ = p * x.factorization r := hpow
    cases h_or with
    | inl hgap_zero =>
        refine ⟨x.factorization r, ?_⟩
        omega
    | inr hbody_zero =>
        simp [hbody_zero]
  rcases
      triominoWieferichShrink_exists_eq_pow_of_factorization_dvd_core
        (n := gap) (p := p) hgap0 hdiv_gap with ⟨u, hu⟩
  rcases
      triominoWieferichShrink_exists_eq_pow_of_factorization_dvd_core
        (n := body) (p := p) hbody0 hdiv_body with ⟨v, hv⟩
  exact ⟨u, v, hu, hv⟩

/--
route 1 の補助:
`GN p (z-y) y` が `p` 乗で、かつ `q^p ∣ GN` なら、
その `p` 乗根は `q` を因子にもつ。したがって `GN = (q * v1)^p`。
-/
theorem triominoWieferichShrink_GN_eq_q_mul_pow_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    ∃ v1 : ℕ, GN p (z - y) y = (q * v1) ^ p := by
  rcases
      triominoWieferichShrink_gap_GN_are_pth_powers_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN with
    ⟨_u, v, _hu, hv⟩
  have hqpow_dvd_vpow : q ^ p ∣ v ^ p := by
    rw [← hv]
    exact hqpow_dvd_GN
  have hq_dvd_vpow : q ∣ v ^ p := by
    have hq_dvd_qpow : q ∣ q ^ p := by
      exact dvd_pow (dvd_refl q) hpack.hp.ne_zero
    exact dvd_trans hq_dvd_qpow hqpow_dvd_vpow
  have hq_dvd_v : q ∣ v := hqP.dvd_of_dvd_pow hq_dvd_vpow
  rcases hq_dvd_v with ⟨v1, hv1⟩
  refine ⟨v1, ?_⟩
  calc
    GN p (z - y) y = v ^ p := hv
    _ = (q * v1) ^ p := by rw [hv1]

/--
route 1 の補助:
`gap = u^p` と `GN = (q*v1)^p` の分解から、
`x / q = u * v1` まで落とす。
-/
theorem triominoWieferichShrink_xdiv_eq_mul_of_gap_GN_powers_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    ∃ u v1 : ℕ,
      (z - y) = u ^ p
        ∧ GN p (z - y) y = (q * v1) ^ p
        ∧ x / q = u * v1 := by
  rcases
      triominoWieferichShrink_gap_GN_are_pth_powers_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN with
    ⟨u, v, hu, hv⟩
  have hqpow_dvd_vpow : q ^ p ∣ v ^ p := by
    rw [← hv]
    exact hqpow_dvd_GN
  have hq_dvd_vpow : q ∣ v ^ p := by
    have hq_dvd_qpow : q ∣ q ^ p := by
      exact dvd_pow (dvd_refl q) hpack.hp.ne_zero
    exact dvd_trans hq_dvd_qpow hqpow_dvd_vpow
  have hq_dvd_v : q ∣ v := hqP.dvd_of_dvd_pow hq_dvd_vpow
  rcases hq_dvd_v with ⟨v1, hv1⟩
  have hGNq : GN p (z - y) y = (q * v1) ^ p := by
    calc
      GN p (z - y) y = v ^ p := hv
      _ = (q * v1) ^ p := by rw [hv1]
  have hxMul : x = q * (x / q) :=
    triominoWieferichShrink_x_eq_q_mul_div_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hgap_body :
      x ^ p = (z - y) * GN p (z - y) y := by
    simpa [PrimeGe5CounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN
  have hpow_eq : (q * (x / q)) ^ p = (q * (u * v1)) ^ p := by
    calc
      (q * (x / q)) ^ p = x ^ p := by rw [← hxMul]
      _ = (z - y) * GN p (z - y) y := hgap_body
      _ = (z - y) * (q * v1) ^ p := by rw [hGNq]
      _ = u ^ p * (q * v1) ^ p := by rw [hu]
      _ = (u * (q * v1)) ^ p := by
        exact (Nat.mul_pow u (q * v1) p).symm
      _ = (q * (u * v1)) ^ p := by
        congr 1
        ac_rfl
  have hmul_eq : q * (x / q) = q * (u * v1) := by
    exact (Nat.pow_left_injective hpack.hp.ne_zero) hpow_eq
  have hxdiv_eq : x / q = u * v1 := by
    exact Nat.eq_of_mul_eq_mul_left hqP.pos hmul_eq
  exact ⟨u, v1, hu, hGNq, hxdiv_eq⟩

/--
`x = q * (x / q)` と `x ≠ 0` から、shadow 固定の `x / q` も非零になる。

`z_core` 内で `(x / q)^p` の正値を使う前処理を共通化する。
-/
theorem triominoWieferichShrink_xdiv_ne_zero_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    x / q ≠ 0 := by
  intro hxdiv0
  apply hpack.hx0
  calc
    x = q * (x / q) := by
      exact
        triominoWieferichShrink_x_eq_q_mul_div_core
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
    _ = 0 := by simp [hxdiv0]

/--
`x / q` は nonzero なので、候補式比較で使う `(x / q)^p` も正になる。
-/
theorem triominoWieferichShrink_xdiv_pow_pos_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    0 < (x / q) ^ p := by
  have hxdiv_pos : 0 < x / q := by
    exact Nat.pos_of_ne_zero <|
      triominoWieferichShrink_xdiv_ne_zero_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact Nat.pow_pos hxdiv_pos

/--
元の反例等式を shadow 固定の `x / q` へ正規化した形。

`z_core` で `z'^p < z^p` を比較するときの基準式として使う。
-/
theorem triominoWieferichShrink_zpow_eq_ypow_add_qpow_mul_xdivpow_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    z ^ p = y ^ p + q ^ p * (x / q) ^ p := by
  have hxMul : x = q * (x / q) := by
    exact
      triominoWieferichShrink_x_eq_q_mul_div_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  calc
    z ^ p = x ^ p + y ^ p := by
      simpa [Nat.add_comm] using hpack.hEq.symm
    _ = (q * (x / q)) ^ p + y ^ p := by
      have hxpow : x ^ p = (q * (x / q)) ^ p := by
        nth_rewrite 1 [hxMul]
        rfl
      simp [hxpow]
    _ = q ^ p * (x / q) ^ p + y ^ p := by
      simp [Nat.mul_pow]
    _ = y ^ p + q ^ p * (x / q) ^ p := by
      ac_rfl

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
`Nums + links` から `Inv` witness を回収する。

最後の数学 kernel から `Inv` を外へ追い出し、外側の pack 条件だけで再構成する。
-/
theorem triominoWieferichShrinkKernelInv_of_nums_from_links
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (n : TriominoWieferichShrinkKernelNumsB p x y z q)
    (hxMul : x = q * n.x')
    (hyEq : n.y' = y) :
    TriominoWieferichShrinkWitnessInvB p x y z q n.x' n.y' n.z' := by
  refine
    { hxy' := ?_
      hx0' := ?_
      hy0' := ?_
      hz0' := ?_ }
  · refine (Nat.coprime_iff_gcd_eq_one).2 ?_
    by_contra hg1
    have hg_ne1 : Nat.gcd n.x' n.y' ≠ 1 := by
      simpa using hg1
    rcases Nat.exists_prime_and_dvd (n := Nat.gcd n.x' n.y') hg_ne1 with ⟨d, hdP, hd_dvd_g⟩
    have hd_dvd_x' : d ∣ n.x' := dvd_trans hd_dvd_g (Nat.gcd_dvd_left n.x' n.y')
    have hd_dvd_y' : d ∣ n.y' := dvd_trans hd_dvd_g (Nat.gcd_dvd_right n.x' n.y')
    have hd_dvd_x : d ∣ x := by
      have hd_dvd_rhs : d ∣ q * n.x' := dvd_mul_of_dvd_right hd_dvd_x' q
      simpa [hxMul] using hd_dvd_rhs
    have hd_dvd_y : d ∣ y := by
      simpa [hyEq] using hd_dvd_y'
    exact (Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt hdP) hd_dvd_x hd_dvd_y) hpack.hxy
  · intro hx0'
    apply hpack.hx0
    calc
      x = q * n.x' := hxMul
      _ = 0 := by simp [hx0']
  · simpa [hyEq] using hpack.hy0
  · intro hz0'
    -- In `Nat`, `0 - y = 0`, so `z' = 0` would force `p ∣ (z' - y)`.
    apply n.hpB'
    simp [hz0']

/--
`Nums + hEq' + links` から `Seed + links` を梱包する。

最後の `sorry` は `hEq'` まででよく、`Eq` witness は外で再構成する。
-/
def TriominoWieferichShrinkKernelNumsEqLinkB.toSeedLink
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (d : TriominoWieferichShrinkKernelNumsEqLinkB p x y z q) :
    TriominoWieferichShrinkKernelSeedLinkB p x y z q := by
  have hx0' : d.n.x' ≠ 0 := by
    intro hx0'
    apply hpack.hx0
    calc
      x = q * d.n.x' := d.hxMul
      _ = 0 := by simp [hx0']
  have hEq :
      TriominoWieferichShrinkWitnessEqB p x y z q d.n.x' d.n.y' d.n.z' := by
    exact
      triominoWieferichShrinkWitnessEq_of_eq_and_hx0
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hx0' d.hEq'
  exact ⟨⟨d.n, hEq⟩, d.hxMul, d.hyEq⟩

/--
shadow 固定の `z' + hEq'` から、`Nums + hEq' + links` を梱包する。

`x' := x / q`, `y' := y` はここで固定し、
`hxMul / hyEq` は純算術で外側合成する。
-/
def TriominoWieferichShrinkKernelZEqB.toNumsEqLink
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y)
    (d : TriominoWieferichShrinkKernelZEqB p x y z q) :
    TriominoWieferichShrinkKernelNumsEqLinkB p x y z q := by
  have hxMul : x = q * (x / q) := by
    exact
      triominoWieferichShrink_x_eq_q_mul_div_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact
    { n :=
        { x' := x / q
          y' := y
          z' := d.z'
          hzlt := d.hzlt
          hpB' := by simpa using d.hpB' }
      hEq' := by simpa using d.hEq'
      hxMul := hxMul
      hyEq := rfl }

/--
Triomino/Cosmic 固有の等式側 trace 生成 pack の最小核（本丸）。

route 1 で `gap = u^p`, `GN = (q*v1)^p`, `x/q = u*v1`
までは純算術に切り出せたが、`∃`-形式の証人をそのまま `Type` 側へ流すと
`Prop` から `Type` への elimination 制限に当たる。

現時点では、この `candidateZ_data` 自体を最後の `Type`-値の穴として保持する。
-/
def triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_data
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelCandidateZDataB p x y z q := by
  let _ := hpack
  let _ := hpB
  let _ := hqP
  let _ := hq_not_dvd_gap
  let _ := hqpow_dvd_GN
  sorry

/--
Triomino/Cosmic 固有の等式側 trace 生成 pack の最小核（本丸）。

最後の未解決点は、適切な候補 `c` と
`hzlt / hxdiv / hyEq / hpB' / hEq'` をどう同時に供給するかに押し込める。
-/
def triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    { z' : ℕ //
      z' < z
        ∧ ¬ p ∣ (z' - y)
        ∧ (x / q) ^ p + y ^ p = z' ^ p } := by
  let d : TriominoWieferichShrinkKernelCandidateZDataB p x y z q :=
    triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ_data
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact d.toSubtype

/--
Triomino/Cosmic 固有の等式側 trace 生成 pack の最小核（本丸）。

最後の未解決点は、適切な `z'` を 1 つ構成して
`hzlt / hpB' / hEq'` を同時に満たすことに押し込める。
-/
def triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelZEqB p x y z q := by
  have hzCore :
      { z' : ℕ //
        z' < z
          ∧ ¬ p ∣ (z' - y)
          ∧ (x / q) ^ p + y ^ p = z' ^ p } := by
    exact
      triominoWieferichShrinkKernelEqSeedTracePackB_kernel_candidateZ
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  rcases hzCore with ⟨z', hzSpec⟩
  rcases hzSpec with ⟨hzlt, hpB', hEq'⟩
  exact
    { z' := z'
      hzlt := hzlt
      hpB' := hpB'
      hEq' := hEq' }

/--
Triomino/Cosmic 固有の等式側 trace 生成 pack（本丸）。

最小核から `Eq` witness を再構成して `Seed + links` へ梱包する。
-/
def triominoWieferichShrinkKernelEqSeedTracePackB_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkKernelSeedLinkB p x y z q := by
  let dz : TriominoWieferichShrinkKernelZEqB p x y z q :=
    triominoWieferichShrinkKernelEqSeedTracePackB_kernel_z_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let d : TriominoWieferichShrinkKernelNumsEqLinkB p x y z q :=
    dz.toNumsEqLink hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact d.toSeedLink hpack

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
  let c : TriominoWieferichShrinkKernelSeedLinkB p x y z q :=
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
  let c : TriominoWieferichShrinkKernelSeedLinkB p x y z q :=
    triominoWieferichShrinkKernelEqSeedTracePackB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hInv :
      TriominoWieferichShrinkWitnessInvB p x y z q c.s.n.x' c.s.n.y' c.s.n.z' := by
    exact
      triominoWieferichShrinkKernelInv_of_nums_from_links
        hpack c.s.n c.hxMul c.hyEq
  simpa [triominoWieferichShrinkKernelNums_of_pack, c] using hInv

/-- canonical eq-side trace pack から `x = q * x'` を回収する投影版。 -/
theorem triominoWieferichShrinkKernel_hxmul_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    x =
      q *
        (triominoWieferichShrinkKernelNums_of_pack
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' := by
  let c : TriominoWieferichShrinkKernelSeedLinkB p x y z q :=
    triominoWieferichShrinkKernelEqSeedTracePackB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa [triominoWieferichShrinkKernelNums_of_pack, c] using c.hxMul

/-- canonical eq-side trace pack から `y' = y` を回収する投影版。 -/
theorem triominoWieferichShrinkKernel_hy_eq_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkKernelNums_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = y := by
  let c : TriominoWieferichShrinkKernelSeedLinkB p x y z q :=
    triominoWieferichShrinkKernelEqSeedTracePackB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa [triominoWieferichShrinkKernelNums_of_pack, c] using c.hyEq

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

/-- `Candidate` が元の `(x, y)` とどう繋がっているかをまとめる link 仕様。 -/
structure TriominoWieferichShrinkNumsInvCandidateLinkSpecB
    (p x y z q : ℕ)
    (c : TriominoWieferichShrinkNumsInvCandidateB p x y z q) : Prop where
  hxMul : x = q * c.x'
  hyEq : c.y' = y

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

/-- `_of_pack` backend から `x = q * x'` を回収する。 -/
theorem triominoWieferichShrinkNumsInvCandidate_hxmul_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    x =
      q *
        (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' := by
  let r0 : TriominoWieferichShrinkNumsInvRecipeB p x y z q :=
    triominoWieferichShrinkNumsInvRecipe_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let n : TriominoWieferichShrinkKernelNumsB p x y z q :=
    triominoWieferichShrinkKernelNums_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa [triominoWieferichShrinkNumsInvCandidate_of_pack, r0, n] using
    triominoWieferichShrinkKernel_hxmul_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `_of_pack` backend から `y' = y` を回収する。 -/
theorem triominoWieferichShrinkNumsInvCandidate_hy_eq_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = y := by
  let r0 : TriominoWieferichShrinkNumsInvRecipeB p x y z q :=
    triominoWieferichShrinkNumsInvRecipe_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let n : TriominoWieferichShrinkKernelNumsB p x y z q :=
    triominoWieferichShrinkKernelNums_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa [triominoWieferichShrinkNumsInvCandidate_of_pack, r0, n] using
    triominoWieferichShrinkKernel_hy_eq_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- `_of_pack` backend から `hxMul / hyEq` を 1 本に束ねて回収する。 -/
theorem triominoWieferichShrinkNumsInvCandidateLinkSpec_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkNumsInvCandidateLinkSpecB
      p x y z q
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN) := by
  refine ⟨?_, ?_⟩
  · simpa using
      triominoWieferichShrinkNumsInvCandidate_hxmul_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  · simpa using
      triominoWieferichShrinkNumsInvCandidate_hy_eq_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/--
`_of_pack` backend の `hxMul` から `x' = x / q` を回収する。

以後はこの補題を `hxdiv` の正規供給路とし、gate の起動に使う。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hxdiv_via_trace_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' = x / q := by
  have hqpos : 0 < q := hqP.pos
  have hxmul :
      x =
        q *
          (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' := by
    exact
      triominoWieferichShrinkNumsInvCandidate_hxmul_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  calc
    (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      =
        (q *
          (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x') / q := by
        simpa [Nat.mul_comm] using
          (Nat.mul_div_right
            (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
              hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
            hqpos).symm
    _ = x / q := by
      simp [hxmul]

/--
次段の差し替え用に、`x' := x / q`, `y' := y` を先に固定した影候補。

`z'` はまだ `_of_pack` backend の値を流用し、`Eq/Spec` 側が新候補へ追随できるまで
公開 `CandidateB_kernel` は切り替えない。
-/
def triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkNumsInvCandidateB p x y z q := by
  let c : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidate_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact
    { x' := x / q
      y' := y
      z' := c.z' }

/-- 影候補では `x' = x / q` が definitionally fixed。 -/
@[simp] theorem triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_x
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' = x / q := by
  simp [triominoWieferichShrinkNumsInvCandidate_div_eq_shadow]

/-- 影候補では `y' = y` が definitionally fixed。 -/
@[simp] theorem triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_y
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = y := by
  simp [triominoWieferichShrinkNumsInvCandidate_div_eq_shadow]

/--
影候補では `z'` だけ `_of_pack` backend を流用する。

公開 kernel を差し替える前に、`hzlt / hpB' / Eq` の helper をこの値へ追随させる。
-/
@[simp] theorem triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_z
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z'
      =
    (triominoWieferichShrinkNumsInvCandidate_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  simp [triominoWieferichShrinkNumsInvCandidate_div_eq_shadow]

/--
`_of_pack` backend について `x' = x / q`, `y' = y` が示せれば、
影候補 `div_eq_shadow` と 3 フィールドが一致する。

構造体の等値そのものではなく fieldwise 一致に留め、差し替え前の安全確認に使う。
前提の `hxdiv / hy'` は現状の backend からはまだ自動では出ない。
-/
theorem triominoWieferichShrinkNumsInvCandidate_of_pack_shadow_fields_of_eq
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y)
    (hxdiv :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' = x / q)
    (hy' :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = y) :
    ((@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
        =
      (@triominoWieferichShrinkNumsInvCandidate_div_eq_shadow p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x')
    ∧
    ((@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
        =
      (@triominoWieferichShrinkNumsInvCandidate_div_eq_shadow p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y')
    ∧
    ((@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z'
        =
      (@triominoWieferichShrinkNumsInvCandidate_div_eq_shadow p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z') := by
  constructor
  · exact hxdiv.trans
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_x
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).symm
  constructor
  · exact hy'.trans
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_y
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).symm
  · exact
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_z
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).symm

/--
trace から `hxdiv / hy'` を供給して、`_of_pack` backend と shadow 候補の field 一致を起動する。

`EqCore` と `Spec` の両方で使うため、assumptions-free な helper に束ねる。
-/
theorem triominoWieferichShrinkNumsInvCandidate_of_pack_shadow_fields_of_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    ((@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
        =
      (@triominoWieferichShrinkNumsInvCandidate_div_eq_shadow p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x')
    ∧
    ((@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
        =
      (@triominoWieferichShrinkNumsInvCandidate_div_eq_shadow p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y')
    ∧
    ((@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z'
        =
      (@triominoWieferichShrinkNumsInvCandidate_div_eq_shadow p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z') := by
  have hxdiv :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' = x / q := by
    exact
      triominoWieferichShrinkNumsInvCandidate_hxdiv_via_trace_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hy' :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = y := by
    exact
      triominoWieferichShrinkNumsInvCandidate_hy_eq_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact
    triominoWieferichShrinkNumsInvCandidate_of_pack_shadow_fields_of_eq
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN hxdiv hy'

/--
独立実装へ差し替えるための数値候補 kernel。

現時点では shadow 候補
`x' := x / q`, `y' := y`, `z' := backend z'`
を公開 kernel として採用する。
-/
def triominoWieferichShrinkNumsInvCandidateB_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
  triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
    (p := p) (x := x) (y := y) (z := z) (q := q)
    hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/-- public `CandidateB_kernel` 用の link 仕様。shadow kernel では算術と定義展開で供給する。 -/
theorem triominoWieferichShrinkNumsInvCandidateLinkSpec_of_kernel
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkNumsInvCandidateLinkSpecB p x y z q
      (@triominoWieferichShrinkNumsInvCandidateB_kernel p x y z q
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN) := by
  refine ⟨?_, ?_⟩
  · calc
      x = q * (x / q) := by
        exact
          triominoWieferichShrink_x_eq_q_mul_div_core
            (p := p) (x := x) (y := y) (z := z) (q := q)
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
      _ =
          q *
            (@triominoWieferichShrinkNumsInvCandidateB_kernel p x y z q
              hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' := by
        simp [triominoWieferichShrinkNumsInvCandidateB_kernel,
          triominoWieferichShrinkNumsInvCandidate_div_eq_shadow]
  · simp [triominoWieferichShrinkNumsInvCandidateB_kernel,
      triominoWieferichShrinkNumsInvCandidate_div_eq_shadow]

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
  let n : TriominoWieferichShrinkKernelNumsB p x y z q :=
    triominoWieferichShrinkKernelNums_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hEqb :
      n.x' ^ p + n.y' ^ p = n.z' ^ p := by
    exact
      (triominoWieferichShrinkKernelEq_of_nums_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).hEq'
  have hfields :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' =
        c.x'
      ∧
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' =
        c.y'
      ∧
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' =
        c.z' := by
    simpa [c, triominoWieferichShrinkNumsInvCandidateB_kernel] using
      triominoWieferichShrinkNumsInvCandidate_of_pack_shadow_fields_of_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  rcases hfields with ⟨hx, hy, hz⟩
  have hEq' : c.x' ^ p + c.y' ^ p = c.z' ^ p := by
    rw [← hz, ← hy, ← hx]
    simpa [n, triominoWieferichShrinkKernelNums_of_pack] using hEqb
  have hL :
      TriominoWieferichShrinkNumsInvCandidateLinkSpecB p x y z q c :=
    triominoWieferichShrinkNumsInvCandidateLinkSpec_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hx0' : c.x' ≠ 0 := by
    intro hx0
    apply hpack.hx0
    calc
      x = q * c.x' := hL.hxMul
      _ = 0 := by simp [hx0]
  exact
    triominoWieferichShrinkWitnessEq_of_eq_and_hx0
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hx0' hEq'

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
  let cs : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let hL :
      TriominoWieferichShrinkNumsInvCandidateLinkSpecB
        p x y z q
        (triominoWieferichShrinkNumsInvCandidateB_kernel
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN) :=
    triominoWieferichShrinkNumsInvCandidateLinkSpec_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hEq' : c.x' ^ p + c.y' ^ p = c.z' ^ p := by
    have hEq_shadow :
        cs.x' ^ p + cs.y' ^ p = cs.z' ^ p := by
      have hEqb :
          (triominoWieferichShrinkKernelNums_of_pack
            (p := p) (x := x) (y := y) (z := z) (q := q)
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' ^ p
            +
            (triominoWieferichShrinkKernelNums_of_pack
              (p := p) (x := x) (y := y) (z := z) (q := q)
              hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' ^ p
            =
            (triominoWieferichShrinkKernelNums_of_pack
              (p := p) (x := x) (y := y) (z := z) (q := q)
              hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' ^ p := by
        exact
          (triominoWieferichShrinkKernelEq_of_nums_of_pack
            (p := p) (x := x) (y := y) (z := z) (q := q)
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).hEq'
      have hfields :
          (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
              hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' = cs.x'
            ∧
          (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
              hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = cs.y'
            ∧
          (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
              hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' = cs.z' := by
        exact
          triominoWieferichShrinkNumsInvCandidate_of_pack_shadow_fields_of_kernel
            (p := p) (x := x) (y := y) (z := z) (q := q)
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
      rcases hfields with ⟨hx, hy, hz⟩
      rw [← hz, ← hy, ← hx]
      simpa [triominoWieferichShrinkKernelNums_of_pack] using hEqb
    simpa [c, triominoWieferichShrinkNumsInvCandidateB_kernel] using hEq_shadow
  have hx0' : c.x' ≠ 0 := by
    intro hx0
    apply hpack.hx0
    calc
      x = q * c.x' := hL.hxMul
      _ = 0 := by simp [hx0]
  exact
    triominoWieferichShrinkWitnessEq_of_eq_and_hx0
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hx0' hEq'

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
  exact
    triominoWieferichShrink_q_dvd_x_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

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
`q ∣ z` は primitive 条件 `q ∤ (z - y)` と両立しない。

候補 A `z' := z / q` を先に試す際の失敗理由を補題化しておく。
-/
theorem triominoWieferichShrink_q_not_dvd_z
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    ¬ q ∣ z := by
  intro hq_dvd_z
  have hq_dvd_x : q ∣ x :=
    triominoWieferichShrink_q_dvd_x
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hp_pos : 0 < p := hpack.hp.pos
  have hq_dvd_qpow : q ∣ q ^ p := dvd_pow_self _ hp_pos.ne'
  have hqpow_dvd_xpow : q ^ p ∣ x ^ p := by
    exact pow_dvd_pow_of_dvd hq_dvd_x p
  have hq_dvd_xpow : q ∣ x ^ p := dvd_trans hq_dvd_qpow hqpow_dvd_xpow
  have hqpow_dvd_zpow : q ^ p ∣ z ^ p := by
    exact pow_dvd_pow_of_dvd hq_dvd_z p
  have hq_dvd_zpow : q ∣ z ^ p := dvd_trans hq_dvd_qpow hqpow_dvd_zpow
  have hq_dvd_ypow : q ∣ y ^ p := by
    have hq_dvd_sum : q ∣ x ^ p + y ^ p := by
      simpa [hpack.hEq] using hq_dvd_zpow
    have hq_dvd_sub : q ∣ (x ^ p + y ^ p) - x ^ p := by
      exact Nat.dvd_sub hq_dvd_sum hq_dvd_xpow
    simpa [Nat.add_sub_cancel_left] using hq_dvd_sub
  have hq_dvd_y : q ∣ y := hqP.dvd_of_dvd_pow hq_dvd_ypow
  exact hq_not_dvd_gap (Nat.dvd_sub hq_dvd_z hq_dvd_y)

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

/--
`z - y = k * (z' - y')` が分かれば、元の Branch B 条件を移送できる。

係数 `k` に条件は要らず、`p ∣ (z' - y')` なら自動的に `p ∣ k * (z' - y')` となる。
-/
theorem triominoWieferichShrink_hpB'_of_eq_mul_gap
    {p y z y' z' k : ℕ}
    (hpB : ¬ p ∣ (z - y))
    (hgap : z - y = k * (z' - y')) :
    ¬ p ∣ (z' - y') := by
  intro hpB'
  have hdiv : p ∣ k * (z' - y') := dvd_mul_of_dvd_right hpB' k
  apply hpB
  simpa [hgap] using hdiv

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
公開 `CandidateB_kernel` に対して `z - y = k * (z' - y')` が示せれば、
`hpB'` を回収できる。

将来 gap 保存ではなく「一定係数で縮む gap」を採る時の独立ルートとして使う。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hpB'_of_eq_mul_core
    {p x y z q k : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y)
    (hgap :
      z - y =
        k *
          ((triominoWieferichShrinkNumsInvCandidateB_kernel
              (p := p) (x := x) (y := y) (z := z) (q := q)
              hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' -
            (triominoWieferichShrinkNumsInvCandidateB_kernel
              (p := p) (x := x) (y := y) (z := z) (q := q)
              hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y')) :
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
  exact triominoWieferichShrink_hpB'_of_eq_mul_gap hpB hgap

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
  let r0 : TriominoWieferichShrinkNumsInvRecipeB p x y z q :=
    triominoWieferichShrinkNumsInvRecipe_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hz :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z'
        =
      (@triominoWieferichShrinkNumsInvCandidate_div_eq_shadow p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
    exact
      (triominoWieferichShrinkNumsInvCandidate_of_pack_shadow_fields_of_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).2.2
  have hzlt_pack :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' < z := by
    simpa [triominoWieferichShrinkNumsInvCandidate_of_pack, r0] using r0.hzlt
  have hzlt_shadow :
      (@triominoWieferichShrinkNumsInvCandidate_div_eq_shadow p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' < z := by
    rw [← hz]
    exact hzlt_pack
  change
    (@triominoWieferichShrinkNumsInvCandidate_div_eq_shadow p x y z q
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' < z
  exact hzlt_shadow

/--
`Spec_of_kernel` 用に `hzlt` を回収する公開 core helper。

shadow-first に `_of_pack` backend の `< z` を運び、最後に current kernel へ寄せる。
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
  let cs : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let r0 : TriominoWieferichShrinkNumsInvRecipeB p x y z q :=
    triominoWieferichShrinkNumsInvRecipe_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hzlt_pack :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' < z := by
    simpa [triominoWieferichShrinkNumsInvCandidate_of_pack, r0] using r0.hzlt
  have hfields :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' = cs.x'
        ∧
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = cs.y'
        ∧
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' = cs.z' := by
    exact
      triominoWieferichShrinkNumsInvCandidate_of_pack_shadow_fields_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  rcases hfields with ⟨_, ⟨_, hz⟩⟩
  have hzc : c.z' = cs.z' := by
    rfl
  have hzlt_shadow : cs.z' < z := by
    simpa [hz] using hzlt_pack
  simpa [hzc] using hzlt_shadow

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
  let r0 : TriominoWieferichShrinkNumsInvRecipeB p x y z q :=
    triominoWieferichShrinkNumsInvRecipe_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hfields :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' =
        (@triominoWieferichShrinkNumsInvCandidate_div_eq_shadow p x y z q
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      ∧
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' =
        (@triominoWieferichShrinkNumsInvCandidate_div_eq_shadow p x y z q
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      ∧
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' =
        (@triominoWieferichShrinkNumsInvCandidate_div_eq_shadow p x y z q
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
    exact
      triominoWieferichShrinkNumsInvCandidate_of_pack_shadow_fields_of_kernel
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  rcases hfields with ⟨_, ⟨hy, hz⟩⟩
  have hpB'_pack :
      ¬ p ∣
        ((@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' -
          (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y') := by
    simpa [triominoWieferichShrinkNumsInvCandidate_of_pack, r0] using r0.hpB'
  have hpB'_shadow :
      ¬ p ∣
        ((@triominoWieferichShrinkNumsInvCandidate_div_eq_shadow p x y z q
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' -
          (@triominoWieferichShrinkNumsInvCandidate_div_eq_shadow p x y z q
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y') := by
    rw [← hz, ← hy]
    exact hpB'_pack
  change
    ¬ p ∣
      ((@triominoWieferichShrinkNumsInvCandidate_div_eq_shadow p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' -
        (@triominoWieferichShrinkNumsInvCandidate_div_eq_shadow p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y')
  exact hpB'_shadow

/--
`Spec_of_kernel` 用に `hpB'` を回収する公開 core helper。

shadow-first に `_of_pack` backend の `hpB'` を運び、最後に current kernel へ寄せる。
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
  let cs : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let r0 : TriominoWieferichShrinkNumsInvRecipeB p x y z q :=
    triominoWieferichShrinkNumsInvRecipe_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hpB'_pack :
      ¬ p ∣
        ((@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' -
          (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y') := by
    simpa [triominoWieferichShrinkNumsInvCandidate_of_pack, r0] using r0.hpB'
  have hfields :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' = cs.x'
        ∧
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = cs.y'
        ∧
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' = cs.z' := by
    exact
      triominoWieferichShrinkNumsInvCandidate_of_pack_shadow_fields_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  rcases hfields with ⟨_, ⟨hy, hz⟩⟩
  have hyc : c.y' = cs.y' := by
    rfl
  have hzc : c.z' = cs.z' := by
    rfl
  have hpB'_shadow : ¬ p ∣ (cs.z' - cs.y') := by
    simpa [hy, hz] using hpB'_pack
  intro hp_div
  have hp_div_c : p ∣ (c.z' - c.y') := by
    simpa [c] using hp_div
  have hp_div_shadow : p ∣ (cs.z' - cs.y') := by
    simpa [hyc, hzc] using hp_div_c
  apply hpB'_shadow
  exact hp_div_shadow

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
  let hL :
      TriominoWieferichShrinkNumsInvCandidateLinkSpecB p x y z q c :=
    triominoWieferichShrinkNumsInvCandidateLinkSpec_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  refine (Nat.coprime_iff_gcd_eq_one).2 ?_
  by_contra hg1
  have hg_ne1 : Nat.gcd c.x' c.y' ≠ 1 := by simpa [c] using hg1
  rcases Nat.exists_prime_and_dvd (n := Nat.gcd c.x' c.y') hg_ne1 with ⟨d, hdP, hd_dvd_g⟩
  have hd_dvd_x' : d ∣ c.x' := dvd_trans hd_dvd_g (Nat.gcd_dvd_left c.x' c.y')
  have hd_dvd_y' : d ∣ c.y' := dvd_trans hd_dvd_g (Nat.gcd_dvd_right c.x' c.y')
  have hd_dvd_x : d ∣ x := by
    have hd_dvd_rhs : d ∣ q * c.x' := dvd_mul_of_dvd_right hd_dvd_x' q
    simpa [hL.hxMul] using hd_dvd_rhs
  have hd_dvd_y : d ∣ y := by
    simpa [hL.hyEq] using hd_dvd_y'
  exact (Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt hdP) hd_dvd_x hd_dvd_y) hpack.hxy

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
影候補 `div_eq_shadow` では `y' = y` が definitionally 固定されているので、
`hy0'` は独立ルートで即座に回収できる。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hy0_shadow_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' ≠ 0 := by
  have hy' :
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = y := by
    simp [triominoWieferichShrinkNumsInvCandidate_div_eq_shadow]
  exact
    triominoWieferichShrink_hy0_of_eq_y
      (p := p) (x := x) (y := y) (z := z) hpack hy'

/--
影候補 `div_eq_shadow` では `x' = x / q` が definitionally 固定されているので、
`q ∣ x` から `hx0'` を独立ルートで回収できる。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hx0_shadow_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' ≠ 0 := by
  have hxq : q ∣ x :=
    triominoWieferichShrink_q_dvd_x
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hxdiv :
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' = x / q := by
    simp [triominoWieferichShrinkNumsInvCandidate_div_eq_shadow]
  have hxmul :
      x =
        q *
          (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
            (p := p) (x := x) (y := y) (z := z) (q := q)
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' := by
    calc
      x = q * (x / q) := by
        simpa using (Nat.mul_div_cancel' hxq).symm
      _ =
          q *
            (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
              (p := p) (x := x) (y := y) (z := z) (q := q)
              hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' := by
        simp
  exact
    triominoWieferichShrink_hx0_of_eq_mul_right
      (x := x) (q := q)
      (x' :=
        (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x')
      hpack.hx0 hxmul

/--
影候補 `div_eq_shadow` では `x' = x / q`, `y' = y` が definitionally 固定されているので、
`Nat.Coprime x' y'` も独立ルートで回収できる。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hxy_shadow_core
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    Nat.Coprime
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' := by
  have hxq : q ∣ x :=
    triominoWieferichShrink_q_dvd_x
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hxdiv :
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' = x / q := by
    simp [triominoWieferichShrinkNumsInvCandidate_div_eq_shadow]
  have hy' :
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = y := by
    simp [triominoWieferichShrinkNumsInvCandidate_div_eq_shadow]
  have hxmul :
      x =
        q *
          (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
            (p := p) (x := x) (y := y) (z := z) (q := q)
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' := by
    calc
      x = q * (x / q) := by
        simpa using (Nat.mul_div_cancel' hxq).symm
      _ =
          q *
            (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
              (p := p) (x := x) (y := y) (z := z) (q := q)
              hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' := by
        simp
  exact
    triominoWieferichShrink_hxy_of_eq_mul_eq_y
      (x := x) (y := y) (q := q)
      (x' :=
        (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x')
      (y' :=
        (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y')
      hpack.hxy hxmul hy'

/--
gate 付き：backend の `hEq'` を shadow triple へ運ぶ。

現時点では `_of_pack` backend の `x' / y'` は opaque なので、
`hxdiv / hy'` を仮定として受け、fieldwise gate で shadow 側へ rewrite する。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hEq_shadow_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y)
    (hxdiv :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' = x / q)
    (hy' :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = y) :
    (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' ^ p
      +
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' ^ p
      =
    (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' ^ p := by
  let _ := hxdiv
  let _ := hy'
  simpa [triominoWieferichShrinkNumsInvCandidateB_kernel] using
    triominoWieferichShrinkNumsInvCandidate_hEq_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN

/--
gate 付き：shadow triple 用の `Eq` witness。

`hxdiv / hy'` が供給できれば、backend の `hEq'` を shadow 側へ運び、
`hx0'` は shadow 独立ルートで回収して `Eq` witness を完成できる。
-/
theorem triominoWieferichShrinkNumsInvCandidateEq_shadow_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y)
    (hxdiv :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' = x / q)
    (hy' :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = y) :
    TriominoWieferichShrinkWitnessEqB
      p x y z q
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  have hx0' :
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' ≠ 0 := by
    simpa using
      triominoWieferichShrinkNumsInvCandidate_hx0_shadow_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hEq' :
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' ^ p
      +
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' ^ p
      =
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' ^ p := by
    exact
      triominoWieferichShrinkNumsInvCandidate_hEq_shadow_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN hxdiv hy'
  exact
    triominoWieferichShrinkWitnessEq_of_eq_and_hx0
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hx0' hEq'

/--
trace から `hxdiv / hy'` を供給して、shadow triple の `hEq'` を起動する。

gate 付き shadow `Eq` への assumptions-free な正規ルート。
-/
theorem triominoWieferichShrinkNumsInvCandidate_hEq_shadow_via_trace_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' ^ p
      +
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' ^ p
      =
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' ^ p := by
  have hxdiv :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' = x / q := by
    exact
      triominoWieferichShrinkNumsInvCandidate_hxdiv_via_trace_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hy' :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = y := by
    exact
      triominoWieferichShrinkNumsInvCandidate_hy_eq_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact
    triominoWieferichShrinkNumsInvCandidate_hEq_shadow_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN hxdiv hy'

/--
trace から `hxdiv / hy'` を供給して、shadow triple の `Eq` witness を起動する。

public kernel 差し替え前に、shadow `Eq` の可動性を保証するための正規ルート。
-/
theorem triominoWieferichShrinkNumsInvCandidateEq_shadow_via_trace_of_pack
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    TriominoWieferichShrinkWitnessEqB
      p x y z q
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x'
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y'
      (triominoWieferichShrinkNumsInvCandidate_div_eq_shadow
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
  have hxdiv :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' = x / q := by
    exact
      triominoWieferichShrinkNumsInvCandidate_hxdiv_via_trace_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hy' :
      (@triominoWieferichShrinkNumsInvCandidate_of_pack p x y z q
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = y := by
    exact
      triominoWieferichShrinkNumsInvCandidate_hy_eq_of_pack
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact
    triominoWieferichShrinkNumsInvCandidateEq_shadow_of_pack
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN hxdiv hy'

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
  let hL :
      TriominoWieferichShrinkNumsInvCandidateLinkSpecB
        p x y z q
        (triominoWieferichShrinkNumsInvCandidateB_kernel
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN) :=
    triominoWieferichShrinkNumsInvCandidateLinkSpec_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact
    triominoWieferichShrinkNumsInvCandidate_hxy_of_eq_mul_eq_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
      hL.hxMul hL.hyEq

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
  let hL :
      TriominoWieferichShrinkNumsInvCandidateLinkSpecB
        p x y z q
        (triominoWieferichShrinkNumsInvCandidateB_kernel
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN) :=
    triominoWieferichShrinkNumsInvCandidateLinkSpec_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  intro hx0
  apply hpack.hx0
  calc
    x = q *
          (triominoWieferichShrinkNumsInvCandidateB_kernel
            (p := p) (x := x) (y := y) (z := z) (q := q)
            hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' := hL.hxMul
    _ = 0 := by simp [hx0]

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
  let hL :
      TriominoWieferichShrinkNumsInvCandidateLinkSpecB
        p x y z q
        (triominoWieferichShrinkNumsInvCandidateB_kernel
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN) :=
    triominoWieferichShrinkNumsInvCandidateLinkSpec_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact
    triominoWieferichShrinkNumsInvCandidate_hx0_of_eq_mul_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
      hL.hxMul

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
  let hL :
      TriominoWieferichShrinkNumsInvCandidateLinkSpecB
        p x y z q
        (triominoWieferichShrinkNumsInvCandidateB_kernel
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN) :=
    triominoWieferichShrinkNumsInvCandidateLinkSpec_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa [hL.hyEq] using hpack.hy0

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
  let hL :
      TriominoWieferichShrinkNumsInvCandidateLinkSpecB
        p x y z q
        (triominoWieferichShrinkNumsInvCandidateB_kernel
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN) :=
    triominoWieferichShrinkNumsInvCandidateLinkSpec_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  exact
    triominoWieferichShrinkNumsInvCandidate_hy0_of_eq_core
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
      hL.hyEq

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
  have hx0' : c.x' ≠ 0 := by
    simpa [c] using
      triominoWieferichShrinkNumsInvCandidate_hx0_core
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hEq :
      TriominoWieferichShrinkWitnessEqB p x y z q c.x' c.y' c.z' := by
    exact
      triominoWieferichShrinkWitnessEq_of_eq_and_hx0
        (p := p) (x := x) (y := y) (z := z) (q := q)
        hx0' hEq'
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
  let cand : TriominoWieferichShrinkNumsInvCandidateB p x y z q :=
    triominoWieferichShrinkNumsInvCandidateB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  let hL :
      TriominoWieferichShrinkNumsInvCandidateLinkSpecB p x y z q cand :=
    triominoWieferichShrinkNumsInvCandidateLinkSpec_of_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  have hxMul : x = q * n.x' := by
    simpa
        [triominoWieferichShrinkKernelNumsCoreB_kernel,
          triominoWieferichShrinkNumsInvCoreB_kernel,
          TriominoWieferichShrinkNumsInvRecipeB.toCore,
          TriominoWieferichShrinkNumsInvRecipeB.toNums,
          triominoWieferichShrinkNumsInvRecipeB_kernel, cand, n]
      using hL.hxMul
  have hyEq : n.y' = y := by
    simpa
        [triominoWieferichShrinkKernelNumsCoreB_kernel,
          triominoWieferichShrinkNumsInvCoreB_kernel,
          TriominoWieferichShrinkNumsInvRecipeB.toCore,
          TriominoWieferichShrinkNumsInvRecipeB.toNums,
          triominoWieferichShrinkNumsInvRecipeB_kernel, cand, n]
      using hL.hyEq
  exact ⟨⟨n, hEq⟩, hInv, hxMul, hyEq⟩

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
  have hxMul : x = q * s.n.x' := by
    simpa [TriominoWieferichShrinkKernelCoreB.toSeed, c, s] using c.hxMul
  have hyEq : s.n.y' = y := by
    simpa [TriominoWieferichShrinkKernelCoreB.toSeed, c, s] using c.hyEq
  exact ⟨s, hInv, hxMul, hyEq⟩

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

/-- current-path から `x = q * x'` を回収する投影版。 -/
theorem triominoWieferichShrinkKernel_hxmul_of_core_path
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    x =
      q *
        (triominoWieferichShrinkKernelNumsB_kernel
          (p := p) (x := x) (y := y) (z := z) (q := q)
          hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' := by
  let c : TriominoWieferichShrinkKernelCoreB p x y z q :=
    triominoWieferichShrinkKernelCoreB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa
      [triominoWieferichShrinkKernelNumsB_kernel,
        triominoWieferichShrinkKernelSeedB_kernel,
        triominoWieferichShrinkKernelEqSeedB_kernel,
        triominoWieferichShrinkKernelEqSeedCoreB_kernel,
        triominoWieferichShrinkKernelEqSeedTraceB_kernel,
        TriominoWieferichShrinkKernelCoreB.toSeed, c]
    using c.hxMul

/-- current-path から `y' = y` を回収する投影版。 -/
theorem triominoWieferichShrinkKernel_hy_eq_of_core_path
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hpB : ¬ p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hq_not_dvd_gap : ¬ q ∣ (z - y))
    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
    (triominoWieferichShrinkKernelNumsB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' = y := by
  let c : TriominoWieferichShrinkKernelCoreB p x y z q :=
    triominoWieferichShrinkKernelCoreB_kernel
      (p := p) (x := x) (y := y) (z := z) (q := q)
      hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
  simpa
      [triominoWieferichShrinkKernelNumsB_kernel,
        triominoWieferichShrinkKernelSeedB_kernel,
        triominoWieferichShrinkKernelEqSeedB_kernel,
        triominoWieferichShrinkKernelEqSeedCoreB_kernel,
        triominoWieferichShrinkKernelEqSeedTraceB_kernel,
        TriominoWieferichShrinkKernelCoreB.toSeed, c]
    using c.hyEq

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
