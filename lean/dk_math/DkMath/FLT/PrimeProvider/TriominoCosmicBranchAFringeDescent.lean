/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestore

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmicBranchAFringeDescent"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

/--
干渉縞 bundle から smaller packet を得る目標。
-/
theorem branchA_smallerPacket_of_fringe
    (hPrim : PrimeGe5BranchAPrimitivePacketDescentTarget)
    {p x y z t s q : ℕ}
    (hBundle : BranchAInterferenceFringeBundle p x y z t s q) :
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z := by
  have hpack : PrimeGe5CounterexamplePack p x y z := hBundle.padic.pack
  exact hPrim
    hpack
    hBundle.padic.hp_dvd_gap
    hBundle.padic.hgap
    hBundle.padic.hsGN
    hBundle.padic.hsx
    hBundle.padic.hcop_ts
    hBundle.padic.hcop_ty
    hBundle.padic.hcop_sy
    hBundle.padic.hp_not_dvd_s
    hBundle.padic.hp_not_dvd_t

/--
smaller packet から再び干渉縞 bundle を構成する橋。
-/
theorem branchA_smallerFringe_of_smallerPacket
    {p : ℕ}
    {pkt' : PrimeGe5BranchANormalFormPacket p}
    (hp_not_dvd_t' : ¬ p ∣ pkt'.t)
    {q' : ℕ}
    (hqprime' : Nat.Prime q')
    (hqs' : q' ∣ pkt'.s)
    (hqt' : ¬ q' ∣ pkt'.t)
    (hcop_qy' : Nat.Coprime q' pkt'.y)
    (hq_ne_p' : q' ≠ p)
    (hData' : RestoreWitnessProperties p pkt'.x pkt'.y pkt'.z pkt'.t pkt'.s q') :
    BranchAInterferenceFringeBundle p pkt'.x pkt'.y pkt'.z pkt'.t pkt'.s q' := by
  exact branchAInterferenceFringeBundle_default
    pkt'.pack
    pkt'.hp_dvd_gap
    pkt'.hgap
    pkt'.hsGN
    pkt'.hsx
    hp_not_dvd_t'
    hqprime'
    hqs'
    hqt'
    hcop_qy'
    hq_ne_p'
    hData'

/--
smaller packet から witness q' を再取得する補題（bridge）。

付録:
- Step 1: distinguished prime q' の存在 (sorry: Fermat/Cyclotomic 経路)
- Step 2: `restore_witness_properties_default` で RestoreWitnessProperties を no-sorry 構成
-/
theorem branchA_restoreWitness_of_smallerPacket
    {p : ℕ}
    {pkt' : PrimeGe5BranchANormalFormPacket p}
    (hp_not_dvd_t' : ¬ p ∣ pkt'.t) :
    ∃ q' : ℕ,
      Nat.Prime q' ∧
      q' ∣ pkt'.s ∧
      ¬ q' ∣ pkt'.t ∧
      Nat.Coprime q' pkt'.y ∧
      q' ≠ p ∧
      RestoreWitnessProperties p pkt'.x pkt'.y pkt'.z pkt'.t pkt'.s q' := by
  -- Step 1: distinguished prime q' の存在証明（open kernel）
  -- pkt'.hsGN : GN p (pkt'.z - pkt'.y) pkt'.y = p * pkt'.s ^ p および ¬ p ∣ pkt'.t から、
  -- Zsigmondy/cyclotomic 経路で q' ∣ pkt'.s かつ ¬ q' ∣ pkt'.t なる素数 q' を取り出す。
  obtain ⟨q', hqprime', hqs', hqt', hcop_qy', hq_ne_p'⟩ :
      ∃ q' : ℕ,
        Nat.Prime q' ∧
        q' ∣ pkt'.s ∧
        ¬ q' ∣ pkt'.t ∧
        Nat.Coprime q' pkt'.y ∧
        q' ≠ p := by
    -- TODO: GN 側の cyclotomic/Zsigmondy distinguished prime existence
    -- 具体的には GN p (z-y) y = p * s^p と ¬ p ∤ t から s の素因数 q' で
    -- q' ≠ p, Coprime q' y, ¬ q' ∣ t を満たすものを取り出す。
    sorry
  -- Step 2: RestoreWitnessProperties を restore_witness_properties_default で構成（no sorry）
  exact ⟨q', hqprime', hqs', hqt', hcop_qy', hq_ne_p',
    restore_witness_properties_default
      pkt'.pack pkt'.hp_dvd_gap pkt'.hgap pkt'.hsGN pkt'.hsx
      hqprime' hqs' hqt' hcop_qy' hq_ne_p'⟩

/--
PrimitivePacketDescentTarget から降下した smaller packet において
`¬ p ∣ pkt'.t` が維持されることを要求する独立補題。

付録:
- `PrimeGe5BranchANormalFormPacket` はフィールドに `hp_not_dvd_t` を持たない。
- `PrimeGe5BranchAPrimitivePacketDescentTarget` の入力では `¬ p ∣ t` が仮定されるが、
  返す packet の `t'` フィールドへの継承は construct の具体経路によって保証される必要がある。
- Kummer/Zsigmondy による concrete descent では `¬ p ∣ t'` が保持されると期待されるが、
  現在の抽象 target 型ではこれを型から直接読み出せないため open kernel として置く。
- `branchA_wf_contradiction_on_z` の `hpt'` をこの補題へ委譲することで、
  本体の証明骨格を明確に保ちながらこのギャップを外部化する。
-/
theorem branchA_smallerPacket_p_not_dvd_t
    (hPrim : PrimeGe5BranchAPrimitivePacketDescentTarget)
    {p x y z t s q : ℕ}
    (hBundle : BranchAInterferenceFringeBundle p x y z t s q)
    {pkt' : PrimeGe5BranchANormalFormPacket p}
    (hlt : pkt'.z < z) :
    ¬ p ∣ pkt'.t := by
  -- TODO: PrimitivePacketDescentTarget の p ∤ t 前提が降下後 packet でも保持されることの証明。
  -- pkt' は hPrim を hBundle の各フィールドに適用した結果として出てくる packet であり、
  -- concrete realization (Kummer descent) では p ∤ t' が保持されることが知られているが、
  -- 現状の抽象 target 経由ではこれを型から直接導出できない open kernel である。
  sorry

/--
`z` に関する well-founded descent による矛盾導出。
-/
theorem branchA_wf_contradiction_on_z
    (hPrim : PrimeGe5BranchAPrimitivePacketDescentTarget)
    {p : ℕ} :
    ¬ ∃ x y z t s q : ℕ, BranchAInterferenceFringeBundle p x y z t s q := by
  classical
  intro hExists
  let P : ℕ → Prop := fun z =>
    ∃ x y t s q : ℕ, BranchAInterferenceFringeBundle p x y z t s q
  have hP : ∃ z : ℕ, P z := by
    rcases hExists with ⟨x, y, z, t, s, q, hB⟩
    exact ⟨z, ⟨x, y, t, s, q, hB⟩⟩
  let z0 : ℕ := Nat.find hP
  have hz0 : P z0 := Nat.find_spec hP
  rcases hz0 with ⟨x0, y0, t0, s0, q0, hB0⟩
  have hMin : ∀ z, P z → z0 ≤ z := by
    intro z hz
    exact Nat.find_min' hP hz
  -- smaller packet from fringe bundle
  rcases branchA_smallerPacket_of_fringe hPrim hB0 with ⟨pkt', hzp⟩
  -- `p ∤ pkt'.t` を独立補題 branchA_smallerPacket_p_not_dvd_t へ委譲
  have hpt' : ¬ p ∣ pkt'.t :=
    branchA_smallerPacket_p_not_dvd_t hPrim hB0 hzp
  rcases branchA_restoreWitness_of_smallerPacket (p := p) (pkt' := pkt') hpt' with
    ⟨q', hqprime', hqs', hqt', hcop_qy', hq_ne_p', hData'⟩
  have hB' : BranchAInterferenceFringeBundle p pkt'.x pkt'.y pkt'.z pkt'.t pkt'.s q' :=
    branchA_smallerFringe_of_smallerPacket (p := p) (pkt' := pkt') hpt' (q' := q')
      hqprime' hqs' hqt' hcop_qy' hq_ne_p' hData'
  have hP' : P pkt'.z := ⟨pkt'.x, pkt'.y, pkt'.t, pkt'.s, q', hB'⟩
  have hz0le : z0 ≤ pkt'.z := hMin pkt'.z hP'
  exact Nat.not_lt_of_ge hz0le hzp


/--
干渉縞矛盾 target の確定。
-/
theorem branchAFringeContradiction_of_descent
    (hPrim : PrimeGe5BranchAPrimitivePacketDescentTarget) :
    BranchAFringeContradictionTarget := by
  intro p x y z t s q hBundle
  have hNoInf : ¬ ∃ x y z t s q : ℕ, BranchAInterferenceFringeBundle p x y z t s q :=
    branchA_wf_contradiction_on_z (hPrim := hPrim) (p := p)
  have hExists : ∃ x y z t s q : ℕ, BranchAInterferenceFringeBundle p x y z t s q :=
    ⟨x, y, z, t, s, q, hBundle⟩
  exact hNoInf hExists

end DkMath.FLT
