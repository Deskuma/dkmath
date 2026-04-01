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
  -- TODO: 実装（存在性は Fermat/Cyclotomic 経路による）
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
  have hpt' : ¬ p ∣ pkt'.t := by
    -- TODO: `p ∤ t` を smaller packet で維持することを保証する lemma を適用
    sorry
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
