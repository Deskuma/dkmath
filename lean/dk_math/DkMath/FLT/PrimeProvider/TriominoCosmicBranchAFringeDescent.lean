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
`z` に関する well-founded descent による矛盾導出。
-/
theorem branchA_wf_contradiction_on_z
    (hPrim : PrimeGe5BranchAPrimitivePacketDescentTarget)
    {p : ℕ} :
    ¬ ∃ x y z t s q : ℕ, BranchAInterferenceFringeBundle p x y z t s q := by
  -- TODO: branchA_smallerPacket_of_fringe + branchA_smallerFringe_of_smallerPacket
  -- を使って、`Nat.lt_wfRel` の無限降下を否定
  sorry

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
