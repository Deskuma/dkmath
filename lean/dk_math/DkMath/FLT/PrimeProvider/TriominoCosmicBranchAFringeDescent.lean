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
    {p x y z t s q : ℕ}
    (hBundle : BranchAInterferenceFringeBundle p x y z t s q) :
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z := by
  -- TODO: 既存の降下ステップ + packet 生成ルートで構成・証明
  sorry

/--
smaller packet から再び干渉縞 bundle を構成する目標。
-/
theorem branchA_smallerFringe_of_smallerPacket
    {p : ℕ}
    {pkt' : PrimeGe5BranchANormalFormPacket p} :
    ∃ q' : ℕ, BranchAInterferenceFringeBundle p pkt'.x pkt'.y pkt'.z pkt'.t pkt'.s q' := by
  -- TODO: 既存 witness 生成・restoreProperties ルートで構成・証明
  sorry

/--
`z` に関する well-founded descent による矛盾導出。
-/
theorem branchA_wf_contradiction_on_z
    {p : ℕ} :
    ¬ ∃ x y z t s q : ℕ, BranchAInterferenceFringeBundle p x y z t s q := by
  -- TODO: branchA_smallerPacket_of_fringe + branchA_smallerFringe_of_smallerPacket
  -- を使って、`Nat.lt_wfRel` の無限降下を否定
  sorry

/--
干渉縞矛盾 target の確定。
-/
theorem branchAFringeContradiction_of_descent : BranchAFringeContradictionTarget := by
  intro p x y z t s q hBundle
  have hNoInf : ¬ ∃ x y z t s q : ℕ, BranchAInterferenceFringeBundle p x y z t s q :=
    branchA_wf_contradiction_on_z (p := p)
  have hExists : ∃ x y z t s q : ℕ, BranchAInterferenceFringeBundle p x y z t s q :=
    ⟨x, y, z, t, s, q, hBundle⟩
  exact hNoInf hExists

end DkMath.FLT
