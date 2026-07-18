/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.BranchB

#print "file: DkMath.FLT.Five.Provider"

namespace DkMath.FLT.Five

/-- A Branch-B counterexample receives at least one existential clean GN5 channel. -/
abbrev BranchBCleanGN5ChannelProvider : Prop :=
  ∀ {x y z : ℕ},
    CounterexamplePack x y z →
    ¬ 5 ∣ z - y →
    ∃ q : ℕ, CleanGN5Channel (z - y) y q

/-- Contract for the local Branch-B contradiction. -/
abbrev BranchBRefuter : Prop :=
  ∀ {x y z q : ℕ},
    CounterexamplePack x y z →
    CleanGN5Channel (z - y) y q →
    False

end DkMath.FLT.Five
