/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Five.BranchB

#print "file: DkMath.FLT.Five.Provider"

namespace DkMath.FLT.Five

/-!
# Conditional clean-channel interfaces

These declarations separate the elementary local contradiction from the problem of
supplying a suitable prime.  They remain useful public interfaces, although the final
unconditional FLT5 route proceeds through signed five-adic normalization and golden
descent rather than assuming a global clean-channel provider.
-/

/-- A Branch-B counterexample receives at least one existential clean GN5 channel. -/
abbrev BranchBCleanGN5ChannelProvider : Prop :=
  ∀ {x y z : ℕ},
    CounterexamplePack x y z →
    ¬ 5 ∣ z - y →
    ∃ q : ℕ, CleanGN5Channel (z - y) y q

/--
The unbundled inversion-escape kernel for Branch B.

This is the unbundled form of the local data: one prime enters `GN5`, avoids the gap,
and fails to lift to its square.  It is retained as a conditional reusable interface.
-/
abbrev BranchBNoLiftEscape : Prop :=
  ∀ {x y z : ℕ},
    CounterexamplePack x y z →
    ¬ 5 ∣ z - y →
    ∃ q : ℕ,
      Nat.Prime q ∧
      q ∣ GN5 (z - y) y ∧
      ¬ q ∣ z - y ∧
      ¬ q ^ 2 ∣ GN5 (z - y) y

/-- The unbundled no-lift escape is exactly sufficient to build the clean provider. -/
theorem branchBCleanGN5ChannelProvider_of_noLiftEscape
    (hEscape : BranchBNoLiftEscape) :
    BranchBCleanGN5ChannelProvider := by
  intro x y z hPack hBranch
  rcases hEscape hPack hBranch with ⟨q, hqPrime, hqGN, hqGap, hqNoLift⟩
  exact ⟨q, hqPrime, hqGN, hqGap, hqNoLift⟩

/-- Contract for the local Branch-B contradiction. -/
abbrev BranchBRefuter : Prop :=
  ∀ {x y z q : ℕ},
    CounterexamplePack x y z →
    CleanGN5Channel (z - y) y q →
    False

/-- The direct square-divisibility refuter closes Branch B once a provider exists. -/
theorem branchB_false_of_clean_provider_by_dvd
    (hProvider : BranchBCleanGN5ChannelProvider)
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  rcases hProvider hPack hBranch with ⟨q, hClean⟩
  exact counterexample_false_of_clean_GN5Channel_by_dvd hPack hClean

/-- The inversion no-lift escape therefore closes the whole Branch-B candidate. -/
theorem branchB_false_of_noLiftEscape_by_dvd
    (hEscape : BranchBNoLiftEscape)
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  exact branchB_false_of_clean_provider_by_dvd
    (branchBCleanGN5ChannelProvider_of_noLiftEscape hEscape) hPack hBranch

end DkMath.FLT.Five
