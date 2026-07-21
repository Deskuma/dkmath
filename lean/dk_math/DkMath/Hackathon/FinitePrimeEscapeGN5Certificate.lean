/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Hackathon.FinitePrimeEscapeGN5

namespace DkMath.Hackathon

/--
Summit certificate for the explicit clean prime channel at `GN 5 1 1` and its
non-fifth-power consequence.
-/
theorem finitePrimeEscapeGN5Certificate :
    Nat.Prime 31 ∧
    31 ∣ DkMath.CosmicFormulaBinom.GN 5 1 1 ∧
    31 ∉ ({2, 3, 5} : Finset ℕ) ∧
    ¬ 31 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 5 1 1 ∧
    ¬ ∃ x : ℕ,
      DkMath.CosmicFormulaBinom.GN 5 1 1 = x ^ 5 := by
  obtain ⟨q, hqPrime, hqDiv, hqFresh, hqNoLift⟩ :=
    finitePrimeEscape_hits_clean_GN5_channel
  have hqEq : q = 31 :=
    freshPrimeFactor_GN5_eq_31 ⟨hqPrime, hqDiv, hqFresh⟩
  subst q
  exact ⟨hqPrime, hqDiv, hqFresh, hqNoLift,
    GN_five_one_one_not_fifth_power⟩

end DkMath.Hackathon

#print "file: DkMath.Hackathon.FinitePrimeEscapeGN5Certificate"
