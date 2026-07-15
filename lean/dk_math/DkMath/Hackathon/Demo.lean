/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Hackathon.FinitePrimeEscape
import DkMath.Hackathon.CosmicCompletion

namespace DkMath.Hackathon

open scoped BigOperators

/-- The fixed finite prime reference set used by the public demonstration. -/
def demoPrimeSet : Finset ℕ := {2, 3, 5, 7}

/-- The product of the fixed finite prime reference set. -/
def demoP : ℕ := 210

/-- The fixed coprime completion offset. -/
def demoU : ℕ := 11

/-- The fixed completed boundary `demoP + demoU`. -/
def demoBoundary : ℕ := 221

theorem demo_product :
    ∏ p ∈ demoPrimeSet, p = demoP := by
  norm_num [demoPrimeSet, demoP]

theorem demo_coprime :
    Nat.Coprime demoP demoU := by
  norm_num [demoP, demoU, Nat.Coprime]

theorem demo_boundary :
    demoP + demoU = demoBoundary := by
  norm_num [demoP, demoU, demoBoundary]

theorem demo_factorization :
    demoBoundary = 13 * 17 := by
  norm_num [demoBoundary]

theorem demo_thirteen_prime :
    Nat.Prime 13 := by
  norm_num

theorem demo_seventeen_prime :
    Nat.Prime 17 := by
  norm_num

theorem demo_thirteen_fresh :
    FreshPrimeFactor demoPrimeSet demoBoundary 13 := by
  refine ⟨demo_thirteen_prime, by norm_num [demoBoundary], ?_⟩
  apply prime_dvd_product_add_coprime_not_mem
      (S := demoPrimeSet) (u := demoU)
  · norm_num [demoPrimeSet, demoU, Nat.Coprime]
  · exact demo_thirteen_prime
  · norm_num [demoPrimeSet, demoU]

theorem demo_seventeen_fresh :
    FreshPrimeFactor demoPrimeSet demoBoundary 17 := by
  refine ⟨demo_seventeen_prime, by norm_num [demoBoundary], ?_⟩
  apply prime_dvd_product_add_coprime_not_mem
      (S := demoPrimeSet) (u := demoU)
  · norm_num [demoPrimeSet, demoU, Nat.Coprime]
  · exact demo_seventeen_prime
  · norm_num [demoPrimeSet, demoU]

theorem demo_cosmic_completion :
    demoP * (demoP + 2 * demoU) + demoU ^ 2 =
      (demoP + demoU) ^ 2 := by
  exact cosmicCompletion demoP demoU

end DkMath.Hackathon
