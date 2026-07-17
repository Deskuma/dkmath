/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Hackathon.FinitePrimeEscape
import DkMath.NumberTheory.PrimitiveBeamExamples

namespace DkMath.Hackathon

open scoped BigOperators

/-- The finite-prime escape boundary for `{2, 3, 5}` lands on `GN 5 1 1`. -/
theorem finitePrimeEscape_hits_GN5 :
    ∃ q,
      FreshPrimeFactor
        ({2, 3, 5} : Finset ℕ)
        (DkMath.CosmicFormulaBinom.GN 5 1 1)
        q := by
  have hEscape := exists_fresh_prime_factor
    (S := ({2, 3, 5} : Finset ℕ))
    (u := 1)
    (by decide)
    (by decide)
  simpa using hEscape

/-- The only prime factor reached by the concrete `GN 5 1 1 = 31` escape is `31`. -/
theorem freshPrimeFactor_GN5_eq_31
    {q : ℕ}
    (hq : FreshPrimeFactor
      ({2, 3, 5} : Finset ℕ)
      (DkMath.CosmicFormulaBinom.GN 5 1 1)
      q) :
    q = 31 := by
  have hqDiv : q ∣ 31 := by
    simpa using hq.2.1
  exact (Nat.dvd_prime (by decide)).mp hqDiv |>.resolve_left hq.1.ne_one

/--
The escaped prime is a clean local channel: it divides `GN 5 1 1`, lies
outside the starting finite prime world, and does not lift to its square.
-/
theorem finitePrimeEscape_hits_clean_GN5_channel :
    ∃ q,
      Nat.Prime q ∧
      q ∣ DkMath.CosmicFormulaBinom.GN 5 1 1 ∧
      q ∉ ({2, 3, 5} : Finset ℕ) ∧
      ¬ q ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 5 1 1 := by
  obtain ⟨q, hq⟩ := finitePrimeEscape_hits_GN5
  have hqEq : q = 31 := freshPrimeFactor_GN5_eq_31 hq
  subst q
  exact ⟨hq.1, hq.2.1, hq.2.2, by decide⟩

/--
A prime channel which occurs without a square lift obstructs every power of
exponent at least two.
-/
theorem not_pow_of_prime_dvd_of_not_sq_dvd
    {N q x d : ℕ}
    (hqPrime : Nat.Prime q)
    (hqDiv : q ∣ N)
    (hqNoLift : ¬ q ^ 2 ∣ N)
    (hd : 2 ≤ d) :
    N ≠ x ^ d := by
  intro hN
  have hqDivPow : q ∣ x ^ d := by simpa [hN] using hqDiv
  have hqDivX : q ∣ x := hqPrime.dvd_of_dvd_pow hqDivPow
  obtain ⟨k, rfl⟩ := hqDivX
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
  apply hqNoLift
  rw [hN]
  use q ^ e * k ^ (2 + e)
  rw [Nat.mul_pow, pow_add]
  ring

/-- A local no-lift prime channel prevents a natural number from being a fifth power. -/
theorem not_fifth_power_of_prime_dvd_of_not_sq_dvd
    {N q : ℕ}
    (hqPrime : Nat.Prime q)
    (hqDiv : q ∣ N)
    (hqNoLift : ¬ q ^ 2 ∣ N) :
    ¬ ∃ x : ℕ, N = x ^ 5 := by
  rintro ⟨x, hx⟩
  exact not_pow_of_prime_dvd_of_not_sq_dvd hqPrime hqDiv hqNoLift (by decide) hx

/-- The concrete GN5 escape target cannot be a perfect fifth power. -/
theorem GN_five_one_one_not_fifth_power :
    ¬ ∃ x : ℕ,
      DkMath.CosmicFormulaBinom.GN 5 1 1 = x ^ 5 := by
  obtain ⟨q, hqPrime, hqDiv, _, hqNoLift⟩ :=
    finitePrimeEscape_hits_clean_GN5_channel
  exact not_fifth_power_of_prime_dvd_of_not_sq_dvd hqPrime hqDiv hqNoLift

end DkMath.Hackathon
