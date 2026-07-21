/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Hackathon.FinitePrimeEscapeGN5Certificate

namespace DkMath.Hackathon

/-- Demo certificate: `31` is prime. -/
theorem finitePrimeEscapeGN5Demo_prime : Nat.Prime 31 :=
  finitePrimeEscapeGN5Certificate.1

/-- Demo certificate: `31` divides the explicit GN target. -/
theorem finitePrimeEscapeGN5Demo_divides :
    31 ∣ DkMath.CosmicFormulaBinom.GN 5 1 1 :=
  finitePrimeEscapeGN5Certificate.2.1

/-- Demo certificate: the prime channel does not lift to its square. -/
theorem finitePrimeEscapeGN5Demo_noLift :
    ¬ 31 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 5 1 1 :=
  finitePrimeEscapeGN5Certificate.2.2.2.1

/-- Demo certificate: the explicit GN target is not a fifth power. -/
theorem finitePrimeEscapeGN5Demo_notFifthPower :
    ¬ ∃ x : ℕ,
      DkMath.CosmicFormulaBinom.GN 5 1 1 = x ^ 5 :=
  finitePrimeEscapeGN5Certificate.2.2.2.2

/-- The complete second-domain presentation certificate. -/
theorem finitePrimeEscapeGN5DemoCertificate :
    Nat.Prime 31 ∧
    31 ∣ DkMath.CosmicFormulaBinom.GN 5 1 1 ∧
    31 ∉ ({2, 3, 5} : Finset ℕ) ∧
    ¬ 31 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 5 1 1 ∧
    ¬ ∃ x : ℕ,
      DkMath.CosmicFormulaBinom.GN 5 1 1 = x ^ 5 :=
  finitePrimeEscapeGN5Certificate

end DkMath.Hackathon

#print "file: DkMath.Hackathon.FinitePrimeEscapeGN5Demo"
