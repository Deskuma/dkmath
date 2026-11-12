/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.ElevenThirteenFLT

#print "file: DkMathTest.FLT.Kummer.PhaseRigidityFLT"

/-! 任意宇宙の係数 API、必要な例外、および標準 FLT 終点の回帰検査。 -/

namespace PhaseRigidityFLTTest

open DkMath.Lib.NumberTheory DkMath.FLT.Kummer
open scoped NumberField

section ArbitraryUniverse
variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

-- The modulus is arbitrary, including zero; this is stronger than reduction mod p.
example (f : Fin p → ℤ) (m : ℤ) :
    (m : 𝓞 K) ∣ ∑ i, f i • hζ.toInteger ^ (i : ℕ) ↔
      ∀ i j, m ∣ f i - f j :=
  phase_sum_dvd_iff hp.out hζ.toInteger_isPrimitiveRoot f m

example (f : Fin p → ℤ) :
    (∑ i, f i • hζ.toInteger ^ (i : ℕ)) = 0 ↔ ∀ i j, f i = f j := by
  simpa only [Int.cast_zero, zero_dvd_iff, sub_eq_zero] using
    phase_sum_dvd_iff hp.out hζ.toInteger_isPrimitiveRoot f 0

-- Equal nonzero coefficients evaluate to zero. An empty phase is essential.
example (a : ℤ) : (∑ i : Fin p, a • hζ.toInteger ^ (i : ℕ)) = 0 := by
  have hs : ∑ i : Fin p, hζ.toInteger ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact hζ.toInteger_isPrimitiveRoot.geom_sum_eq_zero hp.out.one_lt
  rw [← Finset.smul_sum, hs, smul_zero]

-- No auxiliary noncongruence assumption survives in the public Case I theorem.
example (hp5 : 5 ≤ p) (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (hcop : IsCoprime a b) (hfirst : ¬ (p : ℤ) ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := not_int_solution_caseI hζ hp5 hreg hcop hfirst

example (hp5 : 5 ≤ p) (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    FermatLastTheoremWith ℤ p := fermatLastTheoremWith_int_of_regular_prime hζ hp5 hreg
end ArbitraryUniverse

-- The congruent collision k₁=1,k₂=0 really makes the four-term expression vanish.
-- Therefore the sparse obstruction must not silently discard a≢b.
example {R : Type*} [CommRing R] (a ζ : R) :
    a + a * ζ - a * ζ ^ 1 - a * ζ ^ 0 = 0 := by ring

example : FermatLastTheoremFor 11 := fermatLastTheoremFor_eleven
example : FermatLastTheoremFor 13 := fermatLastTheoremFor_thirteen

example {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a ^ 11 + b ^ 11 ≠ c ^ 11 := fermatLastTheoremWith_int_eleven a b c ha hb hc
example {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a ^ 13 + b ^ 13 ≠ c ^ 13 := fermatLastTheoremWith_int_thirteen a b c ha hb hc

end PhaseRigidityFLTTest
