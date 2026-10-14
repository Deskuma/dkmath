import DkMath.NumberTheory.Legendre.ParitySafePersistence

namespace DkMathTest.LegendreCyclotomicPersistence

open DkMath.NumberTheory.Legendre DkMath.NumberTheory.GapFocusing
open DkMath.Gnomon DkMath.NumberTheory.Primitive
open scoped BigOperators

/-- Prime three has one shell residue, rather than consecutive persistence. -/
theorem three_shell_addresses (n : ℕ) :
    3 ∣ oddGnomon n ↔ n ≡ 1 [MOD 3] := by
  simpa using dvd_oddGnomon_iff_modEq_half (q := 3) (by decide) (by decide) (n := n)

theorem three_order_two_at_shell_ten : primeOrder 3 (11 : ℤ) (10 : ℤ) = 2 := by
  exact (dvd_oddGnomon_iff_primeOrder_eq_two (q := 3) (n := 10)
    (by decide) (by decide)).mp (by norm_num [oddGnomon])

theorem three_no_next_shell : ¬3 ∣ oddGnomon 11 :=
  not_dvd_oddGnomon_succ (q := 3) (n := 10) (by decide) (by decide)
    (by norm_num [oddGnomon])

/-- Starting position matters; the bound remains the ceiling of run length/three. -/
theorem three_run_regression :
    (lowerPrimeAddressOffsets 3 10 7).card = 3 ∧ shellFrequencyCap 3 7 = 3 := by
  decide

/-- A zero-length run and a full prime period are covered by the generic bound. -/
theorem frequency_boundaries :
    (lowerPrimeAddressOffsets 3 100 0).card = 0 ∧
      (lowerPrimeAddressOffsets 3 100 3).card ≤ 1 := by
  constructor
  · simp [lowerPrimeAddressOffsets]
  · exact lowerPrimeAddressOffsets_period_card_le_one (by decide) (by decide) 100

/-- Two different actual successor candidates carry the same persistent prime. -/
theorem shell_ten_two_persistent_three_seats :
    2 ∈ lowerParitySafeCandidates 10 ∧ 8 ∈ lowerParitySafeCandidates 10 ∧
      3 ∈ lowerParitySafePersistentSupport 10 2 ∧
      3 ∈ lowerParitySafePersistentSupport 10 8 := by
  norm_num [lowerParitySafeCandidates, mem_squareAnchorOddPointCoprimeOffsets,
    mem_squareAnchorCoprimeOffsets, SquareOffset, Nat.Coprime, Nat.odd_iff,
    lowerParitySafePersistentSupport, mem_paritySafeActiveSupport_iff_dvd]

/-- The proposed unweighted incidence-to-prime-shell injection is false,
already for one prime and one transition. -/
theorem unweighted_single_prime_frequency_bound_false :
    ¬((lowerParitySafeCandidates 10).filter
      (fun r => 3 ∈ lowerParitySafePersistentSupport 10 r)).card ≤
        (lowerPrimeAddressOffsets 3 10 1).card := by
  classical
  have hh := shell_ten_two_persistent_three_seats
  have hsub : ({2, 8} : Finset ℕ) ⊆
      (lowerParitySafeCandidates 10).filter
        (fun r => 3 ∈ lowerParitySafePersistentSupport 10 r) := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hh.1, hh.2.2.1⟩
    · exact Finset.mem_filter.mpr ⟨hh.2.1, hh.2.2.2⟩
  have hcard := Finset.card_le_card hsub
  have hfreq : (lowerPrimeAddressOffsets 3 10 1).card = 1 := by decide
  norm_num at hcard
  omega

/-- Lower canonical transport reverses parity even on an old candidate. -/
theorem lower_parity_reversal_regression :
    1 ∈ squareAnchorOddPointCoprimeOffsets 10 ∧
      successorThresholdInsert 10 1 ∉ squareAnchorOddPointCoprimeOffsets 11 := by
  constructor
  · norm_num [mem_squareAnchorOddPointCoprimeOffsets,
      mem_squareAnchorCoprimeOffsets, SquareOffset, Nat.Coprime, Nat.odd_iff]
  · exact lower_successor_not_paritySafeCandidate_of_odd (by decide)
      (by norm_num [Nat.odd_iff])

/-- Seat-divisor weights sharply reduce the crude all-seat weight in this run.
This is not a reduction of a production residual capacity. -/
theorem seat_weight_capacity_regression :
    lowerParitySafePersistenceCap 10 1 = 9 ∧
      lowerParitySafePersistenceCap 10 1 <
        11 * ∑ q ∈ (primeScalesUpTo 11).erase 2, shellFrequencyCap q 1 := by
  decide

/-- Freshness can be positive while the production support excess is zero.
Thus fresh incidences cannot simply be charged to support excess. -/
theorem fresh_incidence_without_support_excess :
    2 ∈ lowerParitySafeCandidates 6 ∧
      3 ∈ lowerParitySafeFreshSupport 6 2 ∧ paritySafeSupportExcess 7 = 0 := by
  constructor
  · norm_num [lowerParitySafeCandidates, mem_squareAnchorOddPointCoprimeOffsets,
      mem_squareAnchorCoprimeOffsets, SquareOffset, Nat.Coprime, Nat.odd_iff]
  constructor
  · norm_num [lowerParitySafeFreshSupport, mem_paritySafeActiveSupport_iff_dvd]
  · have hactive : squareAnchorOddActivePrimes 7 = {3, 5} := by
      ext q
      rw [mem_squareAnchorOddActivePrimes]
      constructor
      · rintro ⟨hq, hle, hn, h2⟩
        interval_cases q <;> norm_num at *
      · intro hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl <;> norm_num
    have hsupport (r : ℕ) : paritySafeActiveSupport 7 r =
        ({3, 5} : Finset ℕ).filter (fun q => q ∣ 49 + r) := by
      ext q
      rw [mem_paritySafeActiveSupport_iff_dvd, hactive]
      norm_num
    have hcandidates : squareAnchorOddPointCoprimeOffsets 7 =
        ({2, 4, 6, 8, 10, 12} : Finset ℕ) := by
      ext r
      rw [mem_squareAnchorOddPointCoprimeOffsets, mem_squareAnchorCoprimeOffsets]
      simp only [SquareOffset, Nat.odd_iff]
      constructor
      · rintro ⟨⟨⟨hlow, hupp⟩, hcop⟩, hodd⟩
        interval_cases r <;> norm_num [Nat.Coprime] at *
      · intro hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
          norm_num [Nat.Coprime]
    unfold paritySafeSupportExcess
    rw [hcandidates]
    simp_rw [hsupport]
    decide

-- Kernel reduction of the finite candidate counts needs a deeper recursion stack.
set_option maxRecDepth 10000 in
/-- A nonzero conditional charging calibration: twenty transitions, using
only the existing full-cover hypothesis and the checked seat-weighted capacity. -/
theorem twenty_transition_fresh_lower_bound
    (hfull : ∀ i ∈ Finset.range 20, SquareOffsetsFullyCovered (20 + i + 1)) :
    76 ≤ ∑ i ∈ Finset.range 20, lowerParitySafeFreshCount (20 + i) := by
  have hrequired : (∑ i ∈ Finset.range 20,
      (lowerParitySafeCandidates (20 + i)).card) = 245 := by
    simp_rw [lowerParitySafeCandidates_eq_filter_Icc]
    decide
  have hcap : lowerParitySafePersistenceCap 20 20 = 169 := by decide
  have h := sum_lowerParitySafeCandidates_sub_cap_le_fresh_of_fullyCovered 20 20 hfull
  simpa only [hrequired, hcap] using h

end DkMathTest.LegendreCyclotomicPersistence
