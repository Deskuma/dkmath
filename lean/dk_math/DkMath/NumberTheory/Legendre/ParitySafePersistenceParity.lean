/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafePersistence

#print "file: DkMath.NumberTheory.Legendre.ParitySafePersistenceParity"

/-!
# Parity doubles the period of persistence at a fixed lower seat

Only actual lower successor candidates are counted. Their parity requires
`n ≡ r [MOD 2]`. Together with the odd prime's shell address this spaces
repeated events at the same seat by `2*q`, improving Instruction 004's cap.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.Gnomon DkMath.NumberTheory.Primitive
open scoped BigOperators

/-- Fixed lower candidates require the old shell and seat to have the same parity. -/
theorem lower_candidate_modEq_two {n r : ℕ} (hr : r ∈ lowerParitySafeCandidates n) :
    n ≡ r [MOD 2] := by
  rw [lowerParitySafeCandidates_eq_filter_Icc] at hr
  have ho := (Finset.mem_filter.mp hr).2.2
  rw [Nat.add_mod, Nat.pow_mod] at ho
  have hb := Nat.mod_lt (n + 1) (by decide : 0 < 2)
  change n % 2 = r % 2
  interval_cases hm : (n + 1) % 2 <;> norm_num [hm] at ho <;> omega

/-- Addressed transitions at which the fixed seat is an actual lower candidate. -/
noncomputable def lowerCandidatePrimeAddressOffsets (q r N T : ℕ) : Finset ℕ :=
  (lowerPrimeAddressOffsets q N T).filter (fun i => r ∈ lowerParitySafeCandidates (N + i))

/-- The same fixed candidate seat and odd prime have period `2*q`, rather than q. -/
theorem lowerCandidatePrimeAddressOffsets_card_le {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (r N T : ℕ) :
    (lowerCandidatePrimeAddressOffsets q r N T).card ≤ shellFrequencyCap (2 * q) T := by
  classical
  by_cases hT : T = 0
  · simp [lowerCandidatePrimeAddressOffsets, lowerPrimeAddressOffsets, shellFrequencyCap, hT]
  have hmap : ∀ i ∈ lowerCandidatePrimeAddressOffsets q r N T,
      i / (2 * q) ∈ Finset.range (shellFrequencyCap (2 * q) T) := by
    intro i hi
    have hiT := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
    have hle : i ≤ T - 1 := by have := Finset.mem_range.mp hiT; omega
    have hdiv := Nat.div_le_div_right (c := 2 * q) hle
    simp only [Finset.mem_range, shellFrequencyCap, ite_eq_right hT]
    omega
  have hinj : Set.InjOn (fun i : ℕ => i / (2 * q))
      (lowerCandidatePrimeAddressOffsets q r N T) := by
    intro i hi j hj heq
    dsimp only at heq
    have hci := Finset.mem_filter.mp hi
    have hcj := Finset.mem_filter.mp hj
    have hqmod := modEq_of_dvd_oddGnomon hq hq2
      (Finset.mem_filter.mp hci.1).2 (Finset.mem_filter.mp hcj.1).2
    have h2mod := (lower_candidate_modEq_two hci.2).trans
      (lower_candidate_modEq_two hcj.2).symm
    have hcop : Nat.Coprime 2 q := by
      apply Nat.Coprime.symm
      apply hq.coprime_iff_not_dvd.mpr
      intro hd
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hd)
    have hm := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h2mod, hqmod⟩
    have hmod : i % (2 * q) = j % (2 * q) := Nat.ModEq.add_left_cancel' N hm
    have hmul := congrArg (fun x => (2 * q) * x) heq
    have hi' := Nat.mod_add_div i (2 * q)
    have hj' := Nat.mod_add_div j (2 * q)
    omega
  simpa using Finset.card_le_card_of_injOn (fun i => i / (2 * q)) hmap hinj

/-- Fixed-seat persistent incidence bound with the doubled period and actual
old-prime bound. The same offset is used only inside the canonical lower sector. -/
theorem sum_fixedSeat_persistentSupport_le_parity_frequency (r N T : ℕ) :
    (∑ i ∈ (Finset.range T).filter (fun i => r ∈ lowerParitySafeCandidates (N + i)),
      (lowerParitySafePersistentSupport (N + i) r).card) ≤
        ∑ q ∈ ((primeScalesUpTo (N + T)).erase 2).filter (fun q => q ∣ 4 * r + 1),
          shellFrequencyCap (2 * q) T := by
  classical
  let A := (Finset.range T).filter (fun i => r ∈ lowerParitySafeCandidates (N + i))
  let B := ((primeScalesUpTo (N + T)).erase 2).filter (fun q => q ∣ 4 * r + 1)
  calc
    (∑ i ∈ A, (lowerParitySafePersistentSupport (N + i) r).card) ≤
        ∑ i ∈ A, (B.filter (fun q => q ∣ oddGnomon (N + i))).card := by
      apply Finset.sum_le_sum
      intro i hi
      have hii := Finset.mem_filter.mp hi
      have hb : N + i ≤ N + T := by have := Finset.mem_range.mp hii.1; omega
      apply Finset.card_le_card
      intro q hq
      have ha := Finset.mem_filter.mp
        (lowerParitySafePersistentSupport_subset_addresses hii.2 hb hq)
      have hp := (Nat.mem_primeFactors.mp
        (lowerParitySafePersistentSupport_subset_primeFactors hii.2 hq)).2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨ha.1, hp⟩, ha.2⟩
    _ = ∑ q ∈ B, (lowerCandidatePrimeAddressOffsets q r N T).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [A, lowerCandidatePrimeAddressOffsets, lowerPrimeAddressOffsets,
        Finset.card_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hc : r ∈ lowerParitySafeCandidates (N + i) <;>
        by_cases ha : q ∣ oddGnomon (N + i) <;> simp [hc, ha]
    _ ≤ ∑ q ∈ B, shellFrequencyCap (2 * q) T := by
      apply Finset.sum_le_sum
      intro q hq
      have hb := Finset.mem_erase.mp (Finset.mem_filter.mp hq).1
      exact lowerCandidatePrimeAddressOffsets_card_le
        (mem_primeScalesUpTo.mp hb.2).1 hb.1 r N T

/-- Seat-weighted persistence capacity retaining the candidate parity restriction. -/
noncomputable def lowerParitySafeParityPersistenceCap (N T : ℕ) : ℕ :=
  ∑ r ∈ Finset.Icc 1 (N + T),
    ∑ q ∈ ((primeScalesUpTo (N + T)).erase 2).filter (fun q => q ∣ 4 * r + 1),
      shellFrequencyCap (2 * q) T

/-- The parity-refined capacity bounds the actual persistent incidence count. -/
theorem sum_lowerPersistentCount_le_parityCap (N T : ℕ) :
    (∑ i ∈ Finset.range T, lowerParitySafePersistentCount (N + i)) ≤
      lowerParitySafeParityPersistenceCap N T := by
  classical
  let U := Finset.Icc 1 (N + T)
  have hext (i : ℕ) (hi : i ∈ Finset.range T) :
      (∑ r ∈ lowerParitySafeCandidates (N + i),
        (lowerParitySafePersistentSupport (N + i) r).card) =
      ∑ r ∈ U, if r ∈ lowerParitySafeCandidates (N + i) then
        (lowerParitySafePersistentSupport (N + i) r).card else 0 := by
    have hfilter : U.filter (fun r => r ∈ lowerParitySafeCandidates (N + i)) =
        lowerParitySafeCandidates (N + i) := by
      ext r
      constructor
      · exact fun h => (Finset.mem_filter.mp h).2
      · intro hr
        have hh := Finset.mem_filter.mp hr
        have hs := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets hh.1
        have hii := Finset.mem_range.mp hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hs.1, by omega⟩, hr⟩
    have h := Finset.sum_filter (s := U)
      (p := fun r => r ∈ lowerParitySafeCandidates (N + i))
      (f := fun r => (lowerParitySafePersistentSupport (N + i) r).card)
    rw [hfilter] at h
    exact h
  calc
    (∑ i ∈ Finset.range T, lowerParitySafePersistentCount (N + i)) =
        ∑ i ∈ Finset.range T, ∑ r ∈ U,
          if r ∈ lowerParitySafeCandidates (N + i) then
            (lowerParitySafePersistentSupport (N + i) r).card else 0 :=
      Finset.sum_congr rfl hext
    _ = ∑ r ∈ U, ∑ i ∈ (Finset.range T).filter
        (fun i => r ∈ lowerParitySafeCandidates (N + i)),
        (lowerParitySafePersistentSupport (N + i) r).card := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ lowerParitySafeParityPersistenceCap N T :=
      Finset.sum_le_sum (fun r _ => sum_fixedSeat_persistentSupport_le_parity_frequency r N T)

/-- The strengthened finite-run fresh-incidence lower bound. -/
theorem sum_lowerCandidates_sub_parityCap_le_fresh_of_fullyCovered
    (N T : ℕ) (hfull : ∀ i ∈ Finset.range T, SquareOffsetsFullyCovered (N + i + 1)) :
    (∑ i ∈ Finset.range T, (lowerParitySafeCandidates (N + i)).card) -
        lowerParitySafeParityPersistenceCap N T ≤
      ∑ i ∈ Finset.range T, lowerParitySafeFreshCount (N + i) := by
  have hneed : (∑ i ∈ Finset.range T, (lowerParitySafeCandidates (N + i)).card) ≤
      ∑ i ∈ Finset.range T, lowerParitySafeIncidenceCount (N + i) :=
    Finset.sum_le_sum (fun i hi =>
      lowerParitySafeCandidates_card_le_incidence_of_fullyCovered (hfull i hi))
  have hsplit : (∑ i ∈ Finset.range T, lowerParitySafeIncidenceCount (N + i)) =
      (∑ i ∈ Finset.range T, lowerParitySafePersistentCount (N + i)) +
        ∑ i ∈ Finset.range T, lowerParitySafeFreshCount (N + i) := by
    simp_rw [lowerParitySafeIncidenceCount_eq_persistent_add_fresh]
    rw [Finset.sum_add_distrib]
  have hcap := sum_lowerPersistentCount_le_parityCap N T
  omega

/-- The previous prime-weighted cap equals its exact seat-weighted transpose. -/
theorem lowerPersistenceCap_eq_seatSum (N T : ℕ) :
    lowerParitySafePersistenceCap N T = ∑ r ∈ Finset.Icc 1 (N + T),
      ∑ q ∈ ((primeScalesUpTo (N + T)).erase 2).filter (fun q => q ∣ 4 * r + 1),
        shellFrequencyCap q T := by
  classical
  simp only [lowerParitySafePersistenceCap, lowerPersistentSeatPool,
    Finset.card_filter, Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hd : q ∣ 4 * r + 1 <;> simp [hd]

/-- Doubling a positive period can only lower its finite-run frequency cap. -/
theorem shellFrequencyCap_double_le {q : ℕ} (hq : 0 < q) (T : ℕ) :
    shellFrequencyCap (2 * q) T ≤ shellFrequencyCap q T := by
  by_cases hT : T = 0
  · simp [shellFrequencyCap, hT]
  have hdiv : (T - 1) / (2 * q) ≤ (T - 1) / q := by
    rw [Nat.le_div_iff_mul_le hq]
    exact (Nat.mul_le_mul_left ((T - 1) / (2 * q))
      (by omega : q ≤ 2 * q)).trans (Nat.div_mul_le_self _ _)
  simp only [shellFrequencyCap, ite_eq_right hT]
  omega

/-- Uniform comparison with the actual Instruction 004 capacity. -/
theorem lowerParitySafeParityPersistenceCap_le_oldCap (N T : ℕ) :
    lowerParitySafeParityPersistenceCap N T ≤ lowerParitySafePersistenceCap N T := by
  classical
  rw [lowerPersistenceCap_eq_seatSum]
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro q hq
  have hp := mem_primeScalesUpTo.mp (Finset.mem_erase.mp (Finset.mem_filter.mp hq).1).2
  exact shellFrequencyCap_double_le hp.1.pos T

end DkMath.NumberTheory.Legendre
