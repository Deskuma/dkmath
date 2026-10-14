/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonSupportTurnover
import DkMath.NumberTheory.GapFocusing.HomogeneousAddress

/-!
# Cyclotomic addresses of lower square-shell persistence

The degree is fixed at two while the shell index varies. This arithmetic
progression is different from the fixed-coordinate degree ray of GapFocusing.
Frequency counts prime-shell events; support incidence counts also count seats.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.Gnomon DkMath.CFBRC DkMath.NumberTheory.GapFocusing

/-- The existing homogeneous evaluator at `(n+1,n)` is the odd gnomon,
as an equality of elements of `ℤ`. Its shifted coordinates are `(1,n)`. -/
theorem cyclotomicShiftedEval_two_eq_oddGnomon (n : ℕ) :
    cyclotomicShiftedEval 2 (1 : ℤ) (n : ℤ) = (oddGnomon n : ℤ) := by
  simp [cyclotomicShiftedEval, Polynomial.cyclotomic_two,
    Polynomial.homogenize_add, Polynomial.homogenize_X, oddGnomon]
  ring

/-- Lower common support is exactly old support at the actual degree-two layer. -/
theorem mem_lower_commonSupport_iff_cyclotomic
    {n r q : ℕ} (hr : SquareOffset n r) (hlow : r < n + 1) :
    q ∈ squareOffsetPrimeSupport n r ∩
        squareOffsetPrimeSupport (n + 1) (successorThresholdInsert n r) ↔
      q ∈ squareOffsetPrimeSupport n r ∧
        (q : ℤ) ∣ cyclotomicShiftedEval 2 (1 : ℤ) (n : ℤ) := by
  rw [mem_reindexed_primeSupport_inter_lower_iff hr hlow,
    cyclotomicShiftedEval_two_eq_oddGnomon, Int.natCast_dvd_natCast]

/-- A prime dividing the lower displacement divides neither shell coordinate. -/
theorem not_dvd_coordinates_of_dvd_oddGnomon {q n : ℕ}
    (hq : q.Prime) (hd : q ∣ oddGnomon n) : ¬q ∣ n ∧ ¬q ∣ n + 1 := by
  have hn : ¬q ∣ n := by
    intro h
    have h2 : q ∣ 2 * n := dvd_mul_of_dvd_right h 2
    have hone : q ∣ 1 := (Nat.dvd_add_iff_right h2).mpr hd
    exact hq.not_dvd_one hone
  refine ⟨hn, ?_⟩
  intro h
  have hsum : q ∣ n + (n + 1) := by simpa [oddGnomon, two_mul, Nat.add_assoc] using hd
  exact hn ((Nat.dvd_add_iff_left h).mpr hsum)

/-- For an odd prime, the lower displacement condition is exactly ratio order two.
No denominator hypothesis is hidden: a vanishing denominator gives order zero. -/
theorem dvd_oddGnomon_iff_primeOrder_eq_two {q n : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) :
    q ∣ oddGnomon n ↔ primeOrder q (n + 1 : ℕ) n = 2 := by
  let : Fact q.Prime := ⟨hq⟩
  have hqnot : ¬q ∣ 2 := by
    intro hd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hd)
  by_cases hn : q ∣ n
  · have hz : ((n : ℤ) : ZMod q) = 0 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      exact_mod_cast hn
    have horder : primeOrder q (n + 1 : ℕ) n = 0 := by
      unfold primeOrder primeRatio
      rw [hz, inv_zero, mul_zero, orderOf_zero]
    exact ⟨fun hd => (not_dvd_coordinates_of_dvd_oddGnomon hq hd).1 hn |>.elim,
      fun ho => by omega⟩
  · have hnZ : ¬(q : ℤ) ∣ (n : ℤ) := by exact_mod_cast hn
    have h := dvd_cyclotomicShiftedEval_iff_primeOrder_eq_of_not_dvd
      q 2 (n + 1 : ℕ) n hnZ hqnot
    have hsub : ((n + 1 : ℕ) : ℤ) - (n : ℤ) = 1 := by omega
    rw [hsub, cyclotomicShiftedEval_two_eq_oddGnomon, Int.natCast_dvd_natCast] at h
    exact h

/-- The element-valued cyclotomic form of the same order-two equivalence. -/
theorem dvd_cyclotomic_lower_iff_primeOrder_eq_two {q n : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) :
    (q : ℤ) ∣ cyclotomicShiftedEval 2 (1 : ℤ) (n : ℤ) ↔
      primeOrder q (n + 1 : ℕ) n = 2 := by
  rw [cyclotomicShiftedEval_two_eq_oddGnomon, Int.natCast_dvd_natCast]
  exact dvd_oddGnomon_iff_primeOrder_eq_two hq hq2

/-- Direct support-ledger interface for the fundamental order-two address. -/
theorem mem_lower_commonSupport_iff_primeOrder_eq_two
    {n r q : ℕ} (hr : SquareOffset n r) (hlow : r < n + 1)
    (hq : q.Prime) (hq2 : q ≠ 2) :
    q ∈ squareOffsetPrimeSupport n r ∩
        squareOffsetPrimeSupport (n + 1) (successorThresholdInsert n r) ↔
      q ∈ squareOffsetPrimeSupport n r ∧ primeOrder q (n + 1 : ℕ) n = 2 := by
  rw [mem_reindexed_primeSupport_inter_lower_iff hr hlow,
    dvd_oddGnomon_iff_primeOrder_eq_two hq hq2]

/-- The half-prime residue is the first possible lower shell address. -/
theorem dvd_oddGnomon_iff_modEq_half {q n : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) :
    q ∣ oddGnomon n ↔ n ≡ (q - 1) / 2 [MOD q] := by
  obtain ⟨h, hh⟩ := hq.odd_of_ne_two hq2
  have hhalf : (q - 1) / 2 = h := by omega
  have hqodd : q % 2 = 1 := by omega
  rw [hhalf]
  constructor
  · rintro ⟨k, hk⟩
    have hkodd : k % 2 = 1 := by
      have hm := congrArg (fun x : ℕ => x % 2) hk
      simp [oddGnomon, Nat.add_mod, Nat.mul_mod, hqodd] at hm
      omega
    have hnk : n = h + q * (k / 2) := by
      have hsplit := Nat.mod_add_div k 2
      simp only [hkodd] at hsplit
      dsimp [oddGnomon] at hk
      nlinarith
    simp [hnk, Nat.ModEq]
  · intro hm
    have hhq : h < q := by omega
    have hmod : n % q = h := by simpa [Nat.ModEq, Nat.mod_eq_of_lt hhq] using hm
    have hsplit := Nat.mod_add_div n q
    refine ⟨2 * (n / q) + 1, ?_⟩
    dsimp [oddGnomon]
    rw [hmod] at hsplit
    nlinarith

/-- Natural-number form of the complete shell arithmetic progression. -/
theorem dvd_oddGnomon_iff_eq_half_add_mul {q n : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) :
    q ∣ oddGnomon n ↔ ∃ k : ℕ, n = (q - 1) / 2 + k * q := by
  rw [dvd_oddGnomon_iff_modEq_half hq hq2]
  have hqpos := hq.pos
  have hhalf : (q - 1) / 2 < q := by omega
  constructor
  · intro hm
    refine ⟨n / q, ?_⟩
    have hmod : n % q = (q - 1) / 2 := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hhalf] using hm
    simpa [hmod, Nat.mul_comm] using (Nat.mod_add_div n q).symm
  · rintro ⟨k, rfl⟩
    simp [Nat.ModEq]

/-- Repeated lower addresses have exactly the same residue, symmetrically. -/
theorem modEq_of_dvd_oddGnomon {q n m : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hn : q ∣ oddGnomon n) (hm : q ∣ oddGnomon m) : n ≡ m [MOD q] :=
  ((dvd_oddGnomon_iff_modEq_half hq hq2).mp hn).trans
    ((dvd_oddGnomon_iff_modEq_half hq hq2).mp hm).symm

/-- Given one address, congruence is also sufficient for every other address. -/
theorem dvd_oddGnomon_iff_modEq_of_dvd {q n m : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hn : q ∣ oddGnomon n) :
    q ∣ oddGnomon m ↔ m ≡ n [MOD q] := by
  rw [dvd_oddGnomon_iff_modEq_half hq hq2]
  exact ⟨fun hm => hm.trans ((dvd_oddGnomon_iff_modEq_half hq hq2).mp hn).symm,
    fun hm => hm.trans ((dvd_oddGnomon_iff_modEq_half hq hq2).mp hn)⟩

/-- Fixing a seat as well as a shell address restricts the prime basis further:
every old divisor at an addressed shell divides `4*r+1`. -/
theorem dvd_four_mul_offset_add_one_of_lower_persistence {q n r : ℕ}
    (hpoint : q ∣ n ^ 2 + r) (haddress : q ∣ oddGnomon n) : q ∣ 4 * r + 1 := by
  have hp : (q : ℤ) ∣ (n : ℤ) ^ 2 + r := by exact_mod_cast hpoint
  have ha : (q : ℤ) ∣ 2 * (n : ℤ) + 1 := by
    exact_mod_cast haddress
  have hd := (dvd_mul_of_dvd_right hp (4 : ℤ)).sub
    (dvd_mul_of_dvd_left ha (2 * (n : ℤ) - 1))
  have heq : 4 * ((n : ℤ) ^ 2 + r) -
      (2 * (n : ℤ) + 1) * (2 * (n : ℤ) - 1) = 4 * (r : ℤ) + 1 := by ring
  rw [heq] at hd
  exact_mod_cast hd

/-- The same odd prime cannot persist on consecutive lower transitions. -/
theorem not_dvd_oddGnomon_succ {q n : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hn : q ∣ oddGnomon n) :
    ¬q ∣ oddGnomon (n + 1) := by
  intro hm
  have h := modEq_of_dvd_oddGnomon hq hq2 hn hm
  have hd : q ∣ 1 := (Nat.left_modEq_add_iff.mp h)
  exact hq.not_dvd_one hd

/-- Lower addresses in a run of `T` transitions starting at `N`. -/
def lowerPrimeAddressOffsets (q N T : ℕ) : Finset ℕ :=
  (Finset.range T).filter (fun i => q ∣ oddGnomon (N + i))

/-- The ceiling of a natural run length divided by a positive period,
written without rational casts. -/
def shellFrequencyCap (q T : ℕ) : ℕ :=
  if T = 0 then 0 else (T - 1) / q + 1

/-- At most one occurrence per period: quotient blocks give an injection.
This holds for an arbitrary starting shell, including zero. -/
theorem lowerPrimeAddressOffsets_card_le {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (N T : ℕ) :
    (lowerPrimeAddressOffsets q N T).card ≤ shellFrequencyCap q T := by
  classical
  by_cases hT : T = 0
  · simp [lowerPrimeAddressOffsets, shellFrequencyCap, hT]
  have hmap : ∀ i ∈ lowerPrimeAddressOffsets q N T,
      i / q ∈ Finset.range (shellFrequencyCap q T) := by
    intro i hi
    have hiT := (Finset.mem_filter.mp hi).1
    have hle : i ≤ T - 1 := by have := Finset.mem_range.mp hiT; omega
    have hdiv := Nat.div_le_div_right (c := q) hle
    simp only [Finset.mem_range, shellFrequencyCap, ite_eq_right hT]
    omega
  have hinj : Set.InjOn (fun i : ℕ => i / q) (lowerPrimeAddressOffsets q N T) := by
    intro i hi j hj heq
    dsimp only at heq
    have hm := modEq_of_dvd_oddGnomon hq hq2
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    have hmod : i % q = j % q := Nat.ModEq.add_left_cancel' N hm
    have hmul := congrArg (fun x => q * x) heq
    have hi' := Nat.mod_add_div i q
    have hj' := Nat.mod_add_div j q
    omega
  simpa using Finset.card_le_card_of_injOn (fun i => i / q) hmap hinj

/-- Every block of exactly one prime period contains at most one address. -/
theorem lowerPrimeAddressOffsets_period_card_le_one {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (N : ℕ) :
    (lowerPrimeAddressOffsets q N q).card ≤ 1 := by
  have h := lowerPrimeAddressOffsets_card_le hq hq2 N q
  have hlt : q - 1 < q := Nat.sub_lt hq.pos (by decide)
  simpa [shellFrequencyCap, hq.ne_zero, Nat.div_eq_of_lt hlt] using h

end DkMath.NumberTheory.Legendre
