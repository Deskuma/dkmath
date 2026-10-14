/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeExcessCertificate
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.GCD.BigOperators

#print "file: DkMath.NumberTheory.Legendre.ParitySafeCRTSeat"

/-!
## Windowed CRT support witnesses

Congruence transport, parity selection and candidate coprimality are separate
theorem obligations. A short period supplies an offset, not automatically a
candidate for an arbitrary anchor. Prime anchors have a proved short-period
candidate provider; a family still needs seat-level distinctness and enough
total charge to force an uncovered candidate.
-/

namespace DkMath.NumberTheory

open scoped BigOperators

/-- Every residue class of a positive period has a positive representative at most one period. -/
theorem exists_pos_modEq_le_period {m : ℕ} (hm : 0 < m) (a : ℕ) :
    ∃ r, 0 < r ∧ r ≤ m ∧ Nat.ModEq m r a := by
  by_cases hzero : a % m = 0
  · refine ⟨m, hm, le_refl _, ?_⟩
    simp [Nat.ModEq, hzero]
  · refine ⟨a % m, by omega, Nat.le_of_lt (Nat.mod_lt a hm), ?_⟩
    simp [Nat.ModEq]

/-- A full positive period fits in any window at least that long, with exact endpoints. -/
theorem exists_pos_modEq_le_window {m W : ℕ} (hm : 0 < m) (hW : m ≤ W) (a : ℕ) :
    ∃ r, 0 < r ∧ r ≤ W ∧ Nat.ModEq m r a := by
  obtain ⟨r, hr, hle, heq⟩ := exists_pos_modEq_le_period hm a
  exact ⟨r, hr, hle.trans hW, heq⟩

/-- Natural-number complement avoids interpreting a truncated subtraction as a negative residue. -/
theorem modEq_add_complement_zero {m : ℕ} (hm : 0 < m) (A : ℕ) :
    Nat.ModEq m (A + (m - A % m)) 0 := by
  have hre := Nat.mod_add_div A m
  have hrem := Nat.mod_lt A hm
  have hid : A + (m - A % m) = m * (A / m) + m := by omega
  rw [hid]
  exact Nat.modEq_zero_iff_dvd.mpr (dvd_add (dvd_mul_right m (A / m)) dvd_rfl)

/-- Parity is an additional CRT equation; its positive period is twice the odd modulus. -/
theorem exists_parity_offset_le_two_mul_period {m : ℕ} (hm : 0 < m)
    (hcop : Nat.Coprime m 2) (A : ℕ) :
    ∃ r, 0 < r ∧ r ≤ 2 * m ∧ m ∣ A + r ∧ Odd (A + r) := by
  let c := Nat.chineseRemainder hcop (m - A % m) (1 - A % 2)
  obtain ⟨r, hr, hle, heq⟩ := exists_pos_modEq_le_period (by omega : 0 < 2 * m) (c : ℕ)
  have hmEq := (heq.of_dvd (dvd_mul_left m 2)).trans c.prop.1
  have htwoEq := (heq.of_dvd (dvd_mul_right 2 m)).trans c.prop.2
  have hdiv : m ∣ A + r := Nat.modEq_zero_iff_dvd.mp
    ((hmEq.add_left A).trans (modEq_add_complement_zero hm A))
  have hparity : Nat.ModEq 2 (A + (1 - A % 2)) 1 := by
    unfold Nat.ModEq
    omega
  have hpoint := (htwoEq.add_left A).trans hparity
  have hodd : Odd (A + r) := by
    rw [Nat.odd_iff]
    exact hpoint
  exact ⟨r, hr, hle, hdiv, hodd⟩

end DkMath.NumberTheory

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

/-- Congruence at each active prime transports only support membership; it does not assert a window. -/
theorem activeSupport_contains_of_point_modEq {n r : ℕ} (Q : Finset ℕ)
    (hQ : Q ⊆ squareAnchorOddActivePrimes n)
    (hmod : ∀ q ∈ Q, Nat.ModEq q (n ^ 2 + r) 0) :
    Q ⊆ paritySafeActiveSupport n r := by
  intro q hq
  exact mem_paritySafeActiveSupport_iff_dvd.mpr
    ⟨hQ hq, Nat.modEq_zero_iff_dvd.mp (hmod q hq)⟩

/-- A common product multiple is a convenient homogeneous CRT certificate. -/
theorem activeSupport_contains_of_product_dvd {n r : ℕ} (Q : Finset ℕ)
    (hQ : Q ⊆ squareAnchorOddActivePrimes n) (hprod : (∏ q ∈ Q, q) ∣ n ^ 2 + r) :
    Q ⊆ paritySafeActiveSupport n r := by
  apply activeSupport_contains_of_point_modEq Q hQ
  intro q hq
  exact Nat.modEq_zero_iff_dvd.mpr ((Finset.dvd_prod_of_mem id hq).trans hprod)

/-- Candidate membership remains explicit when a congruence witness pays local excess. -/
theorem local_excess_ge_of_point_modEq {n r : ℕ} (Q : Finset ℕ)
    (_hr : r ∈ squareAnchorOddPointCoprimeOffsets n)
    (hQ : Q ⊆ squareAnchorOddActivePrimes n)
    (hmod : ∀ q ∈ Q, Nat.ModEq q (n ^ 2 + r) 0) :
    Q.card - 1 ≤ (paritySafeActiveSupport n r).card - 1 :=
  Nat.sub_le_sub_right (Finset.card_le_card (activeSupport_contains_of_point_modEq Q hQ hmod)) 1

/-- Actual candidate conditions, with parity and anchor coprimality separately supplied. -/
theorem candidate_of_window_coprime_odd {n r : ℕ}
    (hrpos : 0 < r) (hrle : r ≤ 2 * n) (hcop : Nat.Coprime n r) (hodd : Odd (n ^ 2 + r)) :
    r ∈ squareAnchorOddPointCoprimeOffsets n :=
  mem_squareAnchorOddPointCoprimeOffsets.mpr
    ⟨mem_squareAnchorCoprimeOffsets.mpr ⟨⟨hrpos, hrle⟩, hcop⟩, hodd⟩

/-- A parity-adjusted short product period supplies a windowed support witness, before coprimality. -/
theorem exists_windowed_odd_support_of_product_le {n : ℕ} (Q : Finset ℕ)
    (hQ : Q ⊆ squareAnchorOddActivePrimes n) (hshort : (∏ q ∈ Q, q) ≤ n) :
    ∃ r, 0 < r ∧ r ≤ 2 * n ∧ Odd (n ^ 2 + r) ∧ Q ⊆ paritySafeActiveSupport n r := by
  have hpos : 0 < ∏ q ∈ Q, q := Finset.prod_pos fun q hq =>
    (mem_squareAnchorOddActivePrimes.mp (hQ hq)).1.pos
  have hcop : Nat.Coprime (∏ q ∈ Q, q) 2 := Nat.Coprime.prod_left fun q hq =>
    Nat.coprime_two_right.mpr ((mem_squareAnchorOddActivePrimes.mp (hQ hq)).1.odd_of_ne_two
      (mem_squareAnchorOddActivePrimes.mp (hQ hq)).2.2.2)
  obtain ⟨r, hr, hle, hdvd, hodd⟩ :=
    DkMath.NumberTheory.exists_parity_offset_le_two_mul_period hpos hcop (n ^ 2)
  exact ⟨r, hr, by omega, hodd, activeSupport_contains_of_product_dvd Q hQ hdvd⟩

/-- At a prime anchor, an odd point at a positive strict-window offset is automatically anchor coprime. -/
theorem coprime_prime_anchor_of_strict_window_odd {n r : ℕ} (hn : n.Prime)
    (hrpos : 0 < r) (hrlt : r < 2 * n) (hodd : Odd (n ^ 2 + r)) : Nat.Coprime n r := by
  apply hn.coprime_iff_not_dvd.mpr
  intro hdvd
  obtain ⟨k, hk⟩ := hdvd
  have hkpos : 0 < k := by nlinarith [hn.pos]
  have hklt : k < 2 := by nlinarith [hn.pos]
  have hkeq : k = 1 := by omega
  have hre : r = n := by simpa [hkeq] using hk
  rw [hre] at hodd
  have heven : Even (n ^ 2 + n) := by
    have h := Nat.even_mul_succ_self n
    convert h using 1
    ring
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- Infinite prime-anchor certificate provider: a strict short product period realizes all witnesses on a candidate. -/
theorem exists_candidate_support_of_prime_product_lt {n : ℕ} (hn : n.Prime)
    (Q : Finset ℕ) (hQ : Q ⊆ squareAnchorOddActivePrimes n)
    (hshort : (∏ q ∈ Q, q) < n) :
    ∃ r ∈ squareAnchorOddPointCoprimeOffsets n, Q ⊆ paritySafeActiveSupport n r := by
  have hpos : 0 < ∏ q ∈ Q, q := Finset.prod_pos fun q hq =>
    (mem_squareAnchorOddActivePrimes.mp (hQ hq)).1.pos
  have hcop : Nat.Coprime (∏ q ∈ Q, q) 2 := Nat.Coprime.prod_left fun q hq =>
    Nat.coprime_two_right.mpr ((mem_squareAnchorOddActivePrimes.mp (hQ hq)).1.odd_of_ne_two
      (mem_squareAnchorOddActivePrimes.mp (hQ hq)).2.2.2)
  obtain ⟨r, hr, hle, hdvd, hodd⟩ :=
    DkMath.NumberTheory.exists_parity_offset_le_two_mul_period hpos hcop (n ^ 2)
  have hlt : r < 2 * n := by omega
  exact ⟨r, candidate_of_window_coprime_odd hr (by omega)
    (coprime_prime_anchor_of_strict_window_odd hn hr hlt hodd) hodd,
    activeSupport_contains_of_product_dvd Q hQ hdvd⟩

/-- The realized prime-anchor witness pays its local charge into the original global sum. -/
theorem witness_charge_le_supportExcess_of_prime_product_lt {n : ℕ} (hn : n.Prime)
    (Q : Finset ℕ) (hQ : Q ⊆ squareAnchorOddActivePrimes n)
    (hshort : (∏ q ∈ Q, q) < n) : Q.card - 1 ≤ paritySafeSupportExcess n := by
  obtain ⟨r, hr, hw⟩ := exists_candidate_support_of_prime_product_lt hn Q hQ hshort
  have hR : ({r} : Finset ℕ) ⊆ squareAnchorOddPointCoprimeOffsets n := by
    intro x hx
    have heq := Finset.mem_singleton.mp hx
    simpa only [heq] using hr
  have hP : ∀ x ∈ ({r} : Finset ℕ), Q ⊆ paritySafeActiveSupport n x := by
    intro x hx
    have heq := Finset.mem_singleton.mp hx
    simpa only [heq] using hw
  simpa using sum_witness_support_excess_le_supportExcess {r} (fun _ => Q) hR hP

/-- A concrete infinite class supplies charge2, without asserting that this meets every deficit. -/
theorem supportExcess_ge_two_of_prime_gt_105 {n : ℕ} (hn : n.Prime) (hlarge : 105 < n) :
    2 ≤ paritySafeSupportExcess n := by
  have hQ : ({3, 5, 7} : Finset ℕ) ⊆ squareAnchorOddActivePrimes n := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> apply mem_squareAnchorOddActivePrimes.mpr
    all_goals refine ⟨by decide, by omega, ?_, by decide⟩
    all_goals
      intro hdvd
      have hd := (Nat.dvd_prime hn).mp hdvd
      omega
  have hshort : (∏ q ∈ ({3, 5, 7} : Finset ℕ), q) < n := by simpa using hlarge
  simpa using witness_charge_le_supportExcess_of_prime_product_lt hn {3, 5, 7} hQ hshort

/-- Modular separation of the realized seats is a sufficient distinctness certificate. -/
theorem seat_ne_of_distinct_modEq_classes {m r s a b : ℕ}
    (hr : Nat.ModEq m r a) (hs : Nat.ModEq m s b) (hab : ¬Nat.ModEq m a b) : r ≠ s := by
  intro heq
  subst s
  exact hab (hr.symm.trans hs)

/-- Indexed CRT families require injectivity of the actual seat map, not distinct witness sets. -/
theorem sum_indexed_modEq_charge_le_supportExcess {ι : Type*} {n : ℕ}
    (J : Finset ι) (seat : ι → ℕ) (Q : ι → Finset ℕ)
    (hinj : Set.InjOn seat J)
    (hcandidate : ∀ j ∈ J, seat j ∈ squareAnchorOddPointCoprimeOffsets n)
    (hQ : ∀ j ∈ J, Q j ⊆ squareAnchorOddActivePrimes n)
    (hmod : ∀ j ∈ J, ∀ q ∈ Q j, Nat.ModEq q (n ^ 2 + seat j) 0) :
    (∑ j ∈ J, ((Q j).card - 1)) ≤ paritySafeSupportExcess n := by
  have hR : J.image seat ⊆ squareAnchorOddPointCoprimeOffsets n := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
    exact hcandidate j hj
  have h := sum_local_cost_le_supportExcess (J.image seat)
    (fun r => (paritySafeActiveSupport n r).card - 1) hR (by intros; exact le_refl _)
  rw [Finset.sum_image hinj] at h
  apply le_trans (Finset.sum_le_sum ?_) h
  intro j hj
  exact local_excess_ge_of_point_modEq (Q j) (hcandidate j hj) (hQ j hj) (hmod j hj)

theorem uncovered_nonempty_of_indexed_modEq_certificates {ι : Type*} {n : ℕ}
    (J : Finset ι) (seat : ι → ℕ) (Q : ι → Finset ℕ)
    (hinj : Set.InjOn seat J)
    (hcandidate : ∀ j ∈ J, seat j ∈ squareAnchorOddPointCoprimeOffsets n)
    (hQ : ∀ j ∈ J, Q j ⊆ squareAnchorOddActivePrimes n)
    (hmod : ∀ j ∈ J, ∀ q ∈ Q j, Nat.ModEq q (n ^ 2 + seat j) 0)
    (hgap : paritySafeTwoPrimeIncidenceUpper n < (squareAnchorOddPointCoprimeOffsets n).card +
      (∑ j ∈ J, ((Q j).card - 1))) : (paritySafeUncoveredCandidates n).Nonempty :=
  paritySafeUncovered_nonempty_of_twoPrimeUpper_lt_candidate_add_excess
    (sum_indexed_modEq_charge_le_supportExcess J seat Q hinj hcandidate hQ hmod) hgap

theorem exists_prime_squareCell_of_indexed_modEq_certificates {ι : Type*} {n : ℕ}
    (hn : 0 < n) (J : Finset ι) (seat : ι → ℕ) (Q : ι → Finset ℕ)
    (hinj : Set.InjOn seat J)
    (hcandidate : ∀ j ∈ J, seat j ∈ squareAnchorOddPointCoprimeOffsets n)
    (hQ : ∀ j ∈ J, Q j ⊆ squareAnchorOddActivePrimes n)
    (hmod : ∀ j ∈ J, ∀ q ∈ Q j, Nat.ModEq q (n ^ 2 + seat j) 0)
    (hgap : paritySafeTwoPrimeIncidenceUpper n < (squareAnchorOddPointCoprimeOffsets n).card +
      (∑ j ∈ J, ((Q j).card - 1))) : ∃ p, Nat.Prime p ∧ SquareCell n p :=
  exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty hn
    (uncovered_nonempty_of_indexed_modEq_certificates J seat Q hinj hcandidate hQ hmod hgap)

/-- Same-modulus parity-compatible lifts give distinct candidates at a prime anchor and a counted charge. -/
theorem prime_anchor_period_family_charge_le_supportExcess {n : ℕ} (hn : n.Prime)
    (Q : Finset ℕ) (hQ : Q ⊆ squareAnchorOddActivePrimes n) :
    ((n - 1) / (∏ q ∈ Q, q)) * (Q.card - 1) ≤ paritySafeSupportExcess n := by
  let m := ∏ q ∈ Q, q
  let T := (n - 1) / m
  have hm : 0 < m := Finset.prod_pos fun q hq =>
    (mem_squareAnchorOddActivePrimes.mp (hQ hq)).1.pos
  have hcop : Nat.Coprime m 2 := Nat.Coprime.prod_left fun q hq =>
    Nat.coprime_two_right.mpr ((mem_squareAnchorOddActivePrimes.mp (hQ hq)).1.odd_of_ne_two
      (mem_squareAnchorOddActivePrimes.mp (hQ hq)).2.2.2)
  obtain ⟨r, hr, hle, hdvd, hodd⟩ :=
    DkMath.NumberTheory.exists_parity_offset_le_two_mul_period hm hcop (n ^ 2)
  let seat := fun j => r + 2 * m * j
  have hcap : m * T ≤ n - 1 := by
    have h := Nat.mod_add_div (n - 1) m
    dsimp [T]
    omega
  have hstrict : ∀ j ∈ Finset.range T, seat j < 2 * n := by
    intro j hj
    have hjle : j + 1 ≤ T := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    have hmul := Nat.mul_le_mul_left m hjle
    have hminus : n - 1 < n := Nat.sub_lt hn.pos (by decide : 0 < 1)
    dsimp [seat]
    nlinarith
  have hpositive : ∀ j, 0 < seat j := by intro j; dsimp [seat]; omega
  have hoddSeat : ∀ j, Odd (n ^ 2 + seat j) := by
    intro j
    have heven : Even (2 * m * j) := by exact ⟨m * j, by ring⟩
    simpa only [seat, ← Nat.add_assoc] using hodd.add_even heven
  have hdvdSeat : ∀ j, m ∣ n ^ 2 + seat j := by
    intro j
    dsimp [seat]
    rw [← Nat.add_assoc]
    exact dvd_add hdvd (dvd_mul_of_dvd_left (dvd_mul_left m 2) j)
  have hinj : Set.InjOn seat (Finset.range T) := by
    intro i _ j _ hij
    dsimp [seat] at hij
    nlinarith
  have hcandidate : ∀ j ∈ Finset.range T, seat j ∈ squareAnchorOddPointCoprimeOffsets n := by
    intro j hj
    exact candidate_of_window_coprime_odd (hpositive j) (Nat.le_of_lt (hstrict j hj))
      (coprime_prime_anchor_of_strict_window_odd hn (hpositive j) (hstrict j hj) (hoddSeat j))
      (hoddSeat j)
  have hmod : ∀ j ∈ Finset.range T, ∀ q ∈ Q, Nat.ModEq q (n ^ 2 + seat j) 0 := by
    intro j _ q hq
    exact Nat.modEq_zero_iff_dvd.mpr ((Finset.dvd_prod_of_mem id hq).trans (hdvdSeat j))
  have h := sum_indexed_modEq_charge_le_supportExcess (Finset.range T) seat (fun _ => Q)
    hinj hcandidate (fun _ _ => hQ) hmod
  simpa [T, m] using h

/-- The counted prime-anchor family feeds the existing hybrid criterion when it meets demand. -/
theorem prime_squareCell_of_prime_period_family_gap {n : ℕ} (hn : n.Prime)
    (Q : Finset ℕ) (hQ : Q ⊆ squareAnchorOddActivePrimes n)
    (hgap : paritySafeTwoPrimeIncidenceUpper n < (squareAnchorOddPointCoprimeOffsets n).card +
      ((n - 1) / (∏ q ∈ Q, q)) * (Q.card - 1)) :
    ∃ p, Nat.Prime p ∧ SquareCell n p :=
  exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty hn.pos
    (paritySafeUncovered_nonempty_of_twoPrimeUpper_lt_candidate_add_excess
      (prime_anchor_period_family_charge_le_supportExcess hn Q hQ) hgap)

end DkMath.NumberTheory.Legendre
