/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeMergedCRT

#print "file: DkMath.NumberTheory.Legendre.ParitySafeMixedCRT"

/-!
## Candidate-aware CRT families and exact elementary scaling

An extra point residue modulo2p controls anchor coprimality for2^a*p^k.
Period bounds are sufficient conditions; a zero counted range supplies zero
charge. Two prime-anchor families sharing only one label can add their
charges even when their actual seats overlap.
-/

namespace DkMath.NumberTheory

open scoped BigOperators

/-- Two coprime moduli prescribe support0 and coprimality-selector1 on the point. -/
theorem exists_support_one_offset_le_period {m L : ℕ} (hm : 0 < m) (hL : 0 < L)
    (hcop : Nat.Coprime m L) (A : ℕ) :
    ∃ r, 0 < r ∧ r ≤ L * m ∧ m ∣ A + r ∧ Nat.ModEq L (A + r) 1 := by
  let c := Nat.chineseRemainder hcop (m - A % m) ((L - A % L) + 1)
  obtain ⟨r, hr, hle, heq⟩ := exists_pos_modEq_le_period (Nat.mul_pos hL hm) (c : ℕ)
  have hmEq := (heq.of_dvd (dvd_mul_left m L)).trans c.prop.1
  have hLEq := (heq.of_dvd (dvd_mul_right L m)).trans c.prop.2
  have hdiv := Nat.modEq_zero_iff_dvd.mp
    ((hmEq.add_left A).trans (modEq_add_complement_zero hm A))
  have hone : Nat.ModEq L (A + ((L - A % L) + 1)) 1 := by
    simpa only [Nat.add_assoc, Nat.zero_add] using (modEq_add_complement_zero hL A).add_right 1
  exact ⟨r, hr, hle, hdiv, (hLEq.add_left A).trans hone⟩

/-- A positive base and a counted period bound give an explicit distinct finite lift family. -/
theorem exists_positive_period_lift_family {L W : ℕ} (hL : 0 < L)
    (r : ℕ) (hr : 0 < r) (hle : r ≤ L) (T : ℕ) (hcap : L * T ≤ W) :
    ∃ R : Finset ℕ, R.card = T ∧
      ∀ s ∈ R, 0 < s ∧ s ≤ W ∧ ∃ j < T, s = r + L * j := by
  let seat := fun j => r + L * j
  have hinj : Set.InjOn seat (Finset.range T) := by
    intro i _ j _ hij
    dsimp [seat] at hij
    nlinarith
  refine ⟨(Finset.range T).image seat, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  · intro s hs
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    have hjlt := Finset.mem_range.mp hj
    have hjle : j + 1 ≤ T := by omega
    have hmul := Nat.mul_le_mul_left L hjle
    refine ⟨by dsimp [seat]; omega, ?_, j, hjlt, rfl⟩
    dsimp [seat]
    nlinarith

end DkMath.NumberTheory

namespace DkMath.NumberTheory.Legendre

open scoped BigOperators

/-- The point selector1 modulo2p supplies candidate coprimality for every2^a*p^k anchor. -/
theorem candidate_of_two_prime_power_point_modEq_one {n p a k r : ℕ}
    (hform : n = 2 ^ a * p ^ k) (hr : 0 < r) (hle : r ≤ 2 * n)
    (hmod : Nat.ModEq (2 * p) (n ^ 2 + r) 1) :
    r ∈ squareAnchorOddPointCoprimeOffsets n := by
  have hc : Nat.Coprime (2 * p) (n ^ 2 + r) :=
    (Nat.coprime_of_mul_modEq_one 1 (by simpa only [Nat.mul_one] using hmod)).symm
  have htwo := hc.of_dvd_left (dvd_mul_right 2 p)
  have hp := hc.of_dvd_left (dvd_mul_left p 2)
  have hn : Nat.Coprime n (n ^ 2 + r) := by
    nth_rw 1 [hform]
    rw [Nat.coprime_mul_iff_left]
    exact ⟨htwo.pow_left a, hp.pow_left k⟩
  apply mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue.mpr
  exact ⟨⟨hr, hle⟩, Nat.coprime_mul_iff_left.mpr ⟨htwo, hn⟩⟩

/-- Active labels exclude every factor of a positive prime-power anchor component. -/
theorem active_product_coprime_two_prime {n p a k : ℕ}
    (hform : n = 2 ^ a * p ^ k) (hk : 0 < k)
    (Q : Finset ℕ) (hQ : Q ⊆ squareAnchorOddActivePrimes n) :
    Nat.Coprime (∏ q ∈ Q, q) (2 * p) := by
  have hpn : p ∣ n := by
    rw [hform]
    exact dvd_mul_of_dvd_right (dvd_pow_self p (by omega : k ≠ 0)) _
  apply Nat.Coprime.prod_left
  intro q hq
  have hp := activePrime_reducedResidue_packet (hQ hq)
  apply Nat.coprime_mul_iff_right.mpr
  exact ⟨Nat.coprime_two_right.mpr (hp.1.odd_of_ne_two hp.2.2.2.1),
    (hp.1.coprime_iff_not_dvd.mpr hp.2.2.1).of_dvd_right hpn⟩

/-- Mixed-anchor one-seat provider; p*product(Q)≤n fits the combined parity/coprimality period. -/
theorem exists_candidate_support_of_mixed_product_le {n p a k : ℕ}
    (hp : p.Prime) (hform : n = 2 ^ a * p ^ k) (hk : 0 < k)
    (Q : Finset ℕ) (hQ : Q ⊆ squareAnchorOddActivePrimes n)
    (hshort : p * (∏ q ∈ Q, q) ≤ n) :
    ∃ r ∈ squareAnchorOddPointCoprimeOffsets n, Q ⊆ paritySafeActiveSupport n r := by
  have hm : 0 < ∏ q ∈ Q, q := Finset.prod_pos fun q hq =>
    (mem_squareAnchorOddActivePrimes.mp (hQ hq)).1.pos
  obtain ⟨r, hr, hle, hdvd, hmod⟩ := DkMath.NumberTheory.exists_support_one_offset_le_period
    hm (Nat.mul_pos (by decide : 0 < 2) hp.pos)
    (active_product_coprime_two_prime hform hk Q hQ) (n ^ 2)
  exact ⟨r, candidate_of_two_prime_power_point_modEq_one hform hr (by nlinarith) hmod,
    activeSupport_contains_of_product_dvd Q hQ hdvd⟩

/-- Counted mixed-anchor family; congruence1 modulo2p persists through every period lift. -/
theorem mixed_anchor_period_family_charge_le_supportExcess {n p a k : ℕ}
    (hp : p.Prime) (hform : n = 2 ^ a * p ^ k) (hk : 0 < k)
    (Q : Finset ℕ) (hQ : Q ⊆ squareAnchorOddActivePrimes n) :
    (n / (p * (∏ q ∈ Q, q))) * (Q.card - 1) ≤ paritySafeSupportExcess n := by
  let m := ∏ q ∈ Q, q
  have hm : 0 < m := Finset.prod_pos fun q hq =>
    (mem_squareAnchorOddActivePrimes.mp (hQ hq)).1.pos
  obtain ⟨r, hr, hle, hdvd, hmod⟩ := DkMath.NumberTheory.exists_support_one_offset_le_period
    hm (Nat.mul_pos (by decide : 0 < 2) hp.pos)
    (active_product_coprime_two_prime hform hk Q hQ) (n ^ 2)
  let T := n / (p * m)
  have hcap : (2 * p * m) * T ≤ 2 * n := by
    have h : (p * m) * T ≤ n := by
      have hd := Nat.mod_add_div n (p * m)
      dsimp [T]
      omega
    calc
      (2 * p * m) * T = 2 * ((p * m) * T) := by ring
      _ ≤ 2 * n := Nat.mul_le_mul_left 2 h
  obtain ⟨R, hcard, hlifts⟩ := DkMath.NumberTheory.exists_positive_period_lift_family
    (by nlinarith : 0 < 2 * p * m) r hr hle T hcap
  have hR : R ⊆ squareAnchorOddPointCoprimeOffsets n := by
    intro s hs
    obtain ⟨hspos, hsle, j, _, heq⟩ := hlifts s hs
    have hz : Nat.ModEq (2 * p) ((2 * p * m) * j) 0 :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left (dvd_mul_right (2 * p) m) j)
    have hmodS : Nat.ModEq (2 * p) (n ^ 2 + s) 1 := by
      simpa only [heq, Nat.add_assoc, Nat.add_zero] using hmod.add hz
    exact candidate_of_two_prime_power_point_modEq_one hform hspos hsle hmodS
  have hP : ∀ s ∈ R, Q ⊆ paritySafeActiveSupport n s := by
    intro s hs
    obtain ⟨_, _, j, _, heq⟩ := hlifts s hs
    apply activeSupport_contains_of_product_dvd Q hQ
    rw [heq, ← Nat.add_assoc]
    exact dvd_add hdvd (dvd_mul_of_dvd_left (dvd_mul_left m (2 * p)) j)
  have h := sum_witness_support_excess_le_supportExcess R (fun _ => Q) hR hP
  simpa [hcard, T, m] using h

/-- The009 prime-anchor family also exposes its actual finite seats and exact cardinality. -/
theorem exists_prime_anchor_period_support_family {n : ℕ} (hn : n.Prime)
    (Q : Finset ℕ) (hQ : Q ⊆ squareAnchorOddActivePrimes n) :
    ∃ R : Finset ℕ, R ⊆ squareAnchorOddPointCoprimeOffsets n ∧
      (∀ r ∈ R, Q ⊆ paritySafeActiveSupport n r) ∧ R.card = (n - 1) / (∏ q ∈ Q, q) := by
  let m := ∏ q ∈ Q, q
  have hm : 0 < m := Finset.prod_pos fun q hq =>
    (mem_squareAnchorOddActivePrimes.mp (hQ hq)).1.pos
  have hcop : Nat.Coprime m 2 := Nat.Coprime.prod_left fun q hq =>
    Nat.coprime_two_right.mpr ((mem_squareAnchorOddActivePrimes.mp (hQ hq)).1.odd_of_ne_two
      (mem_squareAnchorOddActivePrimes.mp (hQ hq)).2.2.2)
  obtain ⟨r, hr, hle, hdvd, hodd⟩ :=
    DkMath.NumberTheory.exists_parity_offset_le_two_mul_period hm hcop (n ^ 2)
  let T := (n - 1) / m
  have hcap : (2 * m) * T ≤ 2 * (n - 1) := by
    have h : m * T ≤ n - 1 := by
      have hd := Nat.mod_add_div (n - 1) m
      dsimp [T]
      omega
    calc
      (2 * m) * T = 2 * (m * T) := by ring
      _ ≤ 2 * (n - 1) := Nat.mul_le_mul_left 2 h
  obtain ⟨R, hcard, hlifts⟩ := DkMath.NumberTheory.exists_positive_period_lift_family
    (by omega : 0 < 2 * m) r hr hle T hcap
  have hR : R ⊆ squareAnchorOddPointCoprimeOffsets n := by
    intro s hs
    obtain ⟨hspos, hsle, j, _, heq⟩ := hlifts s hs
    have hoddS : Odd (n ^ 2 + s) := by
      have heven : Even (2 * m * j) := ⟨m * j, by ring⟩
      simpa only [heq, ← Nat.add_assoc] using hodd.add_even heven
    have hstrict : s < 2 * n := by
      have hminus := Nat.sub_lt hn.pos (by decide : 0 < 1)
      omega
    exact candidate_of_window_coprime_odd hspos (Nat.le_of_lt hstrict)
      (coprime_prime_anchor_of_strict_window_odd hn hspos hstrict hoddS) hoddS
  refine ⟨R, hR, ?_, hcard⟩
  intro s hs
  obtain ⟨_, _, j, _, heq⟩ := hlifts s hs
  apply activeSupport_contains_of_product_dvd Q hQ
  rw [heq, ← Nat.add_assoc]
  exact dvd_add hdvd (dvd_mul_of_dvd_left (dvd_mul_left m 2) j)

/-- Two star-pair families share only prime3, so their counted charges add despite seat collisions. -/
theorem prime_star_pair_charge_le_supportExcess {n : ℕ} (hn : n.Prime) (hlarge : 7 < n) :
    (n - 1) / 15 + (n - 1) / 21 ≤ paritySafeSupportExcess n := by
  have hactive : ({3, 5, 7} : Finset ℕ) ⊆ squareAnchorOddActivePrimes n := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> apply mem_squareAnchorOddActivePrimes.mpr
    all_goals refine ⟨by decide, by omega, ?_, by decide⟩
    all_goals
      intro hdvd
      have hd := (Nat.dvd_prime hn).mp hdvd
      omega
  have hP : ({3, 5} : Finset ℕ) ⊆ squareAnchorOddActivePrimes n :=
    Finset.Subset.trans (by decide) hactive
  have hQ : ({3, 7} : Finset ℕ) ⊆ squareAnchorOddActivePrimes n :=
    Finset.Subset.trans (by decide) hactive
  obtain ⟨R, hR, hPR, hcardR⟩ := exists_prime_anchor_period_support_family hn {3, 5} hP
  obtain ⟨S, hS, hQS, hcardS⟩ := exists_prime_anchor_period_support_family hn {3, 7} hQ
  have h := two_family_charge_le_supportExcess R S {3, 5} {3, 7} hR hS hPR hQS (by decide)
  simpa [hcardR, hcardS] using h

/-- Exact linear inequality from two merged families; no analytic prime estimate is used. -/
theorem prime_star_pair_linear_charge {n : ℕ} (hn : n.Prime) (hlarge : 7 < n) :
    12 * (n - 1) ≤ 105 * paritySafeSupportExcess n + 198 := by
  have h := prime_star_pair_charge_le_supportExcess hn hlarge
  have h15 := Nat.mod_add_div (n - 1) 15
  have h21 := Nat.mod_add_div (n - 1) 21
  have hm15 := Nat.mod_lt (n - 1) (by decide : 0 < 15)
  have hm21 := Nat.mod_lt (n - 1) (by decide : 0 < 21)
  omega

end DkMath.NumberTheory.Legendre
